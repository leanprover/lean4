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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object* v_msg_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_32928__overap_1009_; lean_object* v___x_1010_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_32928__overap_1009_ = lean_panic_fn_borrowed(v___f_1008_, v_msg_1002_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1010_ = lean_apply_5(v___x_32928__overap_1009_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, lean_box(0));
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object* v_msg_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_msg_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t v_sz_1018_, size_t v_i_1019_, lean_object* v_bs_1020_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_lt(v_i_1019_, v_sz_1018_);
if (v___x_1021_ == 0)
{
return v_bs_1020_;
}
else
{
lean_object* v_v_1022_; lean_object* v___x_1023_; lean_object* v_bs_x27_1024_; lean_object* v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v_v_1022_ = lean_array_uget(v_bs_1020_, v_i_1019_);
v___x_1023_ = lean_unsigned_to_nat(0u);
v_bs_x27_1024_ = lean_array_uset(v_bs_1020_, v_i_1019_, v___x_1023_);
v___x_1025_ = lean_array_get_size(v_v_1022_);
lean_dec(v_v_1022_);
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1019_, v___x_1026_);
v___x_1028_ = lean_array_uset(v_bs_x27_1024_, v_i_1019_, v___x_1025_);
v_i_1019_ = v___x_1027_;
v_bs_1020_ = v___x_1028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object* v_sz_1030_, lean_object* v_i_1031_, lean_object* v_bs_1032_){
_start:
{
size_t v_sz_boxed_1033_; size_t v_i_boxed_1034_; lean_object* v_res_1035_; 
v_sz_boxed_1033_ = lean_unbox_usize(v_sz_1030_);
lean_dec(v_sz_1030_);
v_i_boxed_1034_ = lean_unbox_usize(v_i_1031_);
lean_dec(v_i_1031_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_boxed_1033_, v_i_boxed_1034_, v_bs_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t v_sz_1036_, size_t v_i_1037_, lean_object* v_bs_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
uint8_t v___x_1044_; 
v___x_1044_ = lean_usize_dec_lt(v_i_1037_, v_sz_1036_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v_bs_1038_);
return v___x_1045_;
}
else
{
lean_object* v_v_1046_; lean_object* v_value_1047_; lean_object* v___x_1048_; 
v_v_1046_ = lean_array_uget_borrowed(v_bs_1038_, v_i_1037_);
v_value_1047_ = lean_ctor_get(v_v_1046_, 7);
lean_inc_ref(v_value_1047_);
v___x_1048_ = l_Lean_Elab_getParamRevDeps(v_value_1047_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; lean_object* v_bs_x27_1051_; size_t v___x_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = lean_unsigned_to_nat(0u);
v_bs_x27_1051_ = lean_array_uset(v_bs_1038_, v_i_1037_, v___x_1050_);
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_add(v_i_1037_, v___x_1052_);
v___x_1054_ = lean_array_uset(v_bs_x27_1051_, v_i_1037_, v_a_1049_);
v_i_1037_ = v___x_1053_;
v_bs_1038_ = v___x_1054_;
goto _start;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v_bs_1038_);
v_a_1056_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1048_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1048_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object* v_sz_1064_, lean_object* v_i_1065_, lean_object* v_bs_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
size_t v_sz_boxed_1072_; size_t v_i_boxed_1073_; lean_object* v_res_1074_; 
v_sz_boxed_1072_ = lean_unbox_usize(v_sz_1064_);
lean_dec(v_sz_1064_);
v_i_boxed_1073_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_boxed_1072_, v_i_boxed_1073_, v_bs_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(lean_object* v_msgData_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v_env_1082_; lean_object* v___x_1083_; lean_object* v_mctx_1084_; lean_object* v_lctx_1085_; lean_object* v_options_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1081_ = lean_st_ref_get(v___y_1079_);
v_env_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_env_1082_);
lean_dec(v___x_1081_);
v___x_1083_ = lean_st_ref_get(v___y_1077_);
v_mctx_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_mctx_1084_);
lean_dec(v___x_1083_);
v_lctx_1085_ = lean_ctor_get(v___y_1076_, 2);
v_options_1086_ = lean_ctor_get(v___y_1078_, 2);
lean_inc_ref(v_options_1086_);
lean_inc_ref(v_lctx_1085_);
v___x_1087_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1087_, 0, v_env_1082_);
lean_ctor_set(v___x_1087_, 1, v_mctx_1084_);
lean_ctor_set(v___x_1087_, 2, v_lctx_1085_);
lean_ctor_set(v___x_1087_, 3, v_options_1086_);
v___x_1088_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_msgData_1075_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2___boxed(lean_object* v_msgData_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msgData_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1096_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1097_; double v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_float_of_nat(v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object* v_cls_1102_, lean_object* v_msg_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_ref_1109_; lean_object* v___x_1110_; lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1155_; 
v_ref_1109_ = lean_ctor_get(v___y_1106_, 5);
v___x_1110_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1155_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1155_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v_traceState_1116_; lean_object* v_env_1117_; lean_object* v_nextMacroScope_1118_; lean_object* v_ngen_1119_; lean_object* v_auxDeclNGen_1120_; lean_object* v_cache_1121_; lean_object* v_messages_1122_; lean_object* v_infoState_1123_; lean_object* v_snapshotTasks_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1154_; 
v___x_1115_ = lean_st_ref_take(v___y_1107_);
v_traceState_1116_ = lean_ctor_get(v___x_1115_, 4);
v_env_1117_ = lean_ctor_get(v___x_1115_, 0);
v_nextMacroScope_1118_ = lean_ctor_get(v___x_1115_, 1);
v_ngen_1119_ = lean_ctor_get(v___x_1115_, 2);
v_auxDeclNGen_1120_ = lean_ctor_get(v___x_1115_, 3);
v_cache_1121_ = lean_ctor_get(v___x_1115_, 5);
v_messages_1122_ = lean_ctor_get(v___x_1115_, 6);
v_infoState_1123_ = lean_ctor_get(v___x_1115_, 7);
v_snapshotTasks_1124_ = lean_ctor_get(v___x_1115_, 8);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1126_ = v___x_1115_;
v_isShared_1127_ = v_isSharedCheck_1154_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_snapshotTasks_1124_);
lean_inc(v_infoState_1123_);
lean_inc(v_messages_1122_);
lean_inc(v_cache_1121_);
lean_inc(v_traceState_1116_);
lean_inc(v_auxDeclNGen_1120_);
lean_inc(v_ngen_1119_);
lean_inc(v_nextMacroScope_1118_);
lean_inc(v_env_1117_);
lean_dec(v___x_1115_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1154_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
uint64_t v_tid_1128_; lean_object* v_traces_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1153_; 
v_tid_1128_ = lean_ctor_get_uint64(v_traceState_1116_, sizeof(void*)*1);
v_traces_1129_ = lean_ctor_get(v_traceState_1116_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_traceState_1116_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1131_ = v_traceState_1116_;
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_traces_1129_);
lean_dec(v_traceState_1116_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; double v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_1135_ = 0;
v___x_1136_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_1137_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1137_, 0, v_cls_1102_);
lean_ctor_set(v___x_1137_, 1, v___x_1133_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
lean_ctor_set_float(v___x_1137_, sizeof(void*)*3, v___x_1134_);
lean_ctor_set_float(v___x_1137_, sizeof(void*)*3 + 8, v___x_1134_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*3 + 16, v___x_1135_);
v___x_1138_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_1139_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v_a_1111_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
lean_inc(v_ref_1109_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_ref_1109_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_PersistentArray_push___redArg(v_traces_1129_, v___x_1140_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1141_);
v___x_1143_ = v___x_1131_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1141_);
lean_ctor_set_uint64(v_reuseFailAlloc_1152_, sizeof(void*)*1, v_tid_1128_);
v___x_1143_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v___x_1143_);
v___x_1145_ = v___x_1126_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_env_1117_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_nextMacroScope_1118_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_ngen_1119_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_auxDeclNGen_1120_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v_cache_1121_);
lean_ctor_set(v_reuseFailAlloc_1151_, 6, v_messages_1122_);
lean_ctor_set(v_reuseFailAlloc_1151_, 7, v_infoState_1123_);
lean_ctor_set(v_reuseFailAlloc_1151_, 8, v_snapshotTasks_1124_);
v___x_1145_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1146_ = lean_st_ref_set(v___y_1107_, v___x_1145_);
v___x_1147_ = lean_box(0);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1147_);
v___x_1149_ = v___x_1113_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_1156_, lean_object* v_msg_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_1156_, v_msg_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object* v_00_u03b1_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_apply_1(v_x_1165_, lean_box(0));
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object* v_00_u03b1_1173_, lean_object* v_x_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(v_00_u03b1_1173_, v_x_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object* v_x_1181_, lean_object* v_x_1182_){
_start:
{
if (lean_obj_tag(v_x_1182_) == 0)
{
return v_x_1181_;
}
else
{
lean_object* v_key_1183_; lean_object* v_value_1184_; lean_object* v_tail_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1208_; 
v_key_1183_ = lean_ctor_get(v_x_1182_, 0);
v_value_1184_ = lean_ctor_get(v_x_1182_, 1);
v_tail_1185_ = lean_ctor_get(v_x_1182_, 2);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_x_1182_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1187_ = v_x_1182_;
v_isShared_1188_ = v_isSharedCheck_1208_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_tail_1185_);
lean_inc(v_value_1184_);
lean_inc(v_key_1183_);
lean_dec(v_x_1182_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1208_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; uint64_t v___x_1190_; uint64_t v___x_1191_; uint64_t v___x_1192_; uint64_t v_fold_1193_; uint64_t v___x_1194_; uint64_t v___x_1195_; uint64_t v___x_1196_; size_t v___x_1197_; size_t v___x_1198_; size_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1189_ = lean_array_get_size(v_x_1181_);
v___x_1190_ = l_Lean_ExprStructEq_hash(v_key_1183_);
v___x_1191_ = 32ULL;
v___x_1192_ = lean_uint64_shift_right(v___x_1190_, v___x_1191_);
v_fold_1193_ = lean_uint64_xor(v___x_1190_, v___x_1192_);
v___x_1194_ = 16ULL;
v___x_1195_ = lean_uint64_shift_right(v_fold_1193_, v___x_1194_);
v___x_1196_ = lean_uint64_xor(v_fold_1193_, v___x_1195_);
v___x_1197_ = lean_uint64_to_usize(v___x_1196_);
v___x_1198_ = lean_usize_of_nat(v___x_1189_);
v___x_1199_ = ((size_t)1ULL);
v___x_1200_ = lean_usize_sub(v___x_1198_, v___x_1199_);
v___x_1201_ = lean_usize_land(v___x_1197_, v___x_1200_);
v___x_1202_ = lean_array_uget_borrowed(v_x_1181_, v___x_1201_);
lean_inc(v___x_1202_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 2, v___x_1202_);
v___x_1204_ = v___x_1187_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_key_1183_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_value_1184_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_array_uset(v_x_1181_, v___x_1201_, v___x_1204_);
v_x_1181_ = v___x_1205_;
v_x_1182_ = v_tail_1185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object* v_i_1209_, lean_object* v_source_1210_, lean_object* v_target_1211_){
_start:
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_array_get_size(v_source_1210_);
v___x_1213_ = lean_nat_dec_lt(v_i_1209_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_dec_ref(v_source_1210_);
lean_dec(v_i_1209_);
return v_target_1211_;
}
else
{
lean_object* v_es_1214_; lean_object* v___x_1215_; lean_object* v_source_1216_; lean_object* v_target_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_es_1214_ = lean_array_fget(v_source_1210_, v_i_1209_);
v___x_1215_ = lean_box(0);
v_source_1216_ = lean_array_fset(v_source_1210_, v_i_1209_, v___x_1215_);
v_target_1217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_target_1211_, v_es_1214_);
v___x_1218_ = lean_unsigned_to_nat(1u);
v___x_1219_ = lean_nat_add(v_i_1209_, v___x_1218_);
lean_dec(v_i_1209_);
v_i_1209_ = v___x_1219_;
v_source_1210_ = v_source_1216_;
v_target_1211_ = v_target_1217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object* v_data_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_nbuckets_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1222_ = lean_array_get_size(v_data_1221_);
v___x_1223_ = lean_unsigned_to_nat(2u);
v_nbuckets_1224_ = lean_nat_mul(v___x_1222_, v___x_1223_);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_mk_array(v_nbuckets_1224_, v___x_1226_);
v___x_1228_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1225_, v_data_1221_, v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object* v_a_1229_, lean_object* v_b_1230_, lean_object* v_x_1231_){
_start:
{
if (lean_obj_tag(v_x_1231_) == 0)
{
lean_dec(v_b_1230_);
lean_dec_ref(v_a_1229_);
return v_x_1231_;
}
else
{
lean_object* v_key_1232_; lean_object* v_value_1233_; lean_object* v_tail_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1246_; 
v_key_1232_ = lean_ctor_get(v_x_1231_, 0);
v_value_1233_ = lean_ctor_get(v_x_1231_, 1);
v_tail_1234_ = lean_ctor_get(v_x_1231_, 2);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1231_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1236_ = v_x_1231_;
v_isShared_1237_ = v_isSharedCheck_1246_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_tail_1234_);
lean_inc(v_value_1233_);
lean_inc(v_key_1232_);
lean_dec(v_x_1231_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1246_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
uint8_t v___x_1238_; 
v___x_1238_ = l_Lean_ExprStructEq_beq(v_key_1232_, v_a_1229_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1229_, v_b_1230_, v_tail_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 2, v___x_1239_);
v___x_1241_ = v___x_1236_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_key_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_value_1233_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
else
{
lean_object* v___x_1244_; 
lean_dec(v_value_1233_);
lean_dec(v_key_1232_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v_b_1230_);
lean_ctor_set(v___x_1236_, 0, v_a_1229_);
v___x_1244_ = v___x_1236_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1229_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_b_1230_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_tail_1234_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_a_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 0)
{
uint8_t v___x_1249_; 
v___x_1249_ = 0;
return v___x_1249_;
}
else
{
lean_object* v_key_1250_; lean_object* v_tail_1251_; uint8_t v___x_1252_; 
v_key_1250_ = lean_ctor_get(v_x_1248_, 0);
v_tail_1251_ = lean_ctor_get(v_x_1248_, 2);
v___x_1252_ = l_Lean_ExprStructEq_beq(v_key_1250_, v_a_1247_);
if (v___x_1252_ == 0)
{
v_x_1248_ = v_tail_1251_;
goto _start;
}
else
{
return v___x_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_a_1254_, lean_object* v_x_1255_){
_start:
{
uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_res_1256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1254_, v_x_1255_);
lean_dec(v_x_1255_);
lean_dec_ref(v_a_1254_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1258_, lean_object* v_a_1259_, lean_object* v_b_1260_){
_start:
{
lean_object* v_size_1261_; lean_object* v_buckets_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1305_; 
v_size_1261_ = lean_ctor_get(v_m_1258_, 0);
v_buckets_1262_ = lean_ctor_get(v_m_1258_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_m_1258_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1264_ = v_m_1258_;
v_isShared_1265_ = v_isSharedCheck_1305_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_buckets_1262_);
lean_inc(v_size_1261_);
lean_dec(v_m_1258_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1305_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; uint64_t v___x_1267_; uint64_t v___x_1268_; uint64_t v___x_1269_; uint64_t v_fold_1270_; uint64_t v___x_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; size_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; lean_object* v_bkt_1279_; uint8_t v___x_1280_; 
v___x_1266_ = lean_array_get_size(v_buckets_1262_);
v___x_1267_ = l_Lean_ExprStructEq_hash(v_a_1259_);
v___x_1268_ = 32ULL;
v___x_1269_ = lean_uint64_shift_right(v___x_1267_, v___x_1268_);
v_fold_1270_ = lean_uint64_xor(v___x_1267_, v___x_1269_);
v___x_1271_ = 16ULL;
v___x_1272_ = lean_uint64_shift_right(v_fold_1270_, v___x_1271_);
v___x_1273_ = lean_uint64_xor(v_fold_1270_, v___x_1272_);
v___x_1274_ = lean_uint64_to_usize(v___x_1273_);
v___x_1275_ = lean_usize_of_nat(v___x_1266_);
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_sub(v___x_1275_, v___x_1276_);
v___x_1278_ = lean_usize_land(v___x_1274_, v___x_1277_);
v_bkt_1279_ = lean_array_uget_borrowed(v_buckets_1262_, v___x_1278_);
v___x_1280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1259_, v_bkt_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v_size_x27_1282_; lean_object* v___x_1283_; lean_object* v_buckets_x27_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1281_ = lean_unsigned_to_nat(1u);
v_size_x27_1282_ = lean_nat_add(v_size_1261_, v___x_1281_);
lean_dec(v_size_1261_);
lean_inc(v_bkt_1279_);
v___x_1283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1283_, 0, v_a_1259_);
lean_ctor_set(v___x_1283_, 1, v_b_1260_);
lean_ctor_set(v___x_1283_, 2, v_bkt_1279_);
v_buckets_x27_1284_ = lean_array_uset(v_buckets_1262_, v___x_1278_, v___x_1283_);
v___x_1285_ = lean_unsigned_to_nat(4u);
v___x_1286_ = lean_nat_mul(v_size_x27_1282_, v___x_1285_);
v___x_1287_ = lean_unsigned_to_nat(3u);
v___x_1288_ = lean_nat_div(v___x_1286_, v___x_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_array_get_size(v_buckets_x27_1284_);
v___x_1290_ = lean_nat_dec_le(v___x_1288_, v___x_1289_);
lean_dec(v___x_1288_);
if (v___x_1290_ == 0)
{
lean_object* v_val_1291_; lean_object* v___x_1293_; 
v_val_1291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_buckets_x27_1284_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v_val_1291_);
lean_ctor_set(v___x_1264_, 0, v_size_x27_1282_);
v___x_1293_ = v___x_1264_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_size_x27_1282_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_val_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
lean_object* v___x_1296_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v_buckets_x27_1284_);
lean_ctor_set(v___x_1264_, 0, v_size_x27_1282_);
v___x_1296_ = v___x_1264_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_size_x27_1282_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_buckets_x27_1284_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v___x_1298_; lean_object* v_buckets_x27_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_inc(v_bkt_1279_);
v___x_1298_ = lean_box(0);
v_buckets_x27_1299_ = lean_array_uset(v_buckets_1262_, v___x_1278_, v___x_1298_);
v___x_1300_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1259_, v_b_1260_, v_bkt_1279_);
v___x_1301_ = lean_array_uset(v_buckets_x27_1299_, v___x_1278_, v___x_1300_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v___x_1301_);
v___x_1303_ = v___x_1264_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_size_1261_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1306_, lean_object* v_e_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_st_ref_take(v_a_1306_);
v___x_1311_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1310_, v_e_1307_, v_a_1308_);
v___x_1312_ = lean_st_ref_set(v_a_1306_, v___x_1311_);
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1314_, lean_object* v_e_1315_, lean_object* v_a_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1314_, v_e_1315_, v_a_1316_);
lean_dec(v_a_1314_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1319_, lean_object* v___y_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1320_);
v___x_1327_ = lean_apply_7(v_k_1319_, v_b_1321_, v___y_1320_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, lean_box(0));
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1328_, lean_object* v___y_1329_, lean_object* v_b_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1328_, v___y_1329_, v_b_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1329_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1337_, uint8_t v_bi_1338_, lean_object* v_type_1339_, lean_object* v_k_1340_, uint8_t v_kind_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___f_1348_; lean_object* v___x_1349_; 
lean_inc(v___y_1342_);
v___f_1348_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1348_, 0, v_k_1340_);
lean_closure_set(v___f_1348_, 1, v___y_1342_);
v___x_1349_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1337_, v_bi_1338_, v_type_1339_, v___f_1348_, v_kind_1341_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1349_) == 0)
{
return v___x_1349_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1358_, lean_object* v_bi_1359_, lean_object* v_type_1360_, lean_object* v_k_1361_, lean_object* v_kind_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
uint8_t v_bi_boxed_1369_; uint8_t v_kind_boxed_1370_; lean_object* v_res_1371_; 
v_bi_boxed_1369_ = lean_unbox(v_bi_1359_);
v_kind_boxed_1370_ = lean_unbox(v_kind_1362_);
v_res_1371_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1358_, v_bi_boxed_1369_, v_type_1360_, v_k_1361_, v_kind_boxed_1370_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object* v___x_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1372_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object* v___x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1386_, lean_object* v_type_1387_, lean_object* v_val_1388_, lean_object* v_k_1389_, uint8_t v_nondep_1390_, uint8_t v_kind_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___f_1398_; lean_object* v___x_1399_; 
lean_inc(v___y_1392_);
v___f_1398_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1398_, 0, v_k_1389_);
lean_closure_set(v___f_1398_, 1, v___y_1392_);
v___x_1399_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1386_, v_type_1387_, v_val_1388_, v___f_1398_, v_nondep_1390_, v_kind_1391_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1399_) == 0)
{
return v___x_1399_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1408_, lean_object* v_type_1409_, lean_object* v_val_1410_, lean_object* v_k_1411_, lean_object* v_nondep_1412_, lean_object* v_kind_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v_nondep_boxed_1420_; uint8_t v_kind_boxed_1421_; lean_object* v_res_1422_; 
v_nondep_boxed_1420_ = lean_unbox(v_nondep_1412_);
v_kind_boxed_1421_ = lean_unbox(v_kind_1413_);
v_res_1422_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1408_, v_type_1409_, v_val_1410_, v_k_1411_, v_nondep_boxed_1420_, v_kind_boxed_1421_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1423_, lean_object* v_x_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_apply_1(v_x_1424_, lean_box(0));
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1432_, lean_object* v_x_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1432_, v_x_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1439_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = l_Lean_maxRecDepthErrorMessage;
v___x_1446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1448_ = l_Lean_MessageData_ofFormat(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1450_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1451_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v___x_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1452_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v_ref_1452_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___y_1468_; lean_object* v_fileName_1477_; lean_object* v_fileMap_1478_; lean_object* v_options_1479_; lean_object* v_currRecDepth_1480_; lean_object* v_maxRecDepth_1481_; lean_object* v_ref_1482_; lean_object* v_currNamespace_1483_; lean_object* v_openDecls_1484_; lean_object* v_initHeartbeats_1485_; lean_object* v_maxHeartbeats_1486_; lean_object* v_quotContext_1487_; lean_object* v_currMacroScope_1488_; uint8_t v_diag_1489_; lean_object* v_cancelTk_x3f_1490_; uint8_t v_suppressElabErrors_1491_; lean_object* v_inheritedTraceOptions_1492_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_fileName_1477_ = lean_ctor_get(v___y_1464_, 0);
v_fileMap_1478_ = lean_ctor_get(v___y_1464_, 1);
v_options_1479_ = lean_ctor_get(v___y_1464_, 2);
v_currRecDepth_1480_ = lean_ctor_get(v___y_1464_, 3);
v_maxRecDepth_1481_ = lean_ctor_get(v___y_1464_, 4);
v_ref_1482_ = lean_ctor_get(v___y_1464_, 5);
v_currNamespace_1483_ = lean_ctor_get(v___y_1464_, 6);
v_openDecls_1484_ = lean_ctor_get(v___y_1464_, 7);
v_initHeartbeats_1485_ = lean_ctor_get(v___y_1464_, 8);
v_maxHeartbeats_1486_ = lean_ctor_get(v___y_1464_, 9);
v_quotContext_1487_ = lean_ctor_get(v___y_1464_, 10);
v_currMacroScope_1488_ = lean_ctor_get(v___y_1464_, 11);
v_diag_1489_ = lean_ctor_get_uint8(v___y_1464_, sizeof(void*)*14);
v_cancelTk_x3f_1490_ = lean_ctor_get(v___y_1464_, 12);
v_suppressElabErrors_1491_ = lean_ctor_get_uint8(v___y_1464_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1492_ = lean_ctor_get(v___y_1464_, 13);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = lean_nat_dec_eq(v_maxRecDepth_1481_, v___x_1498_);
if (v___x_1499_ == 0)
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_nat_dec_eq(v_currRecDepth_1480_, v_maxRecDepth_1481_);
if (v___x_1500_ == 0)
{
goto v___jp_1493_;
}
else
{
lean_object* v___x_1501_; 
lean_dec_ref(v_x_1460_);
lean_inc(v_ref_1482_);
v___x_1501_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1482_);
v___y_1468_ = v___x_1501_;
goto v___jp_1467_;
}
}
else
{
goto v___jp_1493_;
}
v___jp_1467_:
{
if (lean_obj_tag(v___y_1468_) == 0)
{
return v___y_1468_;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_a_1469_ = lean_ctor_get(v___y_1468_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___y_1468_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___y_1468_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___y_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
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
v___jp_1493_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1494_ = lean_unsigned_to_nat(1u);
v___x_1495_ = lean_nat_add(v_currRecDepth_1480_, v___x_1494_);
lean_inc_ref(v_inheritedTraceOptions_1492_);
lean_inc(v_cancelTk_x3f_1490_);
lean_inc(v_currMacroScope_1488_);
lean_inc(v_quotContext_1487_);
lean_inc(v_maxHeartbeats_1486_);
lean_inc(v_initHeartbeats_1485_);
lean_inc(v_openDecls_1484_);
lean_inc(v_currNamespace_1483_);
lean_inc(v_ref_1482_);
lean_inc(v_maxRecDepth_1481_);
lean_inc_ref(v_options_1479_);
lean_inc_ref(v_fileMap_1478_);
lean_inc_ref(v_fileName_1477_);
v___x_1496_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1496_, 0, v_fileName_1477_);
lean_ctor_set(v___x_1496_, 1, v_fileMap_1478_);
lean_ctor_set(v___x_1496_, 2, v_options_1479_);
lean_ctor_set(v___x_1496_, 3, v___x_1495_);
lean_ctor_set(v___x_1496_, 4, v_maxRecDepth_1481_);
lean_ctor_set(v___x_1496_, 5, v_ref_1482_);
lean_ctor_set(v___x_1496_, 6, v_currNamespace_1483_);
lean_ctor_set(v___x_1496_, 7, v_openDecls_1484_);
lean_ctor_set(v___x_1496_, 8, v_initHeartbeats_1485_);
lean_ctor_set(v___x_1496_, 9, v_maxHeartbeats_1486_);
lean_ctor_set(v___x_1496_, 10, v_quotContext_1487_);
lean_ctor_set(v___x_1496_, 11, v_currMacroScope_1488_);
lean_ctor_set(v___x_1496_, 12, v_cancelTk_x3f_1490_);
lean_ctor_set(v___x_1496_, 13, v_inheritedTraceOptions_1492_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*14, v_diag_1489_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*14 + 1, v_suppressElabErrors_1491_);
lean_inc(v___y_1465_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
v___x_1497_ = lean_apply_6(v_x_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___x_1496_, v___y_1465_, lean_box(0));
v___y_1468_ = v___x_1497_;
goto v___jp_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1510_, lean_object* v_x_1511_){
_start:
{
if (lean_obj_tag(v_x_1511_) == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_box(0);
return v___x_1512_;
}
else
{
lean_object* v_key_1513_; lean_object* v_value_1514_; lean_object* v_tail_1515_; uint8_t v___x_1516_; 
v_key_1513_ = lean_ctor_get(v_x_1511_, 0);
v_value_1514_ = lean_ctor_get(v_x_1511_, 1);
v_tail_1515_ = lean_ctor_get(v_x_1511_, 2);
v___x_1516_ = l_Lean_ExprStructEq_beq(v_key_1513_, v_a_1510_);
if (v___x_1516_ == 0)
{
v_x_1511_ = v_tail_1515_;
goto _start;
}
else
{
lean_object* v___x_1518_; 
lean_inc(v_value_1514_);
v___x_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_value_1514_);
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1519_, lean_object* v_x_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1519_, v_x_1520_);
lean_dec(v_x_1520_);
lean_dec_ref(v_a_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_buckets_1524_; lean_object* v___x_1525_; uint64_t v___x_1526_; uint64_t v___x_1527_; uint64_t v___x_1528_; uint64_t v_fold_1529_; uint64_t v___x_1530_; uint64_t v___x_1531_; uint64_t v___x_1532_; size_t v___x_1533_; size_t v___x_1534_; size_t v___x_1535_; size_t v___x_1536_; size_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_buckets_1524_ = lean_ctor_get(v_m_1522_, 1);
v___x_1525_ = lean_array_get_size(v_buckets_1524_);
v___x_1526_ = l_Lean_ExprStructEq_hash(v_a_1523_);
v___x_1527_ = 32ULL;
v___x_1528_ = lean_uint64_shift_right(v___x_1526_, v___x_1527_);
v_fold_1529_ = lean_uint64_xor(v___x_1526_, v___x_1528_);
v___x_1530_ = 16ULL;
v___x_1531_ = lean_uint64_shift_right(v_fold_1529_, v___x_1530_);
v___x_1532_ = lean_uint64_xor(v_fold_1529_, v___x_1531_);
v___x_1533_ = lean_uint64_to_usize(v___x_1532_);
v___x_1534_ = lean_usize_of_nat(v___x_1525_);
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_sub(v___x_1534_, v___x_1535_);
v___x_1537_ = lean_usize_land(v___x_1533_, v___x_1536_);
v___x_1538_ = lean_array_uget_borrowed(v_buckets_1524_, v___x_1537_);
v___x_1539_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1523_, v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1540_, v_a_1541_);
lean_dec_ref(v_a_1541_);
lean_dec_ref(v_m_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1546_, lean_object* v_pre_1547_, lean_object* v_post_1548_, uint8_t v_usedLetOnly_1549_, uint8_t v_skipConstInApp_1550_, uint8_t v_skipInstances_1551_, lean_object* v_body_1552_, lean_object* v_x_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_array_push(v_fvars_1546_, v_x_1553_);
v___x_1561_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1547_, v_post_1548_, v_usedLetOnly_1549_, v_skipConstInApp_1550_, v_skipInstances_1551_, v___x_1560_, v_body_1552_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1562_, lean_object* v_pre_1563_, lean_object* v_post_1564_, lean_object* v_usedLetOnly_1565_, lean_object* v_skipConstInApp_1566_, lean_object* v_skipInstances_1567_, lean_object* v_body_1568_, lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
uint8_t v_usedLetOnly_boxed_1576_; uint8_t v_skipConstInApp_boxed_1577_; uint8_t v_skipInstances_boxed_1578_; lean_object* v_res_1579_; 
v_usedLetOnly_boxed_1576_ = lean_unbox(v_usedLetOnly_1565_);
v_skipConstInApp_boxed_1577_ = lean_unbox(v_skipConstInApp_1566_);
v_skipInstances_boxed_1578_ = lean_unbox(v_skipInstances_1567_);
v_res_1579_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1562_, v_pre_1563_, v_post_1564_, v_usedLetOnly_boxed_1576_, v_skipConstInApp_boxed_1577_, v_skipInstances_boxed_1578_, v_body_1568_, v_x_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1580_, lean_object* v_post_1581_, uint8_t v_usedLetOnly_1582_, uint8_t v_skipConstInApp_1583_, uint8_t v_skipInstances_1584_, lean_object* v_e_1585_, lean_object* v_a_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
lean_inc_ref(v_post_1581_);
lean_inc(v___y_1590_);
lean_inc_ref(v___y_1589_);
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc_ref(v_e_1585_);
v___x_1592_ = lean_apply_6(v_post_1581_, v_e_1585_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, lean_box(0));
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1611_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1611_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1611_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
switch(lean_obj_tag(v_a_1593_))
{
case 0:
{
lean_object* v_e_1597_; lean_object* v___x_1599_; 
lean_dec_ref(v_e_1585_);
lean_dec_ref(v_post_1581_);
lean_dec_ref(v_pre_1580_);
v_e_1597_ = lean_ctor_get(v_a_1593_, 0);
lean_inc_ref(v_e_1597_);
lean_dec_ref(v_a_1593_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_e_1597_);
v___x_1599_ = v___x_1595_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_e_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
case 1:
{
lean_object* v_e_1601_; lean_object* v___x_1602_; 
lean_del_object(v___x_1595_);
lean_dec_ref(v_e_1585_);
v_e_1601_ = lean_ctor_get(v_a_1593_, 0);
lean_inc_ref(v_e_1601_);
lean_dec_ref(v_a_1593_);
v___x_1602_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1580_, v_post_1581_, v_usedLetOnly_1582_, v_skipConstInApp_1583_, v_skipInstances_1584_, v_e_1601_, v_a_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1602_;
}
default: 
{
lean_object* v_e_x3f_1603_; 
lean_dec_ref(v_post_1581_);
lean_dec_ref(v_pre_1580_);
v_e_x3f_1603_ = lean_ctor_get(v_a_1593_, 0);
lean_inc(v_e_x3f_1603_);
lean_dec_ref(v_a_1593_);
if (lean_obj_tag(v_e_x3f_1603_) == 0)
{
lean_object* v___x_1605_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_e_1585_);
v___x_1605_ = v___x_1595_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_e_1585_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
else
{
lean_object* v_val_1607_; lean_object* v___x_1609_; 
lean_dec_ref(v_e_1585_);
v_val_1607_ = lean_ctor_get(v_e_x3f_1603_, 0);
lean_inc(v_val_1607_);
lean_dec_ref(v_e_x3f_1603_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_val_1607_);
v___x_1609_ = v___x_1595_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_val_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_e_1585_);
lean_dec_ref(v_post_1581_);
lean_dec_ref(v_pre_1580_);
v_a_1612_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1592_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1592_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1620_, lean_object* v_post_1621_, uint8_t v_usedLetOnly_1622_, uint8_t v_skipConstInApp_1623_, uint8_t v_skipInstances_1624_, lean_object* v_fvars_1625_, lean_object* v_e_1626_, lean_object* v_a_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
if (lean_obj_tag(v_e_1626_) == 6)
{
lean_object* v_binderName_1633_; lean_object* v_binderType_1634_; lean_object* v_body_1635_; uint8_t v_binderInfo_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_binderName_1633_ = lean_ctor_get(v_e_1626_, 0);
lean_inc(v_binderName_1633_);
v_binderType_1634_ = lean_ctor_get(v_e_1626_, 1);
lean_inc_ref(v_binderType_1634_);
v_body_1635_ = lean_ctor_get(v_e_1626_, 2);
lean_inc_ref(v_body_1635_);
v_binderInfo_1636_ = lean_ctor_get_uint8(v_e_1626_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1626_);
v___x_1637_ = lean_expr_instantiate_rev(v_binderType_1634_, v_fvars_1625_);
lean_dec_ref(v_binderType_1634_);
lean_inc_ref(v_post_1621_);
lean_inc_ref(v_pre_1620_);
v___x_1638_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1620_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___x_1637_, v_a_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___f_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref(v___x_1638_);
v___x_1640_ = lean_box(v_usedLetOnly_1622_);
v___x_1641_ = lean_box(v_skipConstInApp_1623_);
v___x_1642_ = lean_box(v_skipInstances_1624_);
v___f_1643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1643_, 0, v_fvars_1625_);
lean_closure_set(v___f_1643_, 1, v_pre_1620_);
lean_closure_set(v___f_1643_, 2, v_post_1621_);
lean_closure_set(v___f_1643_, 3, v___x_1640_);
lean_closure_set(v___f_1643_, 4, v___x_1641_);
lean_closure_set(v___f_1643_, 5, v___x_1642_);
lean_closure_set(v___f_1643_, 6, v_body_1635_);
v___x_1644_ = 0;
v___x_1645_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1633_, v_binderInfo_1636_, v_a_1639_, v___f_1643_, v___x_1644_, v_a_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1645_;
}
else
{
lean_dec_ref(v_body_1635_);
lean_dec(v_binderName_1633_);
lean_dec_ref(v_fvars_1625_);
lean_dec_ref(v_post_1621_);
lean_dec_ref(v_pre_1620_);
return v___x_1638_;
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_expr_instantiate_rev(v_e_1626_, v_fvars_1625_);
lean_dec_ref(v_e_1626_);
lean_inc_ref(v_post_1621_);
lean_inc_ref(v_pre_1620_);
v___x_1647_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1620_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v___x_1646_, v_a_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; uint8_t v___x_1649_; uint8_t v___x_1650_; uint8_t v___x_1651_; lean_object* v___x_1652_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref(v___x_1647_);
v___x_1649_ = 0;
v___x_1650_ = 1;
v___x_1651_ = 1;
v___x_1652_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1625_, v_a_1648_, v___x_1649_, v_usedLetOnly_1622_, v___x_1649_, v___x_1650_, v___x_1651_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec_ref(v_fvars_1625_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1654_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1620_, v_post_1621_, v_usedLetOnly_1622_, v_skipConstInApp_1623_, v_skipInstances_1624_, v_a_1653_, v_a_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
return v___x_1654_;
}
else
{
lean_dec_ref(v_post_1621_);
lean_dec_ref(v_pre_1620_);
return v___x_1652_;
}
}
else
{
lean_dec_ref(v_fvars_1625_);
lean_dec_ref(v_post_1621_);
lean_dec_ref(v_pre_1620_);
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1655_, lean_object* v_pre_1656_, lean_object* v_post_1657_, uint8_t v_usedLetOnly_1658_, uint8_t v_skipConstInApp_1659_, uint8_t v_skipInstances_1660_, lean_object* v_body_1661_, lean_object* v_x_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_array_push(v_fvars_1655_, v_x_1662_);
v___x_1670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1656_, v_post_1657_, v_usedLetOnly_1658_, v_skipConstInApp_1659_, v_skipInstances_1660_, v___x_1669_, v_body_1661_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1671_, lean_object* v_pre_1672_, lean_object* v_post_1673_, lean_object* v_usedLetOnly_1674_, lean_object* v_skipConstInApp_1675_, lean_object* v_skipInstances_1676_, lean_object* v_body_1677_, lean_object* v_x_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_usedLetOnly_boxed_1685_; uint8_t v_skipConstInApp_boxed_1686_; uint8_t v_skipInstances_boxed_1687_; lean_object* v_res_1688_; 
v_usedLetOnly_boxed_1685_ = lean_unbox(v_usedLetOnly_1674_);
v_skipConstInApp_boxed_1686_ = lean_unbox(v_skipConstInApp_1675_);
v_skipInstances_boxed_1687_ = lean_unbox(v_skipInstances_1676_);
v_res_1688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1671_, v_pre_1672_, v_post_1673_, v_usedLetOnly_boxed_1685_, v_skipConstInApp_boxed_1686_, v_skipInstances_boxed_1687_, v_body_1677_, v_x_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1689_, lean_object* v_post_1690_, uint8_t v_usedLetOnly_1691_, uint8_t v_skipConstInApp_1692_, uint8_t v_skipInstances_1693_, lean_object* v_fvars_1694_, lean_object* v_e_1695_, lean_object* v_a_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
if (lean_obj_tag(v_e_1695_) == 8)
{
lean_object* v_declName_1702_; lean_object* v_type_1703_; lean_object* v_value_1704_; lean_object* v_body_1705_; uint8_t v_nondep_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_declName_1702_ = lean_ctor_get(v_e_1695_, 0);
lean_inc(v_declName_1702_);
v_type_1703_ = lean_ctor_get(v_e_1695_, 1);
lean_inc_ref(v_type_1703_);
v_value_1704_ = lean_ctor_get(v_e_1695_, 2);
lean_inc_ref(v_value_1704_);
v_body_1705_ = lean_ctor_get(v_e_1695_, 3);
lean_inc_ref(v_body_1705_);
v_nondep_1706_ = lean_ctor_get_uint8(v_e_1695_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_1695_);
v___x_1707_ = lean_expr_instantiate_rev(v_type_1703_, v_fvars_1694_);
lean_dec_ref(v_type_1703_);
lean_inc_ref(v_post_1690_);
lean_inc_ref(v_pre_1689_);
v___x_1708_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1689_, v_post_1690_, v_usedLetOnly_1691_, v_skipConstInApp_1692_, v_skipInstances_1693_, v___x_1707_, v_a_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___x_1708_);
v___x_1710_ = lean_expr_instantiate_rev(v_value_1704_, v_fvars_1694_);
lean_dec_ref(v_value_1704_);
lean_inc_ref(v_post_1690_);
lean_inc_ref(v_pre_1689_);
v___x_1711_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1689_, v_post_1690_, v_usedLetOnly_1691_, v_skipConstInApp_1692_, v_skipInstances_1693_, v___x_1710_, v_a_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___f_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref(v___x_1711_);
v___x_1713_ = lean_box(v_usedLetOnly_1691_);
v___x_1714_ = lean_box(v_skipConstInApp_1692_);
v___x_1715_ = lean_box(v_skipInstances_1693_);
v___f_1716_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1716_, 0, v_fvars_1694_);
lean_closure_set(v___f_1716_, 1, v_pre_1689_);
lean_closure_set(v___f_1716_, 2, v_post_1690_);
lean_closure_set(v___f_1716_, 3, v___x_1713_);
lean_closure_set(v___f_1716_, 4, v___x_1714_);
lean_closure_set(v___f_1716_, 5, v___x_1715_);
lean_closure_set(v___f_1716_, 6, v_body_1705_);
v___x_1717_ = 0;
v___x_1718_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1702_, v_a_1709_, v_a_1712_, v___f_1716_, v_nondep_1706_, v___x_1717_, v_a_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1718_;
}
else
{
lean_dec(v_a_1709_);
lean_dec_ref(v_body_1705_);
lean_dec(v_declName_1702_);
lean_dec_ref(v_fvars_1694_);
lean_dec_ref(v_post_1690_);
lean_dec_ref(v_pre_1689_);
return v___x_1711_;
}
}
else
{
lean_dec_ref(v_body_1705_);
lean_dec_ref(v_value_1704_);
lean_dec(v_declName_1702_);
lean_dec_ref(v_fvars_1694_);
lean_dec_ref(v_post_1690_);
lean_dec_ref(v_pre_1689_);
return v___x_1708_;
}
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_expr_instantiate_rev(v_e_1695_, v_fvars_1694_);
lean_dec_ref(v_e_1695_);
lean_inc_ref(v_post_1690_);
lean_inc_ref(v_pre_1689_);
v___x_1720_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1689_, v_post_1690_, v_usedLetOnly_1691_, v_skipConstInApp_1692_, v_skipInstances_1693_, v___x_1719_, v_a_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; uint8_t v___x_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = 0;
v___x_1723_ = 1;
v___x_1724_ = l_Lean_Meta_mkLetFVars(v_fvars_1694_, v_a_1721_, v_usedLetOnly_1691_, v___x_1722_, v___x_1723_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec_ref(v_fvars_1694_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1689_, v_post_1690_, v_usedLetOnly_1691_, v_skipConstInApp_1692_, v_skipInstances_1693_, v_a_1725_, v_a_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1726_;
}
else
{
lean_dec_ref(v_post_1690_);
lean_dec_ref(v_pre_1689_);
return v___x_1724_;
}
}
else
{
lean_dec_ref(v_fvars_1694_);
lean_dec_ref(v_post_1690_);
lean_dec_ref(v_pre_1689_);
return v___x_1720_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1727_; lean_object* v_dummy_1728_; 
v___x_1727_ = lean_box(0);
v_dummy_1728_ = l_Lean_Expr_sort___override(v___x_1727_);
return v_dummy_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1729_, lean_object* v_post_1730_, uint8_t v_usedLetOnly_1731_, uint8_t v_skipConstInApp_1732_, uint8_t v_skipInstances_1733_, size_t v_sz_1734_, size_t v_i_1735_, lean_object* v_bs_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1735_, v_sz_1734_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec_ref(v_post_1730_);
lean_dec_ref(v_pre_1729_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_bs_1736_);
return v___x_1744_;
}
else
{
lean_object* v_v_1745_; lean_object* v___x_1746_; 
v_v_1745_ = lean_array_uget_borrowed(v_bs_1736_, v_i_1735_);
lean_inc(v_v_1745_);
lean_inc_ref(v_post_1730_);
lean_inc_ref(v_pre_1729_);
v___x_1746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1729_, v_post_1730_, v_usedLetOnly_1731_, v_skipConstInApp_1732_, v_skipInstances_1733_, v_v_1745_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v_bs_x27_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v_bs_x27_1749_ = lean_array_uset(v_bs_1736_, v_i_1735_, v___x_1748_);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1735_, v___x_1750_);
v___x_1752_ = lean_array_uset(v_bs_x27_1749_, v_i_1735_, v_a_1747_);
v_i_1735_ = v___x_1751_;
v_bs_1736_ = v___x_1752_;
goto _start;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v_bs_1736_);
lean_dec_ref(v_post_1730_);
lean_dec_ref(v_pre_1729_);
v_a_1754_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1746_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1746_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1762_, lean_object* v_post_1763_, uint8_t v_usedLetOnly_1764_, uint8_t v_skipConstInApp_1765_, uint8_t v_skipInstances_1766_, lean_object* v___x_1767_, lean_object* v___y_1768_, lean_object* v_b_1769_, lean_object* v_a_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1762_, v_post_1763_, v_usedLetOnly_1764_, v_skipConstInApp_1765_, v_skipInstances_1766_, v___x_1767_, v___y_1768_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1786_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1786_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1786_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1781_ = lean_array_fset(v_b_1769_, v_a_1770_, v_a_1777_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1782_);
v___x_1784_ = v___x_1779_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_b_1769_);
v_a_1787_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1776_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1776_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1795_, lean_object* v_post_1796_, lean_object* v_usedLetOnly_1797_, lean_object* v_skipConstInApp_1798_, lean_object* v_skipInstances_1799_, lean_object* v___x_1800_, lean_object* v___y_1801_, lean_object* v_b_1802_, lean_object* v_a_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v_usedLetOnly_boxed_1809_; uint8_t v_skipConstInApp_boxed_1810_; uint8_t v_skipInstances_boxed_1811_; lean_object* v_res_1812_; 
v_usedLetOnly_boxed_1809_ = lean_unbox(v_usedLetOnly_1797_);
v_skipConstInApp_boxed_1810_ = lean_unbox(v_skipConstInApp_1798_);
v_skipInstances_boxed_1811_ = lean_unbox(v_skipInstances_1799_);
v_res_1812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1795_, v_post_1796_, v_usedLetOnly_boxed_1809_, v_skipConstInApp_boxed_1810_, v_skipInstances_boxed_1811_, v___x_1800_, v___y_1801_, v_b_1802_, v_a_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_a_1803_);
lean_dec(v___y_1801_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1813_, lean_object* v___x_1814_, lean_object* v_pre_1815_, lean_object* v_post_1816_, uint8_t v_usedLetOnly_1817_, uint8_t v_skipConstInApp_1818_, uint8_t v_skipInstances_1819_, lean_object* v_a_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___y_1829_; uint8_t v___x_1852_; 
v___x_1852_ = lean_nat_dec_lt(v_a_1820_, v_upperBound_1813_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
lean_dec(v_a_1820_);
lean_dec_ref(v_post_1816_);
lean_dec_ref(v_pre_1815_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_b_1821_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_array_fget_borrowed(v_b_1821_, v_a_1820_);
v___x_1855_ = lean_array_get_size(v___x_1814_);
v___x_1856_ = lean_nat_dec_lt(v_a_1820_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; 
lean_inc(v___x_1854_);
v___x_1857_ = lean_box(v_usedLetOnly_1817_);
v___x_1858_ = lean_box(v_skipConstInApp_1818_);
v___x_1859_ = lean_box(v_skipInstances_1819_);
lean_inc(v_a_1820_);
lean_inc(v___y_1822_);
lean_inc_ref(v_post_1816_);
lean_inc_ref(v_pre_1815_);
v___f_1860_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1860_, 0, v_pre_1815_);
lean_closure_set(v___f_1860_, 1, v_post_1816_);
lean_closure_set(v___f_1860_, 2, v___x_1857_);
lean_closure_set(v___f_1860_, 3, v___x_1858_);
lean_closure_set(v___f_1860_, 4, v___x_1859_);
lean_closure_set(v___f_1860_, 5, v___x_1854_);
lean_closure_set(v___f_1860_, 6, v___y_1822_);
lean_closure_set(v___f_1860_, 7, v_b_1821_);
lean_closure_set(v___f_1860_, 8, v_a_1820_);
v___y_1829_ = v___f_1860_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1861_; uint8_t v_isInstance_1862_; 
v___x_1861_ = lean_array_fget_borrowed(v___x_1814_, v_a_1820_);
v_isInstance_1862_ = lean_ctor_get_uint8(v___x_1861_, sizeof(void*)*1 + 4);
if (v_isInstance_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___f_1866_; 
lean_inc(v___x_1854_);
v___x_1863_ = lean_box(v_usedLetOnly_1817_);
v___x_1864_ = lean_box(v_skipConstInApp_1818_);
v___x_1865_ = lean_box(v_skipInstances_1819_);
lean_inc(v_a_1820_);
lean_inc(v___y_1822_);
lean_inc_ref(v_post_1816_);
lean_inc_ref(v_pre_1815_);
v___f_1866_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1866_, 0, v_pre_1815_);
lean_closure_set(v___f_1866_, 1, v_post_1816_);
lean_closure_set(v___f_1866_, 2, v___x_1863_);
lean_closure_set(v___f_1866_, 3, v___x_1864_);
lean_closure_set(v___f_1866_, 4, v___x_1865_);
lean_closure_set(v___f_1866_, 5, v___x_1854_);
lean_closure_set(v___f_1866_, 6, v___y_1822_);
lean_closure_set(v___f_1866_, 7, v_b_1821_);
lean_closure_set(v___f_1866_, 8, v_a_1820_);
v___y_1829_ = v___f_1866_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1867_; lean_object* v___f_1868_; 
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_b_1821_);
v___f_1868_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1868_, 0, v___x_1867_);
v___y_1829_ = v___f_1868_;
goto v___jp_1828_;
}
}
}
v___jp_1828_:
{
lean_object* v___x_1830_; 
lean_inc(v___y_1826_);
lean_inc_ref(v___y_1825_);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
v___x_1830_ = lean_apply_5(v___y_1829_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, lean_box(0));
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1843_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1843_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1843_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
if (lean_obj_tag(v_a_1831_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; 
lean_dec(v_a_1820_);
lean_dec_ref(v_post_1816_);
lean_dec_ref(v_pre_1815_);
v_a_1835_ = lean_ctor_get(v_a_1831_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v_a_1831_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v_a_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_del_object(v___x_1833_);
v_a_1839_ = lean_ctor_get(v_a_1831_, 0);
lean_inc(v_a_1839_);
lean_dec_ref(v_a_1831_);
v___x_1840_ = lean_unsigned_to_nat(1u);
v___x_1841_ = lean_nat_add(v_a_1820_, v___x_1840_);
lean_dec(v_a_1820_);
v_a_1820_ = v___x_1841_;
v_b_1821_ = v_a_1839_;
goto _start;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1820_);
lean_dec_ref(v_post_1816_);
lean_dec_ref(v_pre_1815_);
v_a_1844_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1830_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1830_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1869_, lean_object* v_pre_1870_, lean_object* v_post_1871_, uint8_t v_usedLetOnly_1872_, uint8_t v_skipConstInApp_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_f_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; 
if (lean_obj_tag(v_x_1874_) == 5)
{
lean_object* v_fn_1932_; lean_object* v_arg_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_fn_1932_ = lean_ctor_get(v_x_1874_, 0);
lean_inc_ref(v_fn_1932_);
v_arg_1933_ = lean_ctor_get(v_x_1874_, 1);
lean_inc_ref(v_arg_1933_);
lean_dec_ref(v_x_1874_);
v___x_1934_ = lean_array_set(v_x_1875_, v_x_1876_, v_arg_1933_);
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_sub(v_x_1876_, v___x_1935_);
lean_dec(v_x_1876_);
v_x_1874_ = v_fn_1932_;
v_x_1875_ = v___x_1934_;
v_x_1876_ = v___x_1936_;
goto _start;
}
else
{
lean_dec(v_x_1876_);
if (v_skipConstInApp_1873_ == 0)
{
goto v___jp_1929_;
}
else
{
uint8_t v___x_1938_; 
v___x_1938_ = l_Lean_Expr_isConst(v_x_1874_);
if (v___x_1938_ == 0)
{
goto v___jp_1929_;
}
else
{
v_f_1884_ = v_x_1874_;
v___y_1885_ = v___y_1877_;
v___y_1886_ = v___y_1878_;
v___y_1887_ = v___y_1879_;
v___y_1888_ = v___y_1880_;
v___y_1889_ = v___y_1881_;
goto v___jp_1883_;
}
}
}
v___jp_1883_:
{
if (v_skipInstances_1869_ == 0)
{
size_t v_sz_1890_; size_t v___x_1891_; lean_object* v___x_1892_; 
v_sz_1890_ = lean_array_size(v_x_1875_);
v___x_1891_ = ((size_t)0ULL);
lean_inc_ref(v_post_1871_);
lean_inc_ref(v_pre_1870_);
v___x_1892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1870_, v_post_1871_, v_usedLetOnly_1872_, v_skipConstInApp_1873_, v_skipInstances_1869_, v_sz_1890_, v___x_1891_, v_x_1875_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = l_Lean_mkAppN(v_f_1884_, v_a_1893_);
lean_dec(v_a_1893_);
v___x_1895_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1870_, v_post_1871_, v_usedLetOnly_1872_, v_skipConstInApp_1873_, v_skipInstances_1869_, v___x_1894_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1895_;
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec_ref(v_f_1884_);
lean_dec_ref(v_post_1871_);
lean_dec_ref(v_pre_1870_);
v_a_1896_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1892_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1892_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_array_get_size(v_x_1875_);
lean_inc_ref(v_f_1884_);
v___x_1905_ = l_Lean_Meta_getFunInfoNArgs(v_f_1884_, v___x_1904_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v_paramInfo_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v_paramInfo_1907_ = lean_ctor_get(v_a_1906_, 0);
lean_inc_ref(v_paramInfo_1907_);
lean_dec(v_a_1906_);
v___x_1908_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1871_);
lean_inc_ref(v_pre_1870_);
v___x_1909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1904_, v_paramInfo_1907_, v_pre_1870_, v_post_1871_, v_usedLetOnly_1872_, v_skipConstInApp_1873_, v_skipInstances_1869_, v___x_1908_, v_x_1875_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec_ref(v_paramInfo_1907_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref(v___x_1909_);
v___x_1911_ = l_Lean_mkAppN(v_f_1884_, v_a_1910_);
lean_dec(v_a_1910_);
v___x_1912_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1870_, v_post_1871_, v_usedLetOnly_1872_, v_skipConstInApp_1873_, v_skipInstances_1869_, v___x_1911_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
return v___x_1912_;
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_f_1884_);
lean_dec_ref(v_post_1871_);
lean_dec_ref(v_pre_1870_);
v_a_1913_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1909_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1909_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_f_1884_);
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_post_1871_);
lean_dec_ref(v_pre_1870_);
v_a_1921_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1905_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1905_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
v___jp_1929_:
{
lean_object* v___x_1930_; 
lean_inc_ref(v_post_1871_);
lean_inc_ref(v_pre_1870_);
v___x_1930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1870_, v_post_1871_, v_usedLetOnly_1872_, v_skipConstInApp_1873_, v_skipInstances_1869_, v_x_1874_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1930_);
v_f_1884_ = v_a_1931_;
v___y_1885_ = v___y_1877_;
v___y_1886_ = v___y_1878_;
v___y_1887_ = v___y_1879_;
v___y_1888_ = v___y_1880_;
v___y_1889_ = v___y_1881_;
goto v___jp_1883_;
}
else
{
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_post_1871_);
lean_dec_ref(v_pre_1870_);
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1939_, lean_object* v_pre_1940_, lean_object* v_e_1941_, lean_object* v_post_1942_, uint8_t v_usedLetOnly_1943_, uint8_t v_skipConstInApp_1944_, uint8_t v_skipInstances_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_Core_checkSystem(v___x_1939_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1953_; 
lean_dec_ref(v___x_1952_);
lean_inc_ref(v_pre_1940_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc_ref(v_e_1941_);
v___x_1953_ = lean_apply_6(v_pre_1940_, v_e_1941_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, lean_box(0));
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2002_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1956_ = v___x_1953_;
v_isShared_1957_ = v_isSharedCheck_2002_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2002_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___y_1959_; 
switch(lean_obj_tag(v_a_1954_))
{
case 0:
{
lean_object* v_e_1994_; lean_object* v___x_1996_; 
lean_dec_ref(v_post_1942_);
lean_dec_ref(v_e_1941_);
lean_dec_ref(v_pre_1940_);
v_e_1994_ = lean_ctor_get(v_a_1954_, 0);
lean_inc_ref(v_e_1994_);
lean_dec_ref(v_a_1954_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v_e_1994_);
v___x_1996_ = v___x_1956_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_e_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
case 1:
{
lean_object* v_e_1998_; lean_object* v___x_1999_; 
lean_del_object(v___x_1956_);
lean_dec_ref(v_e_1941_);
v_e_1998_ = lean_ctor_get(v_a_1954_, 0);
lean_inc_ref(v_e_1998_);
lean_dec_ref(v_a_1954_);
v___x_1999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v_e_1998_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1999_;
}
default: 
{
lean_object* v_e_x3f_2000_; 
lean_del_object(v___x_1956_);
v_e_x3f_2000_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_e_x3f_2000_);
lean_dec_ref(v_a_1954_);
if (lean_obj_tag(v_e_x3f_2000_) == 0)
{
v___y_1959_ = v_e_1941_;
goto v___jp_1958_;
}
else
{
lean_object* v_val_2001_; 
lean_dec_ref(v_e_1941_);
v_val_2001_ = lean_ctor_get(v_e_x3f_2000_, 0);
lean_inc(v_val_2001_);
lean_dec_ref(v_e_x3f_2000_);
v___y_1959_ = v_val_2001_;
goto v___jp_1958_;
}
}
}
v___jp_1958_:
{
switch(lean_obj_tag(v___y_1959_))
{
case 7:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v___x_1960_, v___y_1959_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1961_;
}
case 6:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1963_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v___x_1962_, v___y_1959_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1963_;
}
case 8:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1965_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v___x_1964_, v___y_1959_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1965_;
}
case 5:
{
lean_object* v_dummy_1966_; lean_object* v_nargs_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_dummy_1966_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1967_ = l_Lean_Expr_getAppNumArgs(v___y_1959_);
lean_inc(v_nargs_1967_);
v___x_1968_ = lean_mk_array(v_nargs_1967_, v_dummy_1966_);
v___x_1969_ = lean_unsigned_to_nat(1u);
v___x_1970_ = lean_nat_sub(v_nargs_1967_, v___x_1969_);
lean_dec(v_nargs_1967_);
v___x_1971_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1945_, v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v___y_1959_, v___x_1968_, v___x_1970_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1971_;
}
case 10:
{
lean_object* v_data_1972_; lean_object* v_expr_1973_; lean_object* v___x_1974_; 
v_data_1972_ = lean_ctor_get(v___y_1959_, 0);
v_expr_1973_ = lean_ctor_get(v___y_1959_, 1);
lean_inc_ref(v_expr_1973_);
lean_inc_ref(v_post_1942_);
lean_inc_ref(v_pre_1940_);
v___x_1974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v_expr_1973_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; size_t v___x_1976_; size_t v___x_1977_; uint8_t v___x_1978_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref(v___x_1974_);
v___x_1976_ = lean_ptr_addr(v_expr_1973_);
v___x_1977_ = lean_ptr_addr(v_a_1975_);
v___x_1978_ = lean_usize_dec_eq(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_inc(v_data_1972_);
lean_dec_ref(v___y_1959_);
v___x_1979_ = l_Lean_Expr_mdata___override(v_data_1972_, v_a_1975_);
v___x_1980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v___x_1979_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; 
lean_dec(v_a_1975_);
v___x_1981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v___y_1959_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1981_;
}
}
else
{
lean_dec_ref(v___y_1959_);
lean_dec_ref(v_post_1942_);
lean_dec_ref(v_pre_1940_);
return v___x_1974_;
}
}
case 11:
{
lean_object* v_typeName_1982_; lean_object* v_idx_1983_; lean_object* v_struct_1984_; lean_object* v___x_1985_; 
v_typeName_1982_ = lean_ctor_get(v___y_1959_, 0);
v_idx_1983_ = lean_ctor_get(v___y_1959_, 1);
v_struct_1984_ = lean_ctor_get(v___y_1959_, 2);
lean_inc_ref(v_struct_1984_);
lean_inc_ref(v_post_1942_);
lean_inc_ref(v_pre_1940_);
v___x_1985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v_struct_1984_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; size_t v___x_1987_; size_t v___x_1988_; uint8_t v___x_1989_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref(v___x_1985_);
v___x_1987_ = lean_ptr_addr(v_struct_1984_);
v___x_1988_ = lean_ptr_addr(v_a_1986_);
v___x_1989_ = lean_usize_dec_eq(v___x_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_inc(v_idx_1983_);
lean_inc(v_typeName_1982_);
lean_dec_ref(v___y_1959_);
v___x_1990_ = l_Lean_Expr_proj___override(v_typeName_1982_, v_idx_1983_, v_a_1986_);
v___x_1991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v___x_1990_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; 
lean_dec(v_a_1986_);
v___x_1992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v___y_1959_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1992_;
}
}
else
{
lean_dec_ref(v___y_1959_);
lean_dec_ref(v_post_1942_);
lean_dec_ref(v_pre_1940_);
return v___x_1985_;
}
}
default: 
{
lean_object* v___x_1993_; 
v___x_1993_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1940_, v_post_1942_, v_usedLetOnly_1943_, v_skipConstInApp_1944_, v_skipInstances_1945_, v___y_1959_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1993_;
}
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v_post_1942_);
lean_dec_ref(v_e_1941_);
lean_dec_ref(v_pre_1940_);
v_a_2003_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1953_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1953_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v_post_1942_);
lean_dec_ref(v_e_1941_);
lean_dec_ref(v_pre_1940_);
v_a_2011_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1952_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1952_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2019_, lean_object* v_pre_2020_, lean_object* v_e_2021_, lean_object* v_post_2022_, lean_object* v_usedLetOnly_2023_, lean_object* v_skipConstInApp_2024_, lean_object* v_skipInstances_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
uint8_t v_usedLetOnly_boxed_2032_; uint8_t v_skipConstInApp_boxed_2033_; uint8_t v_skipInstances_boxed_2034_; lean_object* v_res_2035_; 
v_usedLetOnly_boxed_2032_ = lean_unbox(v_usedLetOnly_2023_);
v_skipConstInApp_boxed_2033_ = lean_unbox(v_skipConstInApp_2024_);
v_skipInstances_boxed_2034_ = lean_unbox(v_skipInstances_2025_);
v_res_2035_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2019_, v_pre_2020_, v_e_2021_, v_post_2022_, v_usedLetOnly_boxed_2032_, v_skipConstInApp_boxed_2033_, v_skipInstances_boxed_2034_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2036_, lean_object* v_post_2037_, uint8_t v_usedLetOnly_2038_, uint8_t v_skipConstInApp_2039_, uint8_t v_skipInstances_2040_, lean_object* v_e_2041_, lean_object* v_a_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_inc(v_a_2042_);
v___x_2048_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2048_, 0, lean_box(0));
lean_closure_set(v___x_2048_, 1, lean_box(0));
lean_closure_set(v___x_2048_, 2, v_a_2042_);
v___x_2049_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2048_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2084_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2084_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2084_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2050_, v_e_2041_);
lean_dec(v_a_2050_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; 
lean_del_object(v___x_2052_);
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2056_ = lean_box(v_usedLetOnly_2038_);
v___x_2057_ = lean_box(v_skipConstInApp_2039_);
v___x_2058_ = lean_box(v_skipInstances_2040_);
lean_inc_ref(v_e_2041_);
v___f_2059_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2059_, 0, v___x_2055_);
lean_closure_set(v___f_2059_, 1, v_pre_2036_);
lean_closure_set(v___f_2059_, 2, v_e_2041_);
lean_closure_set(v___f_2059_, 3, v_post_2037_);
lean_closure_set(v___f_2059_, 4, v___x_2056_);
lean_closure_set(v___f_2059_, 5, v___x_2057_);
lean_closure_set(v___f_2059_, 6, v___x_2058_);
v___x_2060_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2059_, v_a_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___f_2062_; lean_object* v___x_2063_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc_n(v_a_2061_, 2);
lean_dec_ref(v___x_2060_);
lean_inc(v_a_2042_);
v___f_2062_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2062_, 0, v_a_2042_);
lean_closure_set(v___f_2062_, 1, v_e_2041_);
lean_closure_set(v___f_2062_, 2, v_a_2061_);
v___x_2063_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2062_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v___x_2063_, 0);
lean_dec(v_unused_2071_);
v___x_2065_ = v___x_2063_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_dec(v___x_2063_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v_a_2061_);
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2061_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_a_2061_);
v_a_2072_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2063_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2063_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
lean_dec_ref(v_e_2041_);
return v___x_2060_;
}
}
else
{
lean_object* v_val_2080_; lean_object* v___x_2082_; 
lean_dec_ref(v_e_2041_);
lean_dec_ref(v_post_2037_);
lean_dec_ref(v_pre_2036_);
v_val_2080_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_val_2080_);
lean_dec_ref(v___x_2054_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v_val_2080_);
v___x_2082_ = v___x_2052_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_val_2080_);
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
lean_dec_ref(v_e_2041_);
lean_dec_ref(v_post_2037_);
lean_dec_ref(v_pre_2036_);
v_a_2085_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2049_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2049_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2093_, lean_object* v_pre_2094_, lean_object* v_post_2095_, lean_object* v_usedLetOnly_2096_, lean_object* v_skipConstInApp_2097_, lean_object* v_skipInstances_2098_, lean_object* v_body_2099_, lean_object* v_x_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v_usedLetOnly_boxed_2107_; uint8_t v_skipConstInApp_boxed_2108_; uint8_t v_skipInstances_boxed_2109_; lean_object* v_res_2110_; 
v_usedLetOnly_boxed_2107_ = lean_unbox(v_usedLetOnly_2096_);
v_skipConstInApp_boxed_2108_ = lean_unbox(v_skipConstInApp_2097_);
v_skipInstances_boxed_2109_ = lean_unbox(v_skipInstances_2098_);
v_res_2110_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2093_, v_pre_2094_, v_post_2095_, v_usedLetOnly_boxed_2107_, v_skipConstInApp_boxed_2108_, v_skipInstances_boxed_2109_, v_body_2099_, v_x_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2111_, lean_object* v_post_2112_, uint8_t v_usedLetOnly_2113_, uint8_t v_skipConstInApp_2114_, uint8_t v_skipInstances_2115_, lean_object* v_fvars_2116_, lean_object* v_e_2117_, lean_object* v_a_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
if (lean_obj_tag(v_e_2117_) == 7)
{
lean_object* v_binderName_2124_; lean_object* v_binderType_2125_; lean_object* v_body_2126_; uint8_t v_binderInfo_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_binderName_2124_ = lean_ctor_get(v_e_2117_, 0);
lean_inc(v_binderName_2124_);
v_binderType_2125_ = lean_ctor_get(v_e_2117_, 1);
lean_inc_ref(v_binderType_2125_);
v_body_2126_ = lean_ctor_get(v_e_2117_, 2);
lean_inc_ref(v_body_2126_);
v_binderInfo_2127_ = lean_ctor_get_uint8(v_e_2117_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2117_);
v___x_2128_ = lean_expr_instantiate_rev(v_binderType_2125_, v_fvars_2116_);
lean_dec_ref(v_binderType_2125_);
lean_inc_ref(v_post_2112_);
lean_inc_ref(v_pre_2111_);
v___x_2129_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2111_, v_post_2112_, v_usedLetOnly_2113_, v_skipConstInApp_2114_, v_skipInstances_2115_, v___x_2128_, v_a_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = lean_box(v_usedLetOnly_2113_);
v___x_2132_ = lean_box(v_skipConstInApp_2114_);
v___x_2133_ = lean_box(v_skipInstances_2115_);
v___f_2134_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2134_, 0, v_fvars_2116_);
lean_closure_set(v___f_2134_, 1, v_pre_2111_);
lean_closure_set(v___f_2134_, 2, v_post_2112_);
lean_closure_set(v___f_2134_, 3, v___x_2131_);
lean_closure_set(v___f_2134_, 4, v___x_2132_);
lean_closure_set(v___f_2134_, 5, v___x_2133_);
lean_closure_set(v___f_2134_, 6, v_body_2126_);
v___x_2135_ = 0;
v___x_2136_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2124_, v_binderInfo_2127_, v_a_2130_, v___f_2134_, v___x_2135_, v_a_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2136_;
}
else
{
lean_dec_ref(v_body_2126_);
lean_dec(v_binderName_2124_);
lean_dec_ref(v_fvars_2116_);
lean_dec_ref(v_post_2112_);
lean_dec_ref(v_pre_2111_);
return v___x_2129_;
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_expr_instantiate_rev(v_e_2117_, v_fvars_2116_);
lean_dec_ref(v_e_2117_);
lean_inc_ref(v_post_2112_);
lean_inc_ref(v_pre_2111_);
v___x_2138_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2111_, v_post_2112_, v_usedLetOnly_2113_, v_skipConstInApp_2114_, v_skipInstances_2115_, v___x_2137_, v_a_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; uint8_t v___x_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v___x_2140_ = 0;
v___x_2141_ = 1;
v___x_2142_ = 1;
v___x_2143_ = l_Lean_Meta_mkForallFVars(v_fvars_2116_, v_a_2139_, v___x_2140_, v_usedLetOnly_2113_, v___x_2141_, v___x_2142_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec_ref(v_fvars_2116_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2143_);
v___x_2145_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2111_, v_post_2112_, v_usedLetOnly_2113_, v_skipConstInApp_2114_, v_skipInstances_2115_, v_a_2144_, v_a_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2145_;
}
else
{
lean_dec_ref(v_post_2112_);
lean_dec_ref(v_pre_2111_);
return v___x_2143_;
}
}
else
{
lean_dec_ref(v_fvars_2116_);
lean_dec_ref(v_post_2112_);
lean_dec_ref(v_pre_2111_);
return v___x_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2146_, lean_object* v_pre_2147_, lean_object* v_post_2148_, uint8_t v_usedLetOnly_2149_, uint8_t v_skipConstInApp_2150_, uint8_t v_skipInstances_2151_, lean_object* v_body_2152_, lean_object* v_x_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_array_push(v_fvars_2146_, v_x_2153_);
v___x_2161_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2147_, v_post_2148_, v_usedLetOnly_2149_, v_skipConstInApp_2150_, v_skipInstances_2151_, v___x_2160_, v_body_2152_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2162_, lean_object* v_post_2163_, lean_object* v_usedLetOnly_2164_, lean_object* v_skipConstInApp_2165_, lean_object* v_skipInstances_2166_, lean_object* v_e_2167_, lean_object* v_a_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v_usedLetOnly_boxed_2174_; uint8_t v_skipConstInApp_boxed_2175_; uint8_t v_skipInstances_boxed_2176_; lean_object* v_res_2177_; 
v_usedLetOnly_boxed_2174_ = lean_unbox(v_usedLetOnly_2164_);
v_skipConstInApp_boxed_2175_ = lean_unbox(v_skipConstInApp_2165_);
v_skipInstances_boxed_2176_ = lean_unbox(v_skipInstances_2166_);
v_res_2177_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2162_, v_post_2163_, v_usedLetOnly_boxed_2174_, v_skipConstInApp_boxed_2175_, v_skipInstances_boxed_2176_, v_e_2167_, v_a_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v_a_2168_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2178_, lean_object* v_post_2179_, lean_object* v_usedLetOnly_2180_, lean_object* v_skipConstInApp_2181_, lean_object* v_skipInstances_2182_, lean_object* v_sz_2183_, lean_object* v_i_2184_, lean_object* v_bs_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
uint8_t v_usedLetOnly_boxed_2192_; uint8_t v_skipConstInApp_boxed_2193_; uint8_t v_skipInstances_boxed_2194_; size_t v_sz_boxed_2195_; size_t v_i_boxed_2196_; lean_object* v_res_2197_; 
v_usedLetOnly_boxed_2192_ = lean_unbox(v_usedLetOnly_2180_);
v_skipConstInApp_boxed_2193_ = lean_unbox(v_skipConstInApp_2181_);
v_skipInstances_boxed_2194_ = lean_unbox(v_skipInstances_2182_);
v_sz_boxed_2195_ = lean_unbox_usize(v_sz_2183_);
lean_dec(v_sz_2183_);
v_i_boxed_2196_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2178_, v_post_2179_, v_usedLetOnly_boxed_2192_, v_skipConstInApp_boxed_2193_, v_skipInstances_boxed_2194_, v_sz_boxed_2195_, v_i_boxed_2196_, v_bs_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2198_, lean_object* v_post_2199_, lean_object* v_usedLetOnly_2200_, lean_object* v_skipConstInApp_2201_, lean_object* v_skipInstances_2202_, lean_object* v_e_2203_, lean_object* v_a_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
uint8_t v_usedLetOnly_boxed_2210_; uint8_t v_skipConstInApp_boxed_2211_; uint8_t v_skipInstances_boxed_2212_; lean_object* v_res_2213_; 
v_usedLetOnly_boxed_2210_ = lean_unbox(v_usedLetOnly_2200_);
v_skipConstInApp_boxed_2211_ = lean_unbox(v_skipConstInApp_2201_);
v_skipInstances_boxed_2212_ = lean_unbox(v_skipInstances_2202_);
v_res_2213_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2198_, v_post_2199_, v_usedLetOnly_boxed_2210_, v_skipConstInApp_boxed_2211_, v_skipInstances_boxed_2212_, v_e_2203_, v_a_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v_a_2204_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2214_, lean_object* v_post_2215_, lean_object* v_usedLetOnly_2216_, lean_object* v_skipConstInApp_2217_, lean_object* v_skipInstances_2218_, lean_object* v_fvars_2219_, lean_object* v_e_2220_, lean_object* v_a_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v_usedLetOnly_boxed_2227_; uint8_t v_skipConstInApp_boxed_2228_; uint8_t v_skipInstances_boxed_2229_; lean_object* v_res_2230_; 
v_usedLetOnly_boxed_2227_ = lean_unbox(v_usedLetOnly_2216_);
v_skipConstInApp_boxed_2228_ = lean_unbox(v_skipConstInApp_2217_);
v_skipInstances_boxed_2229_ = lean_unbox(v_skipInstances_2218_);
v_res_2230_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2214_, v_post_2215_, v_usedLetOnly_boxed_2227_, v_skipConstInApp_boxed_2228_, v_skipInstances_boxed_2229_, v_fvars_2219_, v_e_2220_, v_a_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v_a_2221_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2231_, lean_object* v_post_2232_, lean_object* v_usedLetOnly_2233_, lean_object* v_skipConstInApp_2234_, lean_object* v_skipInstances_2235_, lean_object* v_fvars_2236_, lean_object* v_e_2237_, lean_object* v_a_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
uint8_t v_usedLetOnly_boxed_2244_; uint8_t v_skipConstInApp_boxed_2245_; uint8_t v_skipInstances_boxed_2246_; lean_object* v_res_2247_; 
v_usedLetOnly_boxed_2244_ = lean_unbox(v_usedLetOnly_2233_);
v_skipConstInApp_boxed_2245_ = lean_unbox(v_skipConstInApp_2234_);
v_skipInstances_boxed_2246_ = lean_unbox(v_skipInstances_2235_);
v_res_2247_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2231_, v_post_2232_, v_usedLetOnly_boxed_2244_, v_skipConstInApp_boxed_2245_, v_skipInstances_boxed_2246_, v_fvars_2236_, v_e_2237_, v_a_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v_a_2238_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2248_, lean_object* v_post_2249_, lean_object* v_usedLetOnly_2250_, lean_object* v_skipConstInApp_2251_, lean_object* v_skipInstances_2252_, lean_object* v_fvars_2253_, lean_object* v_e_2254_, lean_object* v_a_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_usedLetOnly_boxed_2261_; uint8_t v_skipConstInApp_boxed_2262_; uint8_t v_skipInstances_boxed_2263_; lean_object* v_res_2264_; 
v_usedLetOnly_boxed_2261_ = lean_unbox(v_usedLetOnly_2250_);
v_skipConstInApp_boxed_2262_ = lean_unbox(v_skipConstInApp_2251_);
v_skipInstances_boxed_2263_ = lean_unbox(v_skipInstances_2252_);
v_res_2264_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2248_, v_post_2249_, v_usedLetOnly_boxed_2261_, v_skipConstInApp_boxed_2262_, v_skipInstances_boxed_2263_, v_fvars_2253_, v_e_2254_, v_a_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v_a_2255_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2265_, lean_object* v___x_2266_, lean_object* v_pre_2267_, lean_object* v_post_2268_, lean_object* v_usedLetOnly_2269_, lean_object* v_skipConstInApp_2270_, lean_object* v_skipInstances_2271_, lean_object* v_a_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v_usedLetOnly_boxed_2280_; uint8_t v_skipConstInApp_boxed_2281_; uint8_t v_skipInstances_boxed_2282_; lean_object* v_res_2283_; 
v_usedLetOnly_boxed_2280_ = lean_unbox(v_usedLetOnly_2269_);
v_skipConstInApp_boxed_2281_ = lean_unbox(v_skipConstInApp_2270_);
v_skipInstances_boxed_2282_ = lean_unbox(v_skipInstances_2271_);
v_res_2283_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2265_, v___x_2266_, v_pre_2267_, v_post_2268_, v_usedLetOnly_boxed_2280_, v_skipConstInApp_boxed_2281_, v_skipInstances_boxed_2282_, v_a_2272_, v_b_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___x_2266_);
lean_dec(v_upperBound_2265_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2284_, lean_object* v_pre_2285_, lean_object* v_post_2286_, lean_object* v_usedLetOnly_2287_, lean_object* v_skipConstInApp_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v_skipInstances_boxed_2298_; uint8_t v_usedLetOnly_boxed_2299_; uint8_t v_skipConstInApp_boxed_2300_; lean_object* v_res_2301_; 
v_skipInstances_boxed_2298_ = lean_unbox(v_skipInstances_2284_);
v_usedLetOnly_boxed_2299_ = lean_unbox(v_usedLetOnly_2287_);
v_skipConstInApp_boxed_2300_ = lean_unbox(v_skipConstInApp_2288_);
v_res_2301_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2298_, v_pre_2285_, v_post_2286_, v_usedLetOnly_boxed_2299_, v_skipConstInApp_boxed_2300_, v_x_2289_, v_x_2290_, v_x_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
return v_res_2301_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2303_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2303_, 0, lean_box(0));
lean_closure_set(v___x_2303_, 1, lean_box(0));
lean_closure_set(v___x_2303_, 2, v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2304_, lean_object* v_pre_2305_, lean_object* v_post_2306_, uint8_t v_usedLetOnly_2307_, uint8_t v_skipConstInApp_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v_a_2316_; uint8_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2314_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2315_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2314_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
v___x_2317_ = 0;
v___x_2318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2305_, v_post_2306_, v_usedLetOnly_2307_, v_skipConstInApp_2308_, v___x_2317_, v_input_2304_, v_a_2316_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2320_, 0, lean_box(0));
lean_closure_set(v___x_2320_, 1, lean_box(0));
lean_closure_set(v___x_2320_, 2, v_a_2316_);
v___x_2321_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2320_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; 
v_unused_2329_ = lean_ctor_get(v___x_2321_, 0);
lean_dec(v_unused_2329_);
v___x_2323_ = v___x_2321_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_dec(v___x_2321_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v_a_2319_);
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2319_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
lean_dec(v_a_2316_);
return v___x_2318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2330_, lean_object* v_pre_2331_, lean_object* v_post_2332_, lean_object* v_usedLetOnly_2333_, lean_object* v_skipConstInApp_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
uint8_t v_usedLetOnly_boxed_2340_; uint8_t v_skipConstInApp_boxed_2341_; lean_object* v_res_2342_; 
v_usedLetOnly_boxed_2340_ = lean_unbox(v_usedLetOnly_2333_);
v_skipConstInApp_boxed_2341_ = lean_unbox(v_skipConstInApp_2334_);
v_res_2342_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2330_, v_pre_2331_, v_post_2332_, v_usedLetOnly_boxed_2340_, v_skipConstInApp_boxed_2341_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2343_, lean_object* v_as_2344_, lean_object* v_j_2345_){
_start:
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_array_get_size(v_as_2344_);
v___x_2347_ = lean_nat_dec_lt(v_j_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec(v_j_2345_);
v___x_2348_ = lean_box(0);
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; lean_object* v_declName_2350_; uint8_t v___x_2351_; 
v___x_2349_ = lean_array_fget_borrowed(v_as_2344_, v_j_2345_);
v_declName_2350_ = lean_ctor_get(v___x_2349_, 3);
v___x_2351_ = lean_name_eq(v_declName_2350_, v___x_2343_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = lean_unsigned_to_nat(1u);
v___x_2353_ = lean_nat_add(v_j_2345_, v___x_2352_);
lean_dec(v_j_2345_);
v_j_2345_ = v___x_2353_;
goto _start;
}
else
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_j_2345_);
return v___x_2355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2356_, lean_object* v_as_2357_, lean_object* v_j_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2356_, v_as_2357_, v_j_2358_);
lean_dec_ref(v_as_2357_);
lean_dec(v___x_2356_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_st_ref_get(v_val_2360_);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v_val_2368_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2375_, lean_object* v_val_2376_, lean_object* v_a_2377_, lean_object* v___x_2378_, lean_object* v_____r_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2385_ = lean_st_ref_take(v_val_2375_);
v___x_2386_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2376_, v_a_2377_, v___x_2385_);
v___x_2387_ = lean_st_ref_set(v_val_2375_, v___x_2386_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2378_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2390_, lean_object* v_val_2391_, lean_object* v_a_2392_, lean_object* v___x_2393_, lean_object* v_____r_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2390_, v_val_2391_, v_a_2392_, v___x_2393_, v_____r_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v_val_2391_);
lean_dec(v_val_2390_);
return v_res_2400_;
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0(void){
_start:
{
uint8_t v___x_2401_; uint64_t v___x_2402_; 
v___x_2401_ = 2;
v___x_2402_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_upperBound_2403_, lean_object* v_val_2404_, lean_object* v_next_2405_, lean_object* v_params_2406_, lean_object* v___x_2407_, lean_object* v_val_2408_, lean_object* v_next_2409_, uint8_t v___x_2410_, lean_object* v_a_2411_, uint8_t v_b_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
uint8_t v_a_2419_; uint8_t v___x_2423_; 
v___x_2423_ = lean_nat_dec_lt(v_a_2411_, v_upperBound_2403_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_dec(v_a_2411_);
lean_dec(v_next_2409_);
lean_dec_ref(v___x_2407_);
v___x_2424_ = lean_box(v_b_2412_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = lean_st_ref_get(v_val_2404_);
v___x_2427_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2405_, v_a_2411_, v___x_2426_);
lean_dec(v___x_2426_);
if (v___x_2427_ == 0)
{
v_a_2419_ = v_b_2412_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2428_; uint8_t v_foApprox_2429_; uint8_t v_ctxApprox_2430_; uint8_t v_quasiPatternApprox_2431_; uint8_t v_constApprox_2432_; uint8_t v_isDefEqStuckEx_2433_; uint8_t v_unificationHints_2434_; uint8_t v_assignSyntheticOpaque_2435_; uint8_t v_offsetCnstrs_2436_; uint8_t v_transparency_2437_; uint8_t v_etaStruct_2438_; uint8_t v_univApprox_2439_; uint8_t v_iota_2440_; uint8_t v_beta_2441_; uint8_t v_proj_2442_; uint8_t v_zeta_2443_; uint8_t v_zetaDelta_2444_; uint8_t v_zetaUnused_2445_; uint8_t v_zetaHave_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2509_; 
v___x_2428_ = l_Lean_Meta_Context_config(v___y_2413_);
v_foApprox_2429_ = lean_ctor_get_uint8(v___x_2428_, 0);
v_ctxApprox_2430_ = lean_ctor_get_uint8(v___x_2428_, 1);
v_quasiPatternApprox_2431_ = lean_ctor_get_uint8(v___x_2428_, 2);
v_constApprox_2432_ = lean_ctor_get_uint8(v___x_2428_, 3);
v_isDefEqStuckEx_2433_ = lean_ctor_get_uint8(v___x_2428_, 4);
v_unificationHints_2434_ = lean_ctor_get_uint8(v___x_2428_, 5);
v_assignSyntheticOpaque_2435_ = lean_ctor_get_uint8(v___x_2428_, 7);
v_offsetCnstrs_2436_ = lean_ctor_get_uint8(v___x_2428_, 8);
v_transparency_2437_ = lean_ctor_get_uint8(v___x_2428_, 9);
v_etaStruct_2438_ = lean_ctor_get_uint8(v___x_2428_, 10);
v_univApprox_2439_ = lean_ctor_get_uint8(v___x_2428_, 11);
v_iota_2440_ = lean_ctor_get_uint8(v___x_2428_, 12);
v_beta_2441_ = lean_ctor_get_uint8(v___x_2428_, 13);
v_proj_2442_ = lean_ctor_get_uint8(v___x_2428_, 14);
v_zeta_2443_ = lean_ctor_get_uint8(v___x_2428_, 15);
v_zetaDelta_2444_ = lean_ctor_get_uint8(v___x_2428_, 16);
v_zetaUnused_2445_ = lean_ctor_get_uint8(v___x_2428_, 17);
v_zetaHave_2446_ = lean_ctor_get_uint8(v___x_2428_, 18);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2448_ = v___x_2428_;
v_isShared_2449_ = v_isSharedCheck_2509_;
goto v_resetjp_2447_;
}
else
{
lean_dec(v___x_2428_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2509_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint8_t v_trackZetaDelta_2450_; lean_object* v_zetaDeltaSet_2451_; lean_object* v_lctx_2452_; lean_object* v_localInstances_2453_; lean_object* v_defEqCtx_x3f_2454_; lean_object* v_synthPendingDepth_2455_; lean_object* v_canUnfold_x3f_2456_; uint8_t v_univApprox_2457_; uint8_t v_inTypeClassResolution_2458_; uint8_t v_cacheInferType_2459_; uint8_t v___x_2460_; lean_object* v___x_2462_; 
v_trackZetaDelta_2450_ = lean_ctor_get_uint8(v___y_2413_, sizeof(void*)*7);
v_zetaDeltaSet_2451_ = lean_ctor_get(v___y_2413_, 1);
v_lctx_2452_ = lean_ctor_get(v___y_2413_, 2);
v_localInstances_2453_ = lean_ctor_get(v___y_2413_, 3);
v_defEqCtx_x3f_2454_ = lean_ctor_get(v___y_2413_, 4);
v_synthPendingDepth_2455_ = lean_ctor_get(v___y_2413_, 5);
v_canUnfold_x3f_2456_ = lean_ctor_get(v___y_2413_, 6);
v_univApprox_2457_ = lean_ctor_get_uint8(v___y_2413_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2458_ = lean_ctor_get_uint8(v___y_2413_, sizeof(void*)*7 + 2);
v_cacheInferType_2459_ = lean_ctor_get_uint8(v___y_2413_, sizeof(void*)*7 + 3);
v___x_2460_ = 0;
if (v_isShared_2449_ == 0)
{
v___x_2462_ = v___x_2448_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 0, v_foApprox_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 1, v_ctxApprox_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 2, v_quasiPatternApprox_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 3, v_constApprox_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 4, v_isDefEqStuckEx_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 5, v_unificationHints_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 7, v_assignSyntheticOpaque_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 8, v_offsetCnstrs_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 9, v_transparency_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 10, v_etaStruct_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 11, v_univApprox_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 12, v_iota_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 13, v_beta_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 14, v_proj_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 15, v_zeta_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 16, v_zetaDelta_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 17, v_zetaUnused_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2508_, 18, v_zetaHave_2446_);
v___x_2462_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
uint64_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v_foApprox_2467_; uint8_t v_ctxApprox_2468_; uint8_t v_quasiPatternApprox_2469_; uint8_t v_constApprox_2470_; uint8_t v_isDefEqStuckEx_2471_; uint8_t v_unificationHints_2472_; uint8_t v_proofIrrelevance_2473_; uint8_t v_assignSyntheticOpaque_2474_; uint8_t v_offsetCnstrs_2475_; uint8_t v_etaStruct_2476_; uint8_t v_univApprox_2477_; uint8_t v_iota_2478_; uint8_t v_beta_2479_; uint8_t v_proj_2480_; uint8_t v_zeta_2481_; uint8_t v_zetaDelta_2482_; uint8_t v_zetaUnused_2483_; uint8_t v_zetaHave_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2507_; 
lean_ctor_set_uint8(v___x_2462_, 6, v___x_2460_);
v___x_2463_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2462_);
v___x_2464_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2464_, 0, v___x_2462_);
lean_ctor_set_uint64(v___x_2464_, sizeof(void*)*1, v___x_2463_);
lean_inc(v_canUnfold_x3f_2456_);
lean_inc(v_synthPendingDepth_2455_);
lean_inc(v_defEqCtx_x3f_2454_);
lean_inc_ref(v_localInstances_2453_);
lean_inc_ref(v_lctx_2452_);
lean_inc(v_zetaDeltaSet_2451_);
v___x_2465_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
lean_ctor_set(v___x_2465_, 1, v_zetaDeltaSet_2451_);
lean_ctor_set(v___x_2465_, 2, v_lctx_2452_);
lean_ctor_set(v___x_2465_, 3, v_localInstances_2453_);
lean_ctor_set(v___x_2465_, 4, v_defEqCtx_x3f_2454_);
lean_ctor_set(v___x_2465_, 5, v_synthPendingDepth_2455_);
lean_ctor_set(v___x_2465_, 6, v_canUnfold_x3f_2456_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*7, v_trackZetaDelta_2450_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*7 + 1, v_univApprox_2457_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2458_);
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*7 + 3, v_cacheInferType_2459_);
v___x_2466_ = l_Lean_Meta_Context_config(v___x_2465_);
v_foApprox_2467_ = lean_ctor_get_uint8(v___x_2466_, 0);
v_ctxApprox_2468_ = lean_ctor_get_uint8(v___x_2466_, 1);
v_quasiPatternApprox_2469_ = lean_ctor_get_uint8(v___x_2466_, 2);
v_constApprox_2470_ = lean_ctor_get_uint8(v___x_2466_, 3);
v_isDefEqStuckEx_2471_ = lean_ctor_get_uint8(v___x_2466_, 4);
v_unificationHints_2472_ = lean_ctor_get_uint8(v___x_2466_, 5);
v_proofIrrelevance_2473_ = lean_ctor_get_uint8(v___x_2466_, 6);
v_assignSyntheticOpaque_2474_ = lean_ctor_get_uint8(v___x_2466_, 7);
v_offsetCnstrs_2475_ = lean_ctor_get_uint8(v___x_2466_, 8);
v_etaStruct_2476_ = lean_ctor_get_uint8(v___x_2466_, 10);
v_univApprox_2477_ = lean_ctor_get_uint8(v___x_2466_, 11);
v_iota_2478_ = lean_ctor_get_uint8(v___x_2466_, 12);
v_beta_2479_ = lean_ctor_get_uint8(v___x_2466_, 13);
v_proj_2480_ = lean_ctor_get_uint8(v___x_2466_, 14);
v_zeta_2481_ = lean_ctor_get_uint8(v___x_2466_, 15);
v_zetaDelta_2482_ = lean_ctor_get_uint8(v___x_2466_, 16);
v_zetaUnused_2483_ = lean_ctor_get_uint8(v___x_2466_, 17);
v_zetaHave_2484_ = lean_ctor_get_uint8(v___x_2466_, 18);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2486_ = v___x_2466_;
v_isShared_2487_ = v_isSharedCheck_2507_;
goto v_resetjp_2485_;
}
else
{
lean_dec(v___x_2466_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2507_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; uint8_t v___x_2489_; lean_object* v_config_2491_; 
v___x_2488_ = lean_array_fget_borrowed(v_params_2406_, v_a_2411_);
v___x_2489_ = 2;
if (v_isShared_2487_ == 0)
{
v_config_2491_ = v___x_2486_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 0, v_foApprox_2467_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 1, v_ctxApprox_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 2, v_quasiPatternApprox_2469_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 3, v_constApprox_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 4, v_isDefEqStuckEx_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 5, v_unificationHints_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 6, v_proofIrrelevance_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 7, v_assignSyntheticOpaque_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 8, v_offsetCnstrs_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 10, v_etaStruct_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 11, v_univApprox_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 12, v_iota_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 13, v_beta_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 14, v_proj_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 15, v_zeta_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 16, v_zetaDelta_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 17, v_zetaUnused_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2506_, 18, v_zetaHave_2484_);
v_config_2491_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
uint64_t v___x_2492_; uint64_t v___x_2493_; uint64_t v___x_2494_; uint64_t v___x_2495_; uint64_t v___x_2496_; uint64_t v_key_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_ctor_set_uint8(v_config_2491_, 9, v___x_2489_);
v___x_2492_ = l_Lean_Meta_Context_configKey(v___x_2465_);
lean_dec_ref(v___x_2465_);
v___x_2493_ = 2ULL;
v___x_2494_ = lean_uint64_shift_right(v___x_2492_, v___x_2493_);
v___x_2495_ = lean_uint64_shift_left(v___x_2494_, v___x_2493_);
v___x_2496_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2497_ = lean_uint64_lor(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2498_, 0, v_config_2491_);
lean_ctor_set_uint64(v___x_2498_, sizeof(void*)*1, v_key_2497_);
lean_inc(v_canUnfold_x3f_2456_);
lean_inc(v_synthPendingDepth_2455_);
lean_inc(v_defEqCtx_x3f_2454_);
lean_inc_ref(v_localInstances_2453_);
lean_inc_ref(v_lctx_2452_);
lean_inc(v_zetaDeltaSet_2451_);
v___x_2499_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v_zetaDeltaSet_2451_);
lean_ctor_set(v___x_2499_, 2, v_lctx_2452_);
lean_ctor_set(v___x_2499_, 3, v_localInstances_2453_);
lean_ctor_set(v___x_2499_, 4, v_defEqCtx_x3f_2454_);
lean_ctor_set(v___x_2499_, 5, v_synthPendingDepth_2455_);
lean_ctor_set(v___x_2499_, 6, v_canUnfold_x3f_2456_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*7, v_trackZetaDelta_2450_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*7 + 1, v_univApprox_2457_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2458_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*7 + 3, v_cacheInferType_2459_);
lean_inc_ref(v___x_2407_);
lean_inc(v___x_2488_);
v___x_2500_ = l_Lean_Meta_isExprDefEq(v___x_2488_, v___x_2407_, v___x_2499_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec_ref(v___x_2499_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; uint8_t v___x_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = lean_unbox(v_a_2501_);
lean_dec(v_a_2501_);
if (v___x_2502_ == 0)
{
v_a_2419_ = v_b_2412_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_st_ref_take(v_val_2404_);
lean_inc(v_a_2411_);
lean_inc(v_next_2409_);
v___x_2504_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2408_, v_next_2409_, v_next_2405_, v_a_2411_, v___x_2503_);
v___x_2505_ = lean_st_ref_set(v_val_2404_, v___x_2504_);
v_a_2419_ = v___x_2410_;
goto v___jp_2418_;
}
}
else
{
lean_dec(v_a_2411_);
lean_dec(v_next_2409_);
lean_dec_ref(v___x_2407_);
return v___x_2500_;
}
}
}
}
}
}
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_unsigned_to_nat(1u);
v___x_2421_ = lean_nat_add(v_a_2411_, v___x_2420_);
lean_dec(v_a_2411_);
v_a_2411_ = v___x_2421_;
v_b_2412_ = v_a_2419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_upperBound_2510_, lean_object* v_val_2511_, lean_object* v_next_2512_, lean_object* v_params_2513_, lean_object* v___x_2514_, lean_object* v_val_2515_, lean_object* v_next_2516_, lean_object* v___x_2517_, lean_object* v_a_2518_, lean_object* v_b_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
uint8_t v___x_44689__boxed_2525_; uint8_t v_b_boxed_2526_; lean_object* v_res_2527_; 
v___x_44689__boxed_2525_ = lean_unbox(v___x_2517_);
v_b_boxed_2526_ = lean_unbox(v_b_2519_);
v_res_2527_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_2510_, v_val_2511_, v_next_2512_, v_params_2513_, v___x_2514_, v_val_2515_, v_next_2516_, v___x_44689__boxed_2525_, v_a_2518_, v_b_boxed_2526_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v_val_2515_);
lean_dec_ref(v_params_2513_);
lean_dec(v_next_2512_);
lean_dec(v_val_2511_);
lean_dec(v_upperBound_2510_);
return v_res_2527_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2540_ = l_Lean_Name_append(v___x_2539_, v___x_2538_);
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
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
return v___x_2545_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
return v___x_2548_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2557_ = l_Lean_stringToMessageData(v___x_2556_);
return v___x_2557_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2560_ = l_Lean_stringToMessageData(v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2561_, lean_object* v_val_2562_, lean_object* v_upperBound_2563_, lean_object* v_args_2564_, lean_object* v_e_2565_, lean_object* v_next_2566_, lean_object* v_params_2567_, lean_object* v___x_2568_, uint8_t v___x_2569_, lean_object* v_a_2570_, lean_object* v_b_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_a_2578_; lean_object* v___y_2583_; uint8_t v___x_2602_; 
v___x_2602_ = lean_nat_dec_lt(v_a_2570_, v_upperBound_2563_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v_b_2571_);
return v___x_2603_;
}
else
{
lean_object* v___x_2604_; 
v___x_2604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2561_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref(v___x_2604_);
v___x_2606_ = lean_box(0);
v___x_2607_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2562_, v_a_2570_, v_a_2605_);
lean_dec(v_a_2605_);
if (v___x_2607_ == 0)
{
v_a_2578_ = v___x_2606_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2608_ = lean_array_get_size(v_args_2564_);
v___x_2609_ = lean_nat_dec_lt(v_a_2570_, v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v_options_2610_; lean_object* v_inheritedTraceOptions_2611_; uint8_t v_hasTrace_2612_; 
v_options_2610_ = lean_ctor_get(v___y_2574_, 2);
v_inheritedTraceOptions_2611_ = lean_ctor_get(v___y_2574_, 13);
v_hasTrace_2612_ = lean_ctor_get_uint8(v_options_2610_, sizeof(void*)*1);
if (v_hasTrace_2612_ == 0)
{
goto v___jp_2613_;
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2615_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2616_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2611_, v_options_2610_, v___x_2616_);
if (v___x_2617_ == 0)
{
goto v___jp_2613_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2618_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2562_);
v___x_2619_ = l_Nat_reprFast(v_val_2562_);
v___x_2620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
v___x_2621_ = l_Lean_MessageData_ofFormat(v___x_2620_);
v___x_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2618_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
lean_inc(v_a_2570_);
v___x_2625_ = l_Nat_reprFast(v_a_2570_);
v___x_2626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
v___x_2627_ = l_Lean_MessageData_ofFormat(v___x_2626_);
lean_inc_ref(v___x_2627_);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2624_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2628_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
lean_inc_ref(v_e_2565_);
v___x_2631_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2632_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v___x_2627_);
v___x_2636_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2615_, v___x_2635_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2638_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
lean_inc(v_a_2570_);
v___x_2638_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2561_, v_val_2562_, v_a_2570_, v___x_2606_, v_a_2637_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
v___y_2583_ = v___x_2638_;
goto v___jp_2582_;
}
else
{
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
return v___x_2636_;
}
}
}
v___jp_2613_:
{
lean_object* v___x_2614_; 
lean_inc(v_a_2570_);
v___x_2614_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2561_, v_val_2562_, v_a_2570_, v___x_2606_, v___x_2606_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
v___y_2583_ = v___x_2614_;
goto v___jp_2582_;
}
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2561_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v___x_2639_);
v___x_2641_ = lean_array_fget_borrowed(v_args_2564_, v_a_2570_);
v___x_2642_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2562_, v_a_2570_, v_next_2566_, v_a_2640_);
lean_dec(v_a_2640_);
if (lean_obj_tag(v___x_2642_) == 1)
{
lean_object* v_val_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2771_; 
v_val_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2771_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_val_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2771_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; uint8_t v_foApprox_2648_; uint8_t v_ctxApprox_2649_; uint8_t v_quasiPatternApprox_2650_; uint8_t v_constApprox_2651_; uint8_t v_isDefEqStuckEx_2652_; uint8_t v_unificationHints_2653_; uint8_t v_assignSyntheticOpaque_2654_; uint8_t v_offsetCnstrs_2655_; uint8_t v_transparency_2656_; uint8_t v_etaStruct_2657_; uint8_t v_univApprox_2658_; uint8_t v_iota_2659_; uint8_t v_beta_2660_; uint8_t v_proj_2661_; uint8_t v_zeta_2662_; uint8_t v_zetaDelta_2663_; uint8_t v_zetaUnused_2664_; uint8_t v_zetaHave_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2770_; 
v___x_2647_ = l_Lean_Meta_Context_config(v___y_2572_);
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
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2667_ = v___x_2647_;
v_isShared_2668_ = v_isSharedCheck_2770_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v___x_2647_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2770_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint8_t v_trackZetaDelta_2669_; lean_object* v_zetaDeltaSet_2670_; lean_object* v_lctx_2671_; lean_object* v_localInstances_2672_; lean_object* v_defEqCtx_x3f_2673_; lean_object* v_synthPendingDepth_2674_; lean_object* v_canUnfold_x3f_2675_; uint8_t v_univApprox_2676_; uint8_t v_inTypeClassResolution_2677_; uint8_t v_cacheInferType_2678_; uint8_t v___x_2679_; lean_object* v___x_2681_; 
v_trackZetaDelta_2669_ = lean_ctor_get_uint8(v___y_2572_, sizeof(void*)*7);
v_zetaDeltaSet_2670_ = lean_ctor_get(v___y_2572_, 1);
v_lctx_2671_ = lean_ctor_get(v___y_2572_, 2);
v_localInstances_2672_ = lean_ctor_get(v___y_2572_, 3);
v_defEqCtx_x3f_2673_ = lean_ctor_get(v___y_2572_, 4);
v_synthPendingDepth_2674_ = lean_ctor_get(v___y_2572_, 5);
v_canUnfold_x3f_2675_ = lean_ctor_get(v___y_2572_, 6);
v_univApprox_2676_ = lean_ctor_get_uint8(v___y_2572_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2677_ = lean_ctor_get_uint8(v___y_2572_, sizeof(void*)*7 + 2);
v_cacheInferType_2678_ = lean_ctor_get_uint8(v___y_2572_, sizeof(void*)*7 + 3);
v___x_2679_ = 0;
if (v_isShared_2668_ == 0)
{
v___x_2681_ = v___x_2667_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 0, v_foApprox_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 1, v_ctxApprox_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 2, v_quasiPatternApprox_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 3, v_constApprox_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 4, v_isDefEqStuckEx_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 5, v_unificationHints_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 7, v_assignSyntheticOpaque_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 8, v_offsetCnstrs_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 9, v_transparency_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 10, v_etaStruct_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 11, v_univApprox_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 12, v_iota_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 13, v_beta_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 14, v_proj_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 15, v_zeta_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 16, v_zetaDelta_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 17, v_zetaUnused_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2769_, 18, v_zetaHave_2665_);
v___x_2681_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
uint64_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v_foApprox_2686_; uint8_t v_ctxApprox_2687_; uint8_t v_quasiPatternApprox_2688_; uint8_t v_constApprox_2689_; uint8_t v_isDefEqStuckEx_2690_; uint8_t v_unificationHints_2691_; uint8_t v_proofIrrelevance_2692_; uint8_t v_assignSyntheticOpaque_2693_; uint8_t v_offsetCnstrs_2694_; uint8_t v_etaStruct_2695_; uint8_t v_univApprox_2696_; uint8_t v_iota_2697_; uint8_t v_beta_2698_; uint8_t v_proj_2699_; uint8_t v_zeta_2700_; uint8_t v_zetaDelta_2701_; uint8_t v_zetaUnused_2702_; uint8_t v_zetaHave_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2768_; 
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
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2705_ = v___x_2685_;
v_isShared_2706_ = v_isSharedCheck_2768_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v___x_2685_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2768_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; lean_object* v_config_2711_; 
v___x_2707_ = l_Lean_instInhabitedExpr;
v___x_2708_ = lean_array_get_borrowed(v___x_2707_, v_params_2567_, v_val_2643_);
lean_dec(v_val_2643_);
v___x_2709_ = 2;
if (v_isShared_2706_ == 0)
{
v_config_2711_ = v___x_2705_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 0, v_foApprox_2686_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 1, v_ctxApprox_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 2, v_quasiPatternApprox_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 3, v_constApprox_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 4, v_isDefEqStuckEx_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 5, v_unificationHints_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 6, v_proofIrrelevance_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 7, v_assignSyntheticOpaque_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 8, v_offsetCnstrs_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 10, v_etaStruct_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 11, v_univApprox_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 12, v_iota_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 13, v_beta_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 14, v_proj_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 15, v_zeta_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 16, v_zetaDelta_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 17, v_zetaUnused_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2767_, 18, v_zetaHave_2703_);
v_config_2711_ = v_reuseFailAlloc_2767_;
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
v___x_2720_ = l_Lean_Meta_isExprDefEq(v___x_2708_, v___x_2641_, v___x_2719_, v___y_2573_, v___y_2574_, v___y_2575_);
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
lean_object* v_options_2723_; lean_object* v_inheritedTraceOptions_2724_; uint8_t v_hasTrace_2725_; 
v_options_2723_ = lean_ctor_get(v___y_2574_, 2);
v_inheritedTraceOptions_2724_ = lean_ctor_get(v___y_2574_, 13);
v_hasTrace_2725_ = lean_ctor_get_uint8(v_options_2723_, sizeof(void*)*1);
if (v_hasTrace_2725_ == 0)
{
lean_del_object(v___x_2645_);
goto v___jp_2726_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2729_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2730_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2724_, v_options_2723_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_del_object(v___x_2645_);
goto v___jp_2726_;
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2731_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2562_);
v___x_2732_ = l_Nat_reprFast(v_val_2562_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 3);
lean_ctor_set(v___x_2645_, 0, v___x_2732_);
v___x_2734_ = v___x_2645_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2735_ = l_Lean_MessageData_ofFormat(v___x_2734_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2731_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
lean_inc(v_a_2570_);
v___x_2739_ = l_Nat_reprFast(v_a_2570_);
v___x_2740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
v___x_2741_ = l_Lean_MessageData_ofFormat(v___x_2740_);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2738_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
lean_inc_ref(v_e_2565_);
v___x_2745_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
lean_inc(v___x_2708_);
v___x_2749_ = l_Lean_MessageData_ofExpr(v___x_2708_);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
lean_inc(v___x_2641_);
v___x_2753_ = l_Lean_MessageData_ofExpr(v___x_2641_);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2728_, v___x_2754_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref(v___x_2755_);
lean_inc(v_a_2570_);
v___x_2757_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2561_, v_val_2562_, v_a_2570_, v___x_2606_, v_a_2756_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
v___y_2583_ = v___x_2757_;
goto v___jp_2582_;
}
else
{
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
return v___x_2755_;
}
}
}
}
v___jp_2726_:
{
lean_object* v___x_2727_; 
lean_inc(v_a_2570_);
v___x_2727_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2561_, v_val_2562_, v_a_2570_, v___x_2606_, v___x_2606_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
v___y_2583_ = v___x_2727_;
goto v___jp_2582_;
}
}
else
{
lean_del_object(v___x_2645_);
v_a_2578_ = v___x_2606_;
goto v___jp_2577_;
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_del_object(v___x_2645_);
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
v_a_2759_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2720_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2720_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
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
lean_object* v___x_2772_; uint8_t v___x_2773_; lean_object* v___x_2774_; 
lean_dec(v___x_2642_);
v___x_2772_ = lean_unsigned_to_nat(0u);
v___x_2773_ = 0;
lean_inc(v_a_2570_);
lean_inc(v___x_2641_);
v___x_2774_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v___x_2568_, v_val_2561_, v_next_2566_, v_params_2567_, v___x_2641_, v_val_2562_, v_a_2570_, v___x_2569_, v___x_2772_, v___x_2773_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; uint8_t v___x_2776_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref(v___x_2774_);
v___x_2776_ = lean_unbox(v_a_2775_);
lean_dec(v_a_2775_);
if (v___x_2776_ == 0)
{
lean_object* v_options_2777_; lean_object* v_inheritedTraceOptions_2778_; uint8_t v_hasTrace_2779_; 
v_options_2777_ = lean_ctor_get(v___y_2574_, 2);
v_inheritedTraceOptions_2778_ = lean_ctor_get(v___y_2574_, 13);
v_hasTrace_2779_ = lean_ctor_get_uint8(v_options_2777_, sizeof(void*)*1);
if (v_hasTrace_2779_ == 0)
{
goto v___jp_2780_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2783_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2784_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2778_, v_options_2777_, v___x_2783_);
if (v___x_2784_ == 0)
{
goto v___jp_2780_;
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2785_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2562_);
v___x_2786_ = l_Nat_reprFast(v_val_2562_);
v___x_2787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
v___x_2788_ = l_Lean_MessageData_ofFormat(v___x_2787_);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2785_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
lean_inc(v_a_2570_);
v___x_2792_ = l_Nat_reprFast(v_a_2570_);
v___x_2793_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
v___x_2794_ = l_Lean_MessageData_ofFormat(v___x_2793_);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2791_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
lean_inc_ref(v_e_2565_);
v___x_2798_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
lean_inc(v___x_2641_);
v___x_2802_ = l_Lean_MessageData_ofExpr(v___x_2641_);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2801_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2782_, v___x_2805_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref(v___x_2806_);
lean_inc(v_a_2570_);
v___x_2808_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2561_, v_val_2562_, v_a_2570_, v___x_2606_, v_a_2807_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
v___y_2583_ = v___x_2808_;
goto v___jp_2582_;
}
else
{
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
return v___x_2806_;
}
}
}
v___jp_2780_:
{
lean_object* v___x_2781_; 
lean_inc(v_a_2570_);
v___x_2781_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2561_, v_val_2562_, v_a_2570_, v___x_2606_, v___x_2606_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
v___y_2583_ = v___x_2781_;
goto v___jp_2582_;
}
}
else
{
v_a_2578_ = v___x_2606_;
goto v___jp_2577_;
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
v_a_2809_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2774_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2774_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
v_a_2817_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2639_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2639_);
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
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
v_a_2825_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2604_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2604_);
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
v___jp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = lean_unsigned_to_nat(1u);
v___x_2580_ = lean_nat_add(v_a_2570_, v___x_2579_);
lean_dec(v_a_2570_);
v_a_2570_ = v___x_2580_;
v_b_2571_ = v_a_2578_;
goto _start;
}
v___jp_2582_:
{
if (lean_obj_tag(v___y_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2593_; 
v_a_2584_ = lean_ctor_get(v___y_2583_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___y_2583_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2586_ = v___y_2583_;
v_isShared_2587_ = v_isSharedCheck_2593_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___y_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2593_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
if (lean_obj_tag(v_a_2584_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2590_; 
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
v_a_2588_ = lean_ctor_get(v_a_2584_, 0);
lean_inc(v_a_2588_);
lean_dec_ref(v_a_2584_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v_a_2588_);
v___x_2590_ = v___x_2586_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
else
{
lean_object* v_a_2592_; 
lean_del_object(v___x_2586_);
v_a_2592_ = lean_ctor_get(v_a_2584_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v_a_2584_);
v_a_2578_ = v_a_2592_;
goto v___jp_2577_;
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_a_2570_);
lean_dec_ref(v_e_2565_);
lean_dec(v_val_2562_);
v_a_2594_ = lean_ctor_get(v___y_2583_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___y_2583_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___y_2583_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___y_2583_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2833_, lean_object* v_val_2834_, lean_object* v_upperBound_2835_, lean_object* v_args_2836_, lean_object* v_e_2837_, lean_object* v_next_2838_, lean_object* v_params_2839_, lean_object* v___x_2840_, lean_object* v___x_2841_, lean_object* v_a_2842_, lean_object* v_b_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v___x_44926__boxed_2849_; lean_object* v_res_2850_; 
v___x_44926__boxed_2849_ = lean_unbox(v___x_2841_);
v_res_2850_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2833_, v_val_2834_, v_upperBound_2835_, v_args_2836_, v_e_2837_, v_next_2838_, v_params_2839_, v___x_2840_, v___x_44926__boxed_2849_, v_a_2842_, v_b_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___x_2840_);
lean_dec_ref(v_params_2839_);
lean_dec(v_next_2838_);
lean_dec_ref(v_args_2836_);
lean_dec(v_upperBound_2835_);
lean_dec(v_val_2833_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2853_, lean_object* v___x_2854_, lean_object* v_val_2855_, lean_object* v_e_2856_, lean_object* v_next_2857_, lean_object* v_params_2858_, lean_object* v___x_2859_, lean_object* v_x_2860_, lean_object* v_x_2861_, lean_object* v_x_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
if (lean_obj_tag(v_x_2860_) == 5)
{
lean_object* v_fn_2868_; lean_object* v_arg_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_fn_2868_ = lean_ctor_get(v_x_2860_, 0);
lean_inc_ref(v_fn_2868_);
v_arg_2869_ = lean_ctor_get(v_x_2860_, 1);
lean_inc_ref(v_arg_2869_);
lean_dec_ref(v_x_2860_);
v___x_2870_ = lean_array_set(v_x_2861_, v_x_2862_, v_arg_2869_);
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = lean_nat_sub(v_x_2862_, v___x_2871_);
lean_dec(v_x_2862_);
v_x_2860_ = v_fn_2868_;
v_x_2861_ = v___x_2870_;
v_x_2862_ = v___x_2872_;
goto _start;
}
else
{
uint8_t v___x_2874_; 
lean_dec(v_x_2862_);
v___x_2874_ = l_Lean_Expr_isConst(v_x_2860_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec_ref(v_x_2861_);
lean_dec_ref(v_x_2860_);
lean_dec_ref(v_e_2856_);
v___x_2875_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = l_Lean_Expr_constName_x21(v_x_2860_);
lean_dec_ref(v_x_2860_);
v___x_2878_ = lean_unsigned_to_nat(0u);
v___x_2879_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2877_, v_preDefs_2853_, v___x_2878_);
lean_dec(v___x_2877_);
if (lean_obj_tag(v___x_2879_) == 1)
{
lean_object* v_val_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_val_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_val_2880_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_array_get_borrowed(v___x_2878_, v___x_2854_, v_val_2880_);
v___x_2883_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2855_, v_val_2880_, v___x_2882_, v_x_2861_, v_e_2856_, v_next_2857_, v_params_2858_, v___x_2859_, v___x_2874_, v___x_2878_, v___x_2881_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec_ref(v_x_2861_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2891_; 
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; 
v_unused_2892_ = lean_ctor_get(v___x_2883_, 0);
lean_dec(v_unused_2892_);
v___x_2885_ = v___x_2883_;
v_isShared_2886_ = v_isSharedCheck_2891_;
goto v_resetjp_2884_;
}
else
{
lean_dec(v___x_2883_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2891_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2887_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v___x_2887_);
v___x_2889_ = v___x_2885_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
v_a_2893_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2883_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2883_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec(v___x_2879_);
lean_dec_ref(v_x_2861_);
lean_dec_ref(v_e_2856_);
v___x_2901_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2903_, lean_object* v___x_2904_, lean_object* v_val_2905_, lean_object* v_e_2906_, lean_object* v_next_2907_, lean_object* v_params_2908_, lean_object* v___x_2909_, lean_object* v_x_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2903_, v___x_2904_, v_val_2905_, v_e_2906_, v_next_2907_, v_params_2908_, v___x_2909_, v_x_2910_, v_x_2911_, v_x_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___x_2909_);
lean_dec_ref(v_params_2908_);
lean_dec(v_next_2907_);
lean_dec(v_val_2905_);
lean_dec_ref(v___x_2904_);
lean_dec_ref(v_preDefs_2903_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2919_, lean_object* v___x_2920_, lean_object* v_val_2921_, lean_object* v_a_2922_, lean_object* v_params_2923_, lean_object* v___x_2924_, lean_object* v_e_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_dummy_2931_; lean_object* v_nargs_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_dummy_2931_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2932_ = l_Lean_Expr_getAppNumArgs(v_e_2925_);
lean_inc(v_nargs_2932_);
v___x_2933_ = lean_mk_array(v_nargs_2932_, v_dummy_2931_);
v___x_2934_ = lean_unsigned_to_nat(1u);
v___x_2935_ = lean_nat_sub(v_nargs_2932_, v___x_2934_);
lean_dec(v_nargs_2932_);
lean_inc_ref(v_e_2925_);
v___x_2936_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2919_, v___x_2920_, v_val_2921_, v_e_2925_, v_a_2922_, v_params_2923_, v___x_2924_, v_e_2925_, v___x_2933_, v___x_2935_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2937_, lean_object* v___x_2938_, lean_object* v_val_2939_, lean_object* v_a_2940_, lean_object* v_params_2941_, lean_object* v___x_2942_, lean_object* v_e_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2937_, v___x_2938_, v_val_2939_, v_a_2940_, v_params_2941_, v___x_2942_, v_e_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___x_2942_);
lean_dec_ref(v_params_2941_);
lean_dec(v_a_2940_);
lean_dec(v_val_2939_);
lean_dec_ref(v___x_2938_);
lean_dec_ref(v_preDefs_2937_);
return v_res_2949_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2953_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2954_ = lean_unsigned_to_nat(6u);
v___x_2955_ = lean_unsigned_to_nat(201u);
v___x_2956_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2957_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2958_ = l_mkPanicMessageWithDecl(v___x_2957_, v___x_2956_, v___x_2955_, v___x_2954_, v___x_2953_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2959_, lean_object* v___x_2960_, lean_object* v_a_2961_, lean_object* v_preDefs_2962_, lean_object* v_val_2963_, lean_object* v___f_2964_, lean_object* v___x_2965_, lean_object* v_params_2966_, lean_object* v_body_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2973_ = lean_array_get_size(v_params_2966_);
v___x_2974_ = lean_array_get_borrowed(v___x_2959_, v___x_2960_, v_a_2961_);
v___x_2975_ = lean_nat_dec_eq(v___x_2973_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_dec_ref(v_body_2967_);
lean_dec_ref(v_params_2966_);
lean_dec_ref(v___f_2964_);
lean_dec(v_val_2963_);
lean_dec_ref(v_preDefs_2962_);
lean_dec(v_a_2961_);
lean_dec_ref(v___x_2960_);
v___x_2976_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2977_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2976_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
return v___x_2977_;
}
else
{
lean_object* v___f_2978_; uint8_t v___x_2979_; lean_object* v___x_2980_; 
v___f_2978_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_2978_, 0, v_preDefs_2962_);
lean_closure_set(v___f_2978_, 1, v___x_2960_);
lean_closure_set(v___f_2978_, 2, v_val_2963_);
lean_closure_set(v___f_2978_, 3, v_a_2961_);
lean_closure_set(v___f_2978_, 4, v_params_2966_);
lean_closure_set(v___f_2978_, 5, v___x_2973_);
v___x_2979_ = 0;
v___x_2980_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2967_, v___f_2978_, v___f_2964_, v___x_2979_, v___x_2975_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2980_, 0);
lean_dec(v_unused_2988_);
v___x_2982_ = v___x_2980_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v___x_2980_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_2965_);
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2965_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_a_2989_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2980_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2980_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2997_, lean_object* v___x_2998_, lean_object* v_a_2999_, lean_object* v_preDefs_3000_, lean_object* v_val_3001_, lean_object* v___f_3002_, lean_object* v___x_3003_, lean_object* v_params_3004_, lean_object* v_body_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2997_, v___x_2998_, v_a_2999_, v_preDefs_3000_, v_val_3001_, v___f_3002_, v___x_3003_, v_params_3004_, v_body_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___x_2997_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3018_, 0, v_e_3012_);
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v_preDefs_3028_, lean_object* v___x_3029_, lean_object* v_val_3030_, lean_object* v_upperBound_3031_, lean_object* v_a_3032_, lean_object* v_b_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
uint8_t v___x_3039_; 
v___x_3039_ = lean_nat_dec_lt(v_a_3032_, v_upperBound_3031_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; 
lean_dec(v_a_3032_);
lean_dec(v_val_3030_);
lean_dec_ref(v___x_3029_);
lean_dec_ref(v_preDefs_3028_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_b_3033_);
return v___x_3040_;
}
else
{
lean_object* v___x_3041_; lean_object* v_value_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___f_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; 
v___x_3041_ = lean_array_fget_borrowed(v_preDefs_3028_, v_a_3032_);
v_value_3042_ = lean_ctor_get(v___x_3041_, 7);
v___f_3043_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3044_ = lean_unsigned_to_nat(0u);
v___x_3045_ = lean_box(0);
lean_inc(v_val_3030_);
lean_inc_ref(v_preDefs_3028_);
lean_inc(v_a_3032_);
lean_inc_ref(v___x_3029_);
v___f_3046_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3046_, 0, v___x_3044_);
lean_closure_set(v___f_3046_, 1, v___x_3029_);
lean_closure_set(v___f_3046_, 2, v_a_3032_);
lean_closure_set(v___f_3046_, 3, v_preDefs_3028_);
lean_closure_set(v___f_3046_, 4, v_val_3030_);
lean_closure_set(v___f_3046_, 5, v___f_3043_);
lean_closure_set(v___f_3046_, 6, v___x_3045_);
v___x_3047_ = 0;
lean_inc_ref(v_value_3042_);
v___x_3048_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3042_, v___f_3046_, v___x_3047_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec_ref(v___x_3048_);
v___x_3049_ = lean_unsigned_to_nat(1u);
v___x_3050_ = lean_nat_add(v_a_3032_, v___x_3049_);
lean_dec(v_a_3032_);
v_a_3032_ = v___x_3050_;
v_b_3033_ = v___x_3045_;
goto _start;
}
else
{
lean_dec(v_a_3032_);
lean_dec(v_val_3030_);
lean_dec_ref(v___x_3029_);
lean_dec_ref(v_preDefs_3028_);
return v___x_3048_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v_preDefs_3052_, lean_object* v___x_3053_, lean_object* v_val_3054_, lean_object* v_upperBound_3055_, lean_object* v_a_3056_, lean_object* v_b_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3052_, v___x_3053_, v_val_3054_, v_upperBound_3055_, v_a_3056_, v_b_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v_upperBound_3055_);
return v_res_3063_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3066_ = l_Lean_stringToMessageData(v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
size_t v_sz_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
v_sz_3073_ = lean_array_size(v_preDefs_3067_);
v___x_3074_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3067_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3073_, v___x_3074_, v_preDefs_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; size_t v_sz_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc_n(v_a_3076_, 2);
lean_dec_ref(v___x_3075_);
v_sz_3077_ = lean_array_size(v_a_3076_);
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3077_, v___x_3074_, v_a_3076_);
v___x_3079_ = l_Lean_Elab_FixedParams_Info_init(v_a_3076_);
v___x_3080_ = lean_st_mk_ref(v___x_3079_);
v___x_3081_ = lean_st_ref_take(v___x_3080_);
v___x_3082_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3081_);
v___x_3083_ = lean_st_ref_set(v___x_3080_, v___x_3082_);
v___x_3084_ = lean_array_get_size(v_preDefs_3067_);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_box(0);
lean_inc(v___x_3080_);
v___x_3087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3067_, v___x_3078_, v___x_3080_, v___x_3084_, v___x_3085_, v___x_3086_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3126_; 
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3127_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3126_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3126_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v_options_3092_; uint8_t v_hasTrace_3093_; 
v___x_3091_ = lean_st_ref_get(v___x_3080_);
lean_dec(v___x_3080_);
v_options_3092_ = lean_ctor_get(v_a_3070_, 2);
v_hasTrace_3093_ = lean_ctor_get_uint8(v_options_3092_, sizeof(void*)*1);
if (v_hasTrace_3093_ == 0)
{
lean_object* v___x_3095_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3095_ = v___x_3089_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3091_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v_inheritedTraceOptions_3097_ = lean_ctor_get(v_a_3070_, 13);
v___x_3098_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3099_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3100_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3097_, v_options_3092_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3102_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3102_ = v___x_3089_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3091_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_del_object(v___x_3089_);
v___x_3104_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3091_);
v___x_3105_ = l_Lean_Elab_FixedParams_Info_format(v___x_3091_);
v___x_3106_ = l_Std_Format_indentD(v___x_3105_);
v___x_3107_ = l_Lean_MessageData_ofFormat(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3104_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3098_, v___x_3108_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v___x_3109_, 0);
lean_dec(v_unused_3117_);
v___x_3111_ = v___x_3109_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_dec(v___x_3109_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3091_);
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3091_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v___x_3091_);
v_a_3118_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3109_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3109_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_dec(v___x_3080_);
v_a_3128_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3087_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3087_);
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
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v_preDefs_3067_);
v_a_3136_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3075_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3075_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_upperBound_3151_, lean_object* v_val_3152_, lean_object* v_next_3153_, lean_object* v_params_3154_, lean_object* v___x_3155_, lean_object* v_val_3156_, lean_object* v_next_3157_, uint8_t v___x_3158_, lean_object* v_inst_3159_, lean_object* v_R_3160_, lean_object* v_a_3161_, uint8_t v_b_3162_, lean_object* v_c_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_3151_, v_val_3152_, v_next_3153_, v_params_3154_, v___x_3155_, v_val_3156_, v_next_3157_, v___x_3158_, v_a_3161_, v_b_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3170_ = _args[0];
lean_object* v_val_3171_ = _args[1];
lean_object* v_next_3172_ = _args[2];
lean_object* v_params_3173_ = _args[3];
lean_object* v___x_3174_ = _args[4];
lean_object* v_val_3175_ = _args[5];
lean_object* v_next_3176_ = _args[6];
lean_object* v___x_3177_ = _args[7];
lean_object* v_inst_3178_ = _args[8];
lean_object* v_R_3179_ = _args[9];
lean_object* v_a_3180_ = _args[10];
lean_object* v_b_3181_ = _args[11];
lean_object* v_c_3182_ = _args[12];
lean_object* v___y_3183_ = _args[13];
lean_object* v___y_3184_ = _args[14];
lean_object* v___y_3185_ = _args[15];
lean_object* v___y_3186_ = _args[16];
lean_object* v___y_3187_ = _args[17];
_start:
{
uint8_t v___x_45875__boxed_3188_; uint8_t v_b_boxed_3189_; lean_object* v_res_3190_; 
v___x_45875__boxed_3188_ = lean_unbox(v___x_3177_);
v_b_boxed_3189_ = lean_unbox(v_b_3181_);
v_res_3190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_upperBound_3170_, v_val_3171_, v_next_3172_, v_params_3173_, v___x_3174_, v_val_3175_, v_next_3176_, v___x_45875__boxed_3188_, v_inst_3178_, v_R_3179_, v_a_3180_, v_b_boxed_3189_, v_c_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v_val_3175_);
lean_dec_ref(v_params_3173_);
lean_dec(v_next_3172_);
lean_dec(v_val_3171_);
lean_dec(v_upperBound_3170_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3191_, lean_object* v_val_3192_, lean_object* v_upperBound_3193_, lean_object* v_args_3194_, lean_object* v_e_3195_, lean_object* v_next_3196_, lean_object* v_params_3197_, lean_object* v___x_3198_, uint8_t v___x_3199_, lean_object* v_inst_3200_, lean_object* v_R_3201_, lean_object* v_a_3202_, lean_object* v_b_3203_, lean_object* v_c_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3191_, v_val_3192_, v_upperBound_3193_, v_args_3194_, v_e_3195_, v_next_3196_, v_params_3197_, v___x_3198_, v___x_3199_, v_a_3202_, v_b_3203_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3211_ = _args[0];
lean_object* v_val_3212_ = _args[1];
lean_object* v_upperBound_3213_ = _args[2];
lean_object* v_args_3214_ = _args[3];
lean_object* v_e_3215_ = _args[4];
lean_object* v_next_3216_ = _args[5];
lean_object* v_params_3217_ = _args[6];
lean_object* v___x_3218_ = _args[7];
lean_object* v___x_3219_ = _args[8];
lean_object* v_inst_3220_ = _args[9];
lean_object* v_R_3221_ = _args[10];
lean_object* v_a_3222_ = _args[11];
lean_object* v_b_3223_ = _args[12];
lean_object* v_c_3224_ = _args[13];
lean_object* v___y_3225_ = _args[14];
lean_object* v___y_3226_ = _args[15];
lean_object* v___y_3227_ = _args[16];
lean_object* v___y_3228_ = _args[17];
lean_object* v___y_3229_ = _args[18];
_start:
{
uint8_t v___x_45910__boxed_3230_; lean_object* v_res_3231_; 
v___x_45910__boxed_3230_ = lean_unbox(v___x_3219_);
v_res_3231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3211_, v_val_3212_, v_upperBound_3213_, v_args_3214_, v_e_3215_, v_next_3216_, v_params_3217_, v___x_3218_, v___x_45910__boxed_3230_, v_inst_3220_, v_R_3221_, v_a_3222_, v_b_3223_, v_c_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___x_3218_);
lean_dec_ref(v_params_3217_);
lean_dec(v_next_3216_);
lean_dec_ref(v_args_3214_);
lean_dec(v_upperBound_3213_);
lean_dec(v_val_3211_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v_preDefs_3232_, lean_object* v___x_3233_, lean_object* v_val_3234_, lean_object* v_upperBound_3235_, lean_object* v_inst_3236_, lean_object* v_R_3237_, lean_object* v_a_3238_, lean_object* v_b_3239_, lean_object* v_c_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3232_, v___x_3233_, v_val_3234_, v_upperBound_3235_, v_a_3238_, v_b_3239_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v_preDefs_3247_, lean_object* v___x_3248_, lean_object* v_val_3249_, lean_object* v_upperBound_3250_, lean_object* v_inst_3251_, lean_object* v_R_3252_, lean_object* v_a_3253_, lean_object* v_b_3254_, lean_object* v_c_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v_preDefs_3247_, v___x_3248_, v_val_3249_, v_upperBound_3250_, v_inst_3251_, v_R_3252_, v_a_3253_, v_b_3254_, v_c_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v_upperBound_3250_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3262_, lean_object* v___x_3263_, lean_object* v_pre_3264_, lean_object* v_post_3265_, uint8_t v_usedLetOnly_3266_, uint8_t v_skipConstInApp_3267_, uint8_t v_skipInstances_3268_, lean_object* v___x_3269_, lean_object* v_inst_3270_, lean_object* v_R_3271_, lean_object* v_a_3272_, lean_object* v_b_3273_, lean_object* v_c_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3262_, v___x_3263_, v_pre_3264_, v_post_3265_, v_usedLetOnly_3266_, v_skipConstInApp_3267_, v_skipInstances_3268_, v_a_3272_, v_b_3273_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3282_ = _args[0];
lean_object* v___x_3283_ = _args[1];
lean_object* v_pre_3284_ = _args[2];
lean_object* v_post_3285_ = _args[3];
lean_object* v_usedLetOnly_3286_ = _args[4];
lean_object* v_skipConstInApp_3287_ = _args[5];
lean_object* v_skipInstances_3288_ = _args[6];
lean_object* v___x_3289_ = _args[7];
lean_object* v_inst_3290_ = _args[8];
lean_object* v_R_3291_ = _args[9];
lean_object* v_a_3292_ = _args[10];
lean_object* v_b_3293_ = _args[11];
lean_object* v_c_3294_ = _args[12];
lean_object* v___y_3295_ = _args[13];
lean_object* v___y_3296_ = _args[14];
lean_object* v___y_3297_ = _args[15];
lean_object* v___y_3298_ = _args[16];
lean_object* v___y_3299_ = _args[17];
lean_object* v___y_3300_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3301_; uint8_t v_skipConstInApp_boxed_3302_; uint8_t v_skipInstances_boxed_3303_; lean_object* v_res_3304_; 
v_usedLetOnly_boxed_3301_ = lean_unbox(v_usedLetOnly_3286_);
v_skipConstInApp_boxed_3302_ = lean_unbox(v_skipConstInApp_3287_);
v_skipInstances_boxed_3303_ = lean_unbox(v_skipInstances_3288_);
v_res_3304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3282_, v___x_3283_, v_pre_3284_, v_post_3285_, v_usedLetOnly_boxed_3301_, v_skipConstInApp_boxed_3302_, v_skipInstances_boxed_3303_, v___x_3289_, v_inst_3290_, v_R_3291_, v_a_3292_, v_b_3293_, v_c_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___x_3289_);
lean_dec_ref(v___x_3283_);
lean_dec(v_upperBound_3282_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3305_, lean_object* v_m_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3306_, v_a_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3309_, lean_object* v_m_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3309_, v_m_3310_, v_a_3311_);
lean_dec_ref(v_a_3311_);
lean_dec_ref(v_m_3310_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3313_, lean_object* v_name_3314_, uint8_t v_bi_3315_, lean_object* v_type_3316_, lean_object* v_k_3317_, uint8_t v_kind_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3314_, v_bi_3315_, v_type_3316_, v_k_3317_, v_kind_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3326_, lean_object* v_name_3327_, lean_object* v_bi_3328_, lean_object* v_type_3329_, lean_object* v_k_3330_, lean_object* v_kind_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
uint8_t v_bi_boxed_3338_; uint8_t v_kind_boxed_3339_; lean_object* v_res_3340_; 
v_bi_boxed_3338_ = lean_unbox(v_bi_3328_);
v_kind_boxed_3339_ = lean_unbox(v_kind_3331_);
v_res_3340_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3326_, v_name_3327_, v_bi_boxed_3338_, v_type_3329_, v_k_3330_, v_kind_boxed_3339_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3341_, lean_object* v_name_3342_, lean_object* v_type_3343_, lean_object* v_val_3344_, lean_object* v_k_3345_, uint8_t v_nondep_3346_, uint8_t v_kind_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3342_, v_type_3343_, v_val_3344_, v_k_3345_, v_nondep_3346_, v_kind_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3355_, lean_object* v_name_3356_, lean_object* v_type_3357_, lean_object* v_val_3358_, lean_object* v_k_3359_, lean_object* v_nondep_3360_, lean_object* v_kind_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
uint8_t v_nondep_boxed_3368_; uint8_t v_kind_boxed_3369_; lean_object* v_res_3370_; 
v_nondep_boxed_3368_ = lean_unbox(v_nondep_3360_);
v_kind_boxed_3369_ = lean_unbox(v_kind_3361_);
v_res_3370_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3355_, v_name_3356_, v_type_3357_, v_val_3358_, v_k_3359_, v_nondep_boxed_3368_, v_kind_boxed_3369_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3371_, lean_object* v_ref_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3372_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3379_, lean_object* v_ref_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3379_, v_ref_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3387_, lean_object* v_x_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3396_, lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3396_, v_x_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3405_, lean_object* v_m_3406_, lean_object* v_a_3407_, lean_object* v_b_3408_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3406_, v_a_3407_, v_b_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3410_, lean_object* v_a_3411_, lean_object* v_x_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3411_, v_x_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3414_, lean_object* v_a_3415_, lean_object* v_x_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3414_, v_a_3415_, v_x_3416_);
lean_dec(v_x_3416_);
lean_dec_ref(v_a_3415_);
return v_res_3417_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3418_, lean_object* v_a_3419_, lean_object* v_x_3420_){
_start:
{
uint8_t v___x_3421_; 
v___x_3421_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3419_, v_x_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3422_, lean_object* v_a_3423_, lean_object* v_x_3424_){
_start:
{
uint8_t v_res_3425_; lean_object* v_r_3426_; 
v_res_3425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3422_, v_a_3423_, v_x_3424_);
lean_dec(v_x_3424_);
lean_dec_ref(v_a_3423_);
v_r_3426_ = lean_box(v_res_3425_);
return v_r_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3427_, lean_object* v_data_3428_){
_start:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3430_, lean_object* v_a_3431_, lean_object* v_b_3432_, lean_object* v_x_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3431_, v_b_3432_, v_x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3435_, lean_object* v_i_3436_, lean_object* v_source_3437_, lean_object* v_target_3438_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3436_, v_source_3437_, v_target_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3440_, lean_object* v_x_3441_, lean_object* v_x_3442_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3441_, v_x_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3457_, lean_object* v_x_3458_){
_start:
{
if (lean_obj_tag(v_x_3457_) == 0)
{
lean_object* v___x_3459_; 
v___x_3459_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3459_;
}
else
{
lean_object* v_val_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3471_; 
v_val_3460_ = lean_ctor_get(v_x_3457_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_x_3457_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3462_ = v_x_3457_;
v_isShared_3463_ = v_isSharedCheck_3471_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_val_3460_);
lean_dec(v_x_3457_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3471_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3464_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3465_ = l_Nat_reprFast(v_val_3460_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 3);
lean_ctor_set(v___x_3462_, 0, v___x_3465_);
v___x_3467_ = v___x_3462_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3464_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = l_Repr_addAppParen(v___x_3468_, v_x_3458_);
return v___x_3469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3472_, lean_object* v_x_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3472_, v_x_3473_);
lean_dec(v_x_3473_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3475_, lean_object* v_x_3476_, lean_object* v_x_3477_){
_start:
{
if (lean_obj_tag(v_x_3477_) == 0)
{
lean_dec(v_x_3475_);
return v_x_3476_;
}
else
{
lean_object* v_head_3478_; lean_object* v_tail_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3490_; 
v_head_3478_ = lean_ctor_get(v_x_3477_, 0);
v_tail_3479_ = lean_ctor_get(v_x_3477_, 1);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_x_3477_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3481_ = v_x_3477_;
v_isShared_3482_ = v_isSharedCheck_3490_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_tail_3479_);
lean_inc(v_head_3478_);
lean_dec(v_x_3477_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3490_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
lean_inc(v_x_3475_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set_tag(v___x_3481_, 5);
lean_ctor_set(v___x_3481_, 1, v_x_3475_);
lean_ctor_set(v___x_3481_, 0, v_x_3476_);
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_x_3476_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_x_3475_);
v___x_3484_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3485_ = lean_unsigned_to_nat(0u);
v___x_3486_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3478_, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3484_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v_x_3476_ = v___x_3487_;
v_x_3477_ = v_tail_3479_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3491_, lean_object* v_x_3492_, lean_object* v_x_3493_){
_start:
{
if (lean_obj_tag(v_x_3493_) == 0)
{
lean_dec(v_x_3491_);
return v_x_3492_;
}
else
{
lean_object* v_head_3494_; lean_object* v_tail_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3506_; 
v_head_3494_ = lean_ctor_get(v_x_3493_, 0);
v_tail_3495_ = lean_ctor_get(v_x_3493_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_x_3493_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3497_ = v_x_3493_;
v_isShared_3498_ = v_isSharedCheck_3506_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_tail_3495_);
lean_inc(v_head_3494_);
lean_dec(v_x_3493_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3506_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
lean_inc(v_x_3491_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set_tag(v___x_3497_, 5);
lean_ctor_set(v___x_3497_, 1, v_x_3491_);
lean_ctor_set(v___x_3497_, 0, v_x_3492_);
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_x_3492_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_x_3491_);
v___x_3500_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3501_ = lean_unsigned_to_nat(0u);
v___x_3502_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3494_, v___x_3501_);
v___x_3503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3500_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3491_, v___x_3503_, v_tail_3495_);
return v___x_3504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3507_){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = lean_unsigned_to_nat(0u);
v___x_3509_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3507_, v___x_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3510_, lean_object* v_x_3511_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 0)
{
lean_object* v___x_3512_; 
lean_dec(v_x_3511_);
v___x_3512_ = lean_box(0);
return v___x_3512_;
}
else
{
lean_object* v_tail_3513_; 
v_tail_3513_ = lean_ctor_get(v_x_3510_, 1);
if (lean_obj_tag(v_tail_3513_) == 0)
{
lean_object* v_head_3514_; lean_object* v___x_3515_; 
lean_dec(v_x_3511_);
v_head_3514_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_head_3514_);
lean_dec_ref(v_x_3510_);
v___x_3515_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3514_);
return v___x_3515_;
}
else
{
lean_object* v_head_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
lean_inc(v_tail_3513_);
v_head_3516_ = lean_ctor_get(v_x_3510_, 0);
lean_inc(v_head_3516_);
lean_dec_ref(v_x_3510_);
v___x_3517_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3516_);
v___x_3518_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3511_, v___x_3517_, v_tail_3513_);
return v___x_3518_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3527_ = lean_string_length(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3529_ = lean_nat_to_int(v___x_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3535_){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v___x_3536_ = lean_array_get_size(v_xs_3535_);
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = lean_nat_dec_eq(v___x_3536_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3539_ = lean_array_to_list(v_xs_3535_);
v___x_3540_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3541_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3539_, v___x_3540_);
v___x_3542_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3543_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v___x_3541_);
v___x_3545_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3542_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = l_Std_Format_fill(v___x_3547_);
return v___x_3548_;
}
else
{
lean_object* v___x_3549_; 
lean_dec_ref(v_xs_3535_);
v___x_3549_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3549_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_){
_start:
{
if (lean_obj_tag(v_x_3552_) == 0)
{
lean_dec(v_x_3550_);
return v_x_3551_;
}
else
{
lean_object* v_head_3553_; lean_object* v_tail_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3564_; 
v_head_3553_ = lean_ctor_get(v_x_3552_, 0);
v_tail_3554_ = lean_ctor_get(v_x_3552_, 1);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_x_3552_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3556_ = v_x_3552_;
v_isShared_3557_ = v_isSharedCheck_3564_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_tail_3554_);
lean_inc(v_head_3553_);
lean_dec(v_x_3552_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3564_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
lean_inc(v_x_3550_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set_tag(v___x_3556_, 5);
lean_ctor_set(v___x_3556_, 1, v_x_3550_);
lean_ctor_set(v___x_3556_, 0, v_x_3551_);
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_x_3551_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_x_3550_);
v___x_3559_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3553_);
v___x_3561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3559_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v_x_3551_ = v___x_3561_;
v_x_3552_ = v_tail_3554_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3565_, lean_object* v_x_3566_){
_start:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_object* v___x_3567_; 
lean_dec(v_x_3566_);
v___x_3567_ = lean_box(0);
return v___x_3567_;
}
else
{
lean_object* v_tail_3568_; 
v_tail_3568_ = lean_ctor_get(v_x_3565_, 1);
if (lean_obj_tag(v_tail_3568_) == 0)
{
lean_object* v_head_3569_; lean_object* v___x_3570_; 
lean_dec(v_x_3566_);
v_head_3569_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_head_3569_);
lean_dec_ref(v_x_3565_);
v___x_3570_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3569_);
return v___x_3570_;
}
else
{
lean_object* v_head_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_inc(v_tail_3568_);
v_head_3571_ = lean_ctor_get(v_x_3565_, 0);
lean_inc(v_head_3571_);
lean_dec_ref(v_x_3565_);
v___x_3572_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3571_);
v___x_3573_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3566_, v___x_3572_, v_tail_3568_);
return v___x_3573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3574_){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v___x_3575_ = lean_array_get_size(v_xs_3574_);
v___x_3576_ = lean_unsigned_to_nat(0u);
v___x_3577_ = lean_nat_dec_eq(v___x_3575_, v___x_3576_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3578_ = lean_array_to_list(v_xs_3574_);
v___x_3579_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3580_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3578_, v___x_3579_);
v___x_3581_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3582_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
lean_ctor_set(v___x_3583_, 1, v___x_3580_);
v___x_3584_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3583_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3581_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = l_Std_Format_fill(v___x_3586_);
return v___x_3587_;
}
else
{
lean_object* v___x_3588_; 
lean_dec_ref(v_xs_3574_);
v___x_3588_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3588_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_){
_start:
{
if (lean_obj_tag(v_x_3591_) == 0)
{
lean_dec(v_x_3589_);
return v_x_3590_;
}
else
{
lean_object* v_head_3592_; lean_object* v_tail_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3604_; 
v_head_3592_ = lean_ctor_get(v_x_3591_, 0);
v_tail_3593_ = lean_ctor_get(v_x_3591_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_x_3591_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3595_ = v_x_3591_;
v_isShared_3596_ = v_isSharedCheck_3604_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_tail_3593_);
lean_inc(v_head_3592_);
lean_dec(v_x_3591_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3604_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
lean_inc(v_x_3589_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set_tag(v___x_3595_, 5);
lean_ctor_set(v___x_3595_, 1, v_x_3589_);
lean_ctor_set(v___x_3595_, 0, v_x_3590_);
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_x_3590_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_x_3589_);
v___x_3598_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3599_ = l_Nat_reprFast(v_head_3592_);
v___x_3600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
v___x_3601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3598_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v_x_3590_ = v___x_3601_;
v_x_3591_ = v_tail_3593_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3605_, lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
if (lean_obj_tag(v_x_3607_) == 0)
{
lean_dec(v_x_3605_);
return v_x_3606_;
}
else
{
lean_object* v_head_3608_; lean_object* v_tail_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3620_; 
v_head_3608_ = lean_ctor_get(v_x_3607_, 0);
v_tail_3609_ = lean_ctor_get(v_x_3607_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_x_3607_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3611_ = v_x_3607_;
v_isShared_3612_ = v_isSharedCheck_3620_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_tail_3609_);
lean_inc(v_head_3608_);
lean_dec(v_x_3607_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3620_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
lean_inc(v_x_3605_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 5);
lean_ctor_set(v___x_3611_, 1, v_x_3605_);
lean_ctor_set(v___x_3611_, 0, v_x_3606_);
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_x_3606_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_x_3605_);
v___x_3614_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3615_ = l_Nat_reprFast(v_head_3608_);
v___x_3616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3614_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3605_, v___x_3617_, v_tail_3609_);
return v___x_3618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3621_){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = l_Nat_reprFast(v___y_3621_);
v___x_3623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3624_, lean_object* v_x_3625_){
_start:
{
if (lean_obj_tag(v_x_3624_) == 0)
{
lean_object* v___x_3626_; 
lean_dec(v_x_3625_);
v___x_3626_ = lean_box(0);
return v___x_3626_;
}
else
{
lean_object* v_tail_3627_; 
v_tail_3627_ = lean_ctor_get(v_x_3624_, 1);
if (lean_obj_tag(v_tail_3627_) == 0)
{
lean_object* v_head_3628_; lean_object* v___x_3629_; 
lean_dec(v_x_3625_);
v_head_3628_ = lean_ctor_get(v_x_3624_, 0);
lean_inc(v_head_3628_);
lean_dec_ref(v_x_3624_);
v___x_3629_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3628_);
return v___x_3629_;
}
else
{
lean_object* v_head_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_inc(v_tail_3627_);
v_head_3630_ = lean_ctor_get(v_x_3624_, 0);
lean_inc(v_head_3630_);
lean_dec_ref(v_x_3624_);
v___x_3631_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3630_);
v___x_3632_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3625_, v___x_3631_, v_tail_3627_);
return v___x_3632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3633_){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v___x_3634_ = lean_array_get_size(v_xs_3633_);
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_nat_dec_eq(v___x_3634_, v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3637_ = lean_array_to_list(v_xs_3633_);
v___x_3638_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3639_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3637_, v___x_3638_);
v___x_3640_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3641_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v___x_3639_);
v___x_3643_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3640_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = l_Std_Format_fill(v___x_3645_);
return v___x_3646_;
}
else
{
lean_object* v___x_3647_; 
lean_dec_ref(v_xs_3633_);
v___x_3647_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3647_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3648_, lean_object* v_x_3649_, lean_object* v_x_3650_){
_start:
{
if (lean_obj_tag(v_x_3650_) == 0)
{
lean_dec(v_x_3648_);
return v_x_3649_;
}
else
{
lean_object* v_head_3651_; lean_object* v_tail_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3662_; 
v_head_3651_ = lean_ctor_get(v_x_3650_, 0);
v_tail_3652_ = lean_ctor_get(v_x_3650_, 1);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_x_3650_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3654_ = v_x_3650_;
v_isShared_3655_ = v_isSharedCheck_3662_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_tail_3652_);
lean_inc(v_head_3651_);
lean_dec(v_x_3650_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3662_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
lean_inc(v_x_3648_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 5);
lean_ctor_set(v___x_3654_, 1, v_x_3648_);
lean_ctor_set(v___x_3654_, 0, v_x_3649_);
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_x_3649_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_x_3648_);
v___x_3657_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3651_);
v___x_3659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v_x_3649_ = v___x_3659_;
v_x_3650_ = v_tail_3652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3663_, lean_object* v_x_3664_){
_start:
{
if (lean_obj_tag(v_x_3663_) == 0)
{
lean_object* v___x_3665_; 
lean_dec(v_x_3664_);
v___x_3665_ = lean_box(0);
return v___x_3665_;
}
else
{
lean_object* v_tail_3666_; 
v_tail_3666_ = lean_ctor_get(v_x_3663_, 1);
if (lean_obj_tag(v_tail_3666_) == 0)
{
lean_object* v_head_3667_; lean_object* v___x_3668_; 
lean_dec(v_x_3664_);
v_head_3667_ = lean_ctor_get(v_x_3663_, 0);
lean_inc(v_head_3667_);
lean_dec_ref(v_x_3663_);
v___x_3668_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3667_);
return v___x_3668_;
}
else
{
lean_object* v_head_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_inc(v_tail_3666_);
v_head_3669_ = lean_ctor_get(v_x_3663_, 0);
lean_inc(v_head_3669_);
lean_dec_ref(v_x_3663_);
v___x_3670_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3669_);
v___x_3671_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3664_, v___x_3670_, v_tail_3666_);
return v___x_3671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3672_){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; 
v___x_3673_ = lean_array_get_size(v_xs_3672_);
v___x_3674_ = lean_unsigned_to_nat(0u);
v___x_3675_ = lean_nat_dec_eq(v___x_3673_, v___x_3674_);
if (v___x_3675_ == 0)
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3676_ = lean_array_to_list(v_xs_3672_);
v___x_3677_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3678_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3676_, v___x_3677_);
v___x_3679_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3680_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v___x_3678_);
v___x_3682_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3679_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = l_Std_Format_fill(v___x_3684_);
return v___x_3685_;
}
else
{
lean_object* v___x_3686_; 
lean_dec_ref(v_xs_3672_);
v___x_3686_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3686_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3687_, lean_object* v_x_3688_, lean_object* v_x_3689_){
_start:
{
if (lean_obj_tag(v_x_3689_) == 0)
{
lean_dec(v_x_3687_);
return v_x_3688_;
}
else
{
lean_object* v_head_3690_; lean_object* v_tail_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3701_; 
v_head_3690_ = lean_ctor_get(v_x_3689_, 0);
v_tail_3691_ = lean_ctor_get(v_x_3689_, 1);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_x_3689_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3693_ = v_x_3689_;
v_isShared_3694_ = v_isSharedCheck_3701_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_tail_3691_);
lean_inc(v_head_3690_);
lean_dec(v_x_3689_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3701_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
lean_inc(v_x_3687_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set_tag(v___x_3693_, 5);
lean_ctor_set(v___x_3693_, 1, v_x_3687_);
lean_ctor_set(v___x_3693_, 0, v_x_3688_);
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_x_3688_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_x_3687_);
v___x_3696_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3690_);
v___x_3698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3696_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v_x_3688_ = v___x_3698_;
v_x_3689_ = v_tail_3691_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3702_, lean_object* v_x_3703_){
_start:
{
if (lean_obj_tag(v_x_3702_) == 0)
{
lean_object* v___x_3704_; 
lean_dec(v_x_3703_);
v___x_3704_ = lean_box(0);
return v___x_3704_;
}
else
{
lean_object* v_tail_3705_; 
v_tail_3705_ = lean_ctor_get(v_x_3702_, 1);
if (lean_obj_tag(v_tail_3705_) == 0)
{
lean_object* v_head_3706_; lean_object* v___x_3707_; 
lean_dec(v_x_3703_);
v_head_3706_ = lean_ctor_get(v_x_3702_, 0);
lean_inc(v_head_3706_);
lean_dec_ref(v_x_3702_);
v___x_3707_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3706_);
return v___x_3707_;
}
else
{
lean_object* v_head_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_inc(v_tail_3705_);
v_head_3708_ = lean_ctor_get(v_x_3702_, 0);
lean_inc(v_head_3708_);
lean_dec_ref(v_x_3702_);
v___x_3709_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3708_);
v___x_3710_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3703_, v___x_3709_, v_tail_3705_);
return v___x_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3711_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v___x_3712_ = lean_array_get_size(v_xs_3711_);
v___x_3713_ = lean_unsigned_to_nat(0u);
v___x_3714_ = lean_nat_dec_eq(v___x_3712_, v___x_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3715_ = lean_array_to_list(v_xs_3711_);
v___x_3716_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3717_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3715_, v___x_3716_);
v___x_3718_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3719_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
lean_ctor_set(v___x_3720_, 1, v___x_3717_);
v___x_3721_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3718_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = l_Std_Format_fill(v___x_3723_);
return v___x_3724_;
}
else
{
lean_object* v___x_3725_; 
lean_dec_ref(v_xs_3711_);
v___x_3725_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3725_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_unsigned_to_nat(12u);
v___x_3740_ = lean_nat_to_int(v___x_3739_);
return v___x_3740_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_unsigned_to_nat(9u);
v___x_3745_ = lean_nat_to_int(v___x_3744_);
return v___x_3745_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = lean_unsigned_to_nat(11u);
v___x_3750_ = lean_nat_to_int(v___x_3749_);
return v___x_3750_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3753_ = lean_string_length(v___x_3752_);
return v___x_3753_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3755_ = lean_nat_to_int(v___x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3760_){
_start:
{
lean_object* v_numFixed_3761_; lean_object* v_perms_3762_; lean_object* v_revDeps_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v_numFixed_3761_ = lean_ctor_get(v_x_3760_, 0);
lean_inc(v_numFixed_3761_);
v_perms_3762_ = lean_ctor_get(v_x_3760_, 1);
lean_inc_ref(v_perms_3762_);
v_revDeps_3763_ = lean_ctor_get(v_x_3760_, 2);
lean_inc_ref(v_revDeps_3763_);
lean_dec_ref(v_x_3760_);
v___x_3764_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3765_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3766_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3767_ = l_Nat_reprFast(v_numFixed_3761_);
v___x_3768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
v___x_3769_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3766_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
v___x_3770_ = 0;
v___x_3771_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set_uint8(v___x_3771_, sizeof(void*)*1, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3765_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3772_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = lean_box(1);
v___x_3776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3774_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3776_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
lean_ctor_set(v___x_3779_, 1, v___x_3764_);
v___x_3780_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3781_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3762_);
v___x_3782_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
lean_ctor_set_uint8(v___x_3783_, sizeof(void*)*1, v___x_3770_);
v___x_3784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3779_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
lean_ctor_set(v___x_3785_, 1, v___x_3773_);
v___x_3786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v___x_3775_);
v___x_3787_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
lean_ctor_set(v___x_3789_, 1, v___x_3764_);
v___x_3790_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3791_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3763_);
v___x_3792_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
lean_ctor_set_uint8(v___x_3793_, sizeof(void*)*1, v___x_3770_);
v___x_3794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3789_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v___x_3795_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3796_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
lean_ctor_set(v___x_3797_, 1, v___x_3794_);
v___x_3798_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3797_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3795_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*1, v___x_3770_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3802_, lean_object* v_prec_3803_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3805_, lean_object* v_prec_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3805_, v_prec_3806_);
lean_dec(v_prec_3806_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___f_3816_; lean_object* v___x_5797__overap_3817_; lean_object* v___x_3818_; 
v___f_3816_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5797__overap_3817_ = lean_panic_fn_borrowed(v___f_3816_, v_msg_3810_);
lean_inc(v___y_3814_);
lean_inc_ref(v___y_3813_);
lean_inc(v___y_3812_);
lean_inc_ref(v___y_3811_);
v___x_3818_ = lean_apply_5(v___x_5797__overap_3817_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, lean_box(0));
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___f_3832_; lean_object* v___x_5807__overap_3833_; lean_object* v___x_3834_; 
v___f_3832_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5807__overap_3833_ = lean_panic_fn_borrowed(v___f_3832_, v_msg_3826_);
lean_inc(v___y_3830_);
lean_inc_ref(v___y_3829_);
lean_inc(v___y_3828_);
lean_inc_ref(v___y_3827_);
v___x_3834_ = lean_apply_5(v___x_5807__overap_3833_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, lean_box(0));
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___f_3848_; lean_object* v___x_5817__overap_3849_; lean_object* v___x_3850_; 
v___f_3848_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5817__overap_3849_ = lean_panic_fn_borrowed(v___f_3848_, v_msg_3842_);
lean_inc(v___y_3846_);
lean_inc_ref(v___y_3845_);
lean_inc(v___y_3844_);
lean_inc_ref(v___y_3843_);
v___x_3850_ = lean_apply_5(v___x_5817__overap_3849_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, lean_box(0));
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
return v_res_3857_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3861_ = lean_unsigned_to_nat(12u);
v___x_3862_ = lean_unsigned_to_nat(294u);
v___x_3863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3864_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3865_ = l_mkPanicMessageWithDecl(v___x_3864_, v___x_3863_, v___x_3862_, v___x_3861_, v___x_3860_);
return v___x_3865_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3868_ = lean_unsigned_to_nat(12u);
v___x_3869_ = lean_unsigned_to_nat(297u);
v___x_3870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3871_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3872_ = l_mkPanicMessageWithDecl(v___x_3871_, v___x_3870_, v___x_3869_, v___x_3868_, v___x_3867_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3873_, lean_object* v_as_3874_, size_t v_sz_3875_, size_t v_i_3876_, lean_object* v_b_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v_a_3884_; uint8_t v___x_3888_; 
v___x_3888_ = lean_usize_dec_lt(v_i_3876_, v_sz_3875_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v_b_3877_);
return v___x_3889_;
}
else
{
lean_object* v_a_3890_; 
v_a_3890_ = lean_array_uget_borrowed(v_as_3874_, v_i_3876_);
if (lean_obj_tag(v_a_3890_) == 1)
{
lean_object* v_val_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_val_3891_ = lean_ctor_get(v_a_3890_, 0);
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = lean_box(0);
v___x_3894_ = lean_array_get_borrowed(v___x_3893_, v_val_3891_, v___x_3892_);
if (lean_obj_tag(v___x_3894_) == 1)
{
lean_object* v_val_3895_; lean_object* v___x_3896_; 
v_val_3895_ = lean_ctor_get(v___x_3894_, 0);
v___x_3896_ = lean_array_get_borrowed(v___x_3893_, v___x_3873_, v_val_3895_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
lean_dec_ref(v_b_3877_);
v___x_3897_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3898_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3897_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3908_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3908_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3908_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
if (lean_obj_tag(v_a_3899_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; 
v_a_3903_ = lean_ctor_get(v_a_3899_, 0);
lean_inc(v_a_3903_);
lean_dec_ref(v_a_3899_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v_a_3903_);
v___x_3905_ = v___x_3901_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3903_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
else
{
lean_object* v_a_3907_; 
lean_del_object(v___x_3901_);
v_a_3907_ = lean_ctor_get(v_a_3899_, 0);
lean_inc(v_a_3907_);
lean_dec_ref(v_a_3899_);
v_a_3884_ = v_a_3907_;
goto v___jp_3883_;
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
v_a_3909_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3898_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3898_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
else
{
lean_object* v___x_3917_; 
lean_inc_ref(v___x_3896_);
v___x_3917_ = lean_array_push(v_b_3877_, v___x_3896_);
v_a_3884_ = v___x_3917_;
goto v___jp_3883_;
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3919_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3918_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_dec_ref(v___x_3919_);
v_a_3884_ = v_b_3877_;
goto v___jp_3883_;
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec_ref(v_b_3877_);
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3919_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3919_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
else
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = lean_box(0);
v___x_3929_ = lean_array_push(v_b_3877_, v___x_3928_);
v_a_3884_ = v___x_3929_;
goto v___jp_3883_;
}
}
v___jp_3883_:
{
size_t v___x_3885_; size_t v___x_3886_; 
v___x_3885_ = ((size_t)1ULL);
v___x_3886_ = lean_usize_add(v_i_3876_, v___x_3885_);
v_i_3876_ = v___x_3886_;
v_b_3877_ = v_a_3884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3930_, lean_object* v_as_3931_, lean_object* v_sz_3932_, lean_object* v_i_3933_, lean_object* v_b_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
size_t v_sz_boxed_3940_; size_t v_i_boxed_3941_; lean_object* v_res_3942_; 
v_sz_boxed_3940_ = lean_unbox_usize(v_sz_3932_);
lean_dec(v_sz_3932_);
v_i_boxed_3941_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_res_3942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3930_, v_as_3931_, v_sz_boxed_3940_, v_i_boxed_3941_, v_b_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec_ref(v_as_3931_);
lean_dec_ref(v___x_3930_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3945_, lean_object* v___x_3946_, lean_object* v___x_3947_, lean_object* v_a_3948_, lean_object* v_b_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
uint8_t v___x_3955_; 
v___x_3955_ = lean_nat_dec_lt(v_a_3948_, v_upperBound_3945_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec(v_a_3948_);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_b_3949_);
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; size_t v_sz_3959_; size_t v___x_3960_; lean_object* v___x_3961_; 
v___x_3957_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3958_ = lean_array_fget_borrowed(v___x_3946_, v_a_3948_);
v_sz_3959_ = lean_array_size(v___x_3958_);
v___x_3960_ = ((size_t)0ULL);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3947_, v___x_3958_, v_sz_3959_, v___x_3960_, v___x_3957_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref(v___x_3961_);
v___x_3963_ = lean_array_push(v_b_3949_, v_a_3962_);
v___x_3964_ = lean_unsigned_to_nat(1u);
v___x_3965_ = lean_nat_add(v_a_3948_, v___x_3964_);
lean_dec(v_a_3948_);
v_a_3948_ = v___x_3965_;
v_b_3949_ = v___x_3963_;
goto _start;
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec_ref(v_b_3949_);
lean_dec(v_a_3948_);
v_a_3967_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3961_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3961_);
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
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3975_, lean_object* v___x_3976_, lean_object* v___x_3977_, lean_object* v_a_3978_, lean_object* v_b_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3975_, v___x_3976_, v___x_3977_, v_a_3978_, v_b_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec_ref(v___x_3977_);
lean_dec_ref(v___x_3976_);
lean_dec(v_upperBound_3975_);
return v_res_3985_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3987_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3988_ = lean_unsigned_to_nat(8u);
v___x_3989_ = lean_unsigned_to_nat(281u);
v___x_3990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3991_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3992_ = l_mkPanicMessageWithDecl(v___x_3991_, v___x_3990_, v___x_3989_, v___x_3988_, v___x_3987_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3993_, lean_object* v_a_3994_, lean_object* v_b_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v_a_4002_; uint8_t v___x_4006_; 
v___x_4006_ = lean_nat_dec_lt(v_a_3994_, v_upperBound_3993_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; 
lean_dec(v_a_3994_);
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v_b_3995_);
return v___x_4007_;
}
else
{
lean_object* v_snd_4008_; lean_object* v_snd_4009_; lean_object* v_snd_4010_; lean_object* v_fst_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4135_; 
v_snd_4008_ = lean_ctor_get(v_b_3995_, 1);
lean_inc(v_snd_4008_);
v_snd_4009_ = lean_ctor_get(v_snd_4008_, 1);
lean_inc(v_snd_4009_);
v_snd_4010_ = lean_ctor_get(v_snd_4009_, 1);
lean_inc(v_snd_4010_);
v_fst_4011_ = lean_ctor_get(v_b_3995_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_b_3995_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; 
v_unused_4136_ = lean_ctor_get(v_b_3995_, 1);
lean_dec(v_unused_4136_);
v___x_4013_ = v_b_3995_;
v_isShared_4014_ = v_isSharedCheck_4135_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_fst_4011_);
lean_dec(v_b_3995_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4135_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v_fst_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4133_; 
v_fst_4015_ = lean_ctor_get(v_snd_4008_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_snd_4008_);
if (v_isSharedCheck_4133_ == 0)
{
lean_object* v_unused_4134_; 
v_unused_4134_ = lean_ctor_get(v_snd_4008_, 1);
lean_dec(v_unused_4134_);
v___x_4017_ = v_snd_4008_;
v_isShared_4018_ = v_isSharedCheck_4133_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_fst_4015_);
lean_dec(v_snd_4008_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4133_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v_fst_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4131_; 
v_fst_4019_ = lean_ctor_get(v_snd_4009_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v_snd_4009_);
if (v_isSharedCheck_4131_ == 0)
{
lean_object* v_unused_4132_; 
v_unused_4132_ = lean_ctor_get(v_snd_4009_, 1);
lean_dec(v_unused_4132_);
v___x_4021_ = v_snd_4009_;
v_isShared_4022_ = v_isSharedCheck_4131_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_fst_4019_);
lean_dec(v_snd_4009_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4131_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_array_4023_; lean_object* v_start_4024_; lean_object* v_stop_4025_; uint8_t v___x_4026_; 
v_array_4023_ = lean_ctor_get(v_snd_4010_, 0);
v_start_4024_ = lean_ctor_get(v_snd_4010_, 1);
v_stop_4025_ = lean_ctor_get(v_snd_4010_, 2);
v___x_4026_ = lean_nat_dec_lt(v_start_4024_, v_stop_4025_);
if (v___x_4026_ == 0)
{
lean_object* v___x_4028_; 
lean_dec(v_a_3994_);
if (v_isShared_4022_ == 0)
{
v___x_4028_ = v___x_4021_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_fst_4019_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_snd_4010_);
v___x_4028_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v___x_4028_);
v___x_4030_ = v___x_4017_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_fst_4015_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v___x_4030_);
v___x_4032_ = v___x_4013_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_fst_4011_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
}
}
}
else
{
lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4127_; 
lean_inc(v_stop_4025_);
lean_inc(v_start_4024_);
lean_inc_ref(v_array_4023_);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_snd_4010_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; lean_object* v_unused_4129_; lean_object* v_unused_4130_; 
v_unused_4128_ = lean_ctor_get(v_snd_4010_, 2);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_snd_4010_, 1);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_snd_4010_, 0);
lean_dec(v_unused_4130_);
v___x_4038_ = v_snd_4010_;
v_isShared_4039_ = v_isSharedCheck_4127_;
goto v_resetjp_4037_;
}
else
{
lean_dec(v_snd_4010_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4127_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v_array_4040_; lean_object* v_start_4041_; lean_object* v_stop_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4047_; 
v_array_4040_ = lean_ctor_get(v_fst_4019_, 0);
v_start_4041_ = lean_ctor_get(v_fst_4019_, 1);
v_stop_4042_ = lean_ctor_get(v_fst_4019_, 2);
v___x_4043_ = lean_array_fget(v_array_4023_, v_start_4024_);
v___x_4044_ = lean_unsigned_to_nat(1u);
v___x_4045_ = lean_nat_add(v_start_4024_, v___x_4044_);
lean_dec(v_start_4024_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 1, v___x_4045_);
v___x_4047_ = v___x_4038_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_array_4023_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v___x_4045_);
lean_ctor_set(v_reuseFailAlloc_4126_, 2, v_stop_4025_);
v___x_4047_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
uint8_t v___x_4048_; 
v___x_4048_ = lean_nat_dec_lt(v_start_4041_, v_stop_4042_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4050_; 
lean_dec(v___x_4043_);
lean_dec(v_a_3994_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 1, v___x_4047_);
v___x_4050_ = v___x_4021_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_fst_4019_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v___x_4047_);
v___x_4050_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4052_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v___x_4050_);
v___x_4052_ = v___x_4017_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_fst_4015_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4054_; 
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v___x_4052_);
v___x_4054_ = v___x_4013_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_fst_4011_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; 
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
}
}
}
else
{
lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4122_; 
lean_inc(v_stop_4042_);
lean_inc(v_start_4041_);
lean_inc_ref(v_array_4040_);
v_isSharedCheck_4122_ = !lean_is_exclusive(v_fst_4019_);
if (v_isSharedCheck_4122_ == 0)
{
lean_object* v_unused_4123_; lean_object* v_unused_4124_; lean_object* v_unused_4125_; 
v_unused_4123_ = lean_ctor_get(v_fst_4019_, 2);
lean_dec(v_unused_4123_);
v_unused_4124_ = lean_ctor_get(v_fst_4019_, 1);
lean_dec(v_unused_4124_);
v_unused_4125_ = lean_ctor_get(v_fst_4019_, 0);
lean_dec(v_unused_4125_);
v___x_4060_ = v_fst_4019_;
v_isShared_4061_ = v_isSharedCheck_4122_;
goto v_resetjp_4059_;
}
else
{
lean_dec(v_fst_4019_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4122_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4062_; lean_object* v___x_4064_; 
v___x_4062_ = lean_nat_add(v_start_4041_, v___x_4044_);
lean_dec(v_start_4041_);
if (v_isShared_4061_ == 0)
{
lean_ctor_set(v___x_4060_, 1, v___x_4062_);
v___x_4064_ = v___x_4060_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_array_4040_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4121_, 2, v_stop_4042_);
v___x_4064_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
if (lean_obj_tag(v___x_4043_) == 1)
{
lean_object* v_val_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4109_; 
v_val_4065_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4067_ = v___x_4043_;
v_isShared_4068_ = v_isSharedCheck_4109_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_val_4065_);
lean_dec(v___x_4043_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4109_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4069_ = lean_unsigned_to_nat(0u);
v___x_4070_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4071_ = lean_box(0);
v___x_4072_ = lean_array_get(v___x_4071_, v_val_4065_, v___x_4069_);
lean_dec(v_val_4065_);
lean_inc(v_a_3994_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v_a_3994_);
v___x_4074_ = v___x_4067_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_3994_);
v___x_4074_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
uint8_t v___x_4075_; 
v___x_4075_ = l_Option_instDecidableEq___redArg(v___x_4070_, v___x_4072_, v___x_4074_);
if (v___x_4075_ == 0)
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec_ref(v___x_4064_);
lean_dec_ref(v___x_4047_);
lean_del_object(v___x_4021_);
lean_del_object(v___x_4017_);
lean_dec(v_fst_4015_);
lean_del_object(v___x_4013_);
lean_dec(v_fst_4011_);
v___x_4076_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4077_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4076_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4087_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4087_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4087_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
if (lean_obj_tag(v_a_4078_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; 
lean_dec(v_a_3994_);
v_a_4082_ = lean_ctor_get(v_a_4078_, 0);
lean_inc(v_a_4082_);
lean_dec_ref(v_a_4078_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_a_4082_);
v___x_4084_ = v___x_4080_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4082_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
else
{
lean_object* v_a_4086_; 
lean_del_object(v___x_4080_);
v_a_4086_ = lean_ctor_get(v_a_4078_, 0);
lean_inc(v_a_4086_);
lean_dec_ref(v_a_4078_);
v_a_4002_ = v_a_4086_;
goto v___jp_4001_;
}
}
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_dec(v_a_3994_);
v_a_4088_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4077_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4077_);
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
else
{
lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4100_; 
lean_inc(v_fst_4015_);
v___x_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4096_, 0, v_fst_4015_);
v___x_4097_ = lean_array_push(v_fst_4011_, v___x_4096_);
v___x_4098_ = lean_nat_add(v_fst_4015_, v___x_4044_);
lean_dec(v_fst_4015_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 1, v___x_4047_);
lean_ctor_set(v___x_4021_, 0, v___x_4064_);
v___x_4100_ = v___x_4021_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4064_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v___x_4047_);
v___x_4100_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
lean_object* v___x_4102_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v___x_4100_);
lean_ctor_set(v___x_4017_, 0, v___x_4098_);
v___x_4102_ = v___x_4017_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4098_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v___x_4100_);
v___x_4102_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
lean_object* v___x_4104_; 
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v___x_4102_);
lean_ctor_set(v___x_4013_, 0, v___x_4097_);
v___x_4104_ = v___x_4013_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4097_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
v_a_4002_ = v___x_4104_;
goto v___jp_4001_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4113_; 
lean_dec(v___x_4043_);
v___x_4110_ = lean_box(0);
v___x_4111_ = lean_array_push(v_fst_4011_, v___x_4110_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 1, v___x_4047_);
lean_ctor_set(v___x_4021_, 0, v___x_4064_);
v___x_4113_ = v___x_4021_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4064_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4047_);
v___x_4113_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4115_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v___x_4113_);
v___x_4115_ = v___x_4017_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_fst_4015_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4117_; 
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 1, v___x_4115_);
lean_ctor_set(v___x_4013_, 0, v___x_4111_);
v___x_4117_ = v___x_4013_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
v_a_4002_ = v___x_4117_;
goto v___jp_4001_;
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
v___jp_4001_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4003_ = lean_unsigned_to_nat(1u);
v___x_4004_ = lean_nat_add(v_a_3994_, v___x_4003_);
lean_dec(v_a_3994_);
v_a_3994_ = v___x_4004_;
v_b_3995_ = v_a_4002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4137_, lean_object* v_a_4138_, lean_object* v_b_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4137_, v_a_4138_, v_b_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v_upperBound_4137_);
return v_res_4145_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4147_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4148_ = lean_unsigned_to_nat(4u);
v___x_4149_ = lean_unsigned_to_nat(275u);
v___x_4150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4151_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4152_ = l_mkPanicMessageWithDecl(v___x_4151_, v___x_4150_, v___x_4149_, v___x_4148_, v___x_4147_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4153_, lean_object* v___x_4154_, lean_object* v___x_4155_, lean_object* v_xs_4156_, lean_object* v_x_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_graph_4163_; lean_object* v_revDeps_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4217_; 
v_graph_4163_ = lean_ctor_get(v_a_4153_, 0);
v_revDeps_4164_ = lean_ctor_get(v_a_4153_, 1);
v_isSharedCheck_4217_ = !lean_is_exclusive(v_a_4153_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4166_ = v_a_4153_;
v_isShared_4167_ = v_isSharedCheck_4217_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_revDeps_4164_);
lean_inc(v_graph_4163_);
lean_dec(v_a_4153_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4217_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4168_ = lean_array_get_borrowed(v___x_4154_, v_graph_4163_, v___x_4155_);
v___x_4169_ = lean_array_get_size(v_xs_4156_);
v___x_4170_ = lean_array_get_size(v___x_4168_);
v___x_4171_ = lean_nat_dec_eq(v___x_4169_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_del_object(v___x_4166_);
lean_dec_ref(v_revDeps_4164_);
lean_dec_ref(v_graph_4163_);
lean_dec_ref(v_xs_4156_);
lean_dec(v___x_4155_);
v___x_4172_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4173_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4172_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
return v___x_4173_;
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4178_; 
v___x_4174_ = lean_mk_empty_array_with_capacity(v___x_4155_);
lean_inc_n(v___x_4155_, 2);
v___x_4175_ = l_Array_toSubarray___redArg(v_xs_4156_, v___x_4155_, v___x_4169_);
lean_inc(v___x_4168_);
v___x_4176_ = l_Array_toSubarray___redArg(v___x_4168_, v___x_4155_, v___x_4170_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 1, v___x_4176_);
lean_ctor_set(v___x_4166_, 0, v___x_4175_);
v___x_4178_ = v___x_4166_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4175_);
lean_ctor_set(v_reuseFailAlloc_4216_, 1, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_inc(v___x_4155_);
v___x_4179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4155_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4174_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4169_, v___x_4155_, v___x_4180_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v_snd_4183_; lean_object* v_fst_4184_; lean_object* v_fst_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref(v___x_4181_);
v_snd_4183_ = lean_ctor_get(v_a_4182_, 1);
lean_inc(v_snd_4183_);
v_fst_4184_ = lean_ctor_get(v_a_4182_, 0);
lean_inc_n(v_fst_4184_, 2);
lean_dec(v_a_4182_);
v_fst_4185_ = lean_ctor_get(v_snd_4183_, 0);
lean_inc(v_fst_4185_);
lean_dec(v_snd_4183_);
v___x_4186_ = lean_unsigned_to_nat(1u);
v___x_4187_ = lean_array_get_size(v_graph_4163_);
v___x_4188_ = lean_mk_empty_array_with_capacity(v___x_4186_);
v___x_4189_ = lean_array_push(v___x_4188_, v_fst_4184_);
v___x_4190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4187_, v_graph_4163_, v_fst_4184_, v___x_4186_, v___x_4189_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
lean_dec(v_fst_4184_);
lean_dec_ref(v_graph_4163_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4199_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4193_ = v___x_4190_;
v_isShared_4194_ = v_isSharedCheck_4199_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4199_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4195_, 0, v_fst_4185_);
lean_ctor_set(v___x_4195_, 1, v_a_4191_);
lean_ctor_set(v___x_4195_, 2, v_revDeps_4164_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 0, v___x_4195_);
v___x_4197_ = v___x_4193_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec(v_fst_4185_);
lean_dec_ref(v_revDeps_4164_);
v_a_4200_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4190_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4190_);
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
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec_ref(v_revDeps_4164_);
lean_dec_ref(v_graph_4163_);
v_a_4208_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4181_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4181_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4218_, lean_object* v___x_4219_, lean_object* v___x_4220_, lean_object* v_xs_4221_, lean_object* v_x_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4218_, v___x_4219_, v___x_4220_, v_xs_4221_, v_x_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec_ref(v_x_4222_);
lean_dec_ref(v___x_4219_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v___x_4235_; 
lean_inc_ref(v_preDefs_4229_);
v___x_4235_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v_value_4240_; lean_object* v___x_4241_; lean_object* v___f_4242_; uint8_t v___x_4243_; lean_object* v___x_4244_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = lean_array_get(v___x_4237_, v_preDefs_4229_, v___x_4238_);
lean_dec_ref(v_preDefs_4229_);
v_value_4240_ = lean_ctor_get(v___x_4239_, 7);
lean_inc_ref(v_value_4240_);
lean_dec(v___x_4239_);
v___x_4241_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4242_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4242_, 0, v_a_4236_);
lean_closure_set(v___f_4242_, 1, v___x_4241_);
lean_closure_set(v___f_4242_, 2, v___x_4238_);
v___x_4243_ = 0;
v___x_4244_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4240_, v___f_4242_, v___x_4243_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
return v___x_4244_;
}
else
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4252_; 
lean_dec_ref(v_preDefs_4229_);
v_a_4245_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4247_ = v___x_4235_;
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4235_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4252_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4250_; 
if (v_isShared_4248_ == 0)
{
v___x_4250_ = v___x_4247_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4260_, lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v_inst_4263_, lean_object* v_R_4264_, lean_object* v_a_4265_, lean_object* v_b_4266_, lean_object* v_c_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4260_, v___x_4261_, v___x_4262_, v_a_4265_, v_b_4266_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4274_, lean_object* v___x_4275_, lean_object* v___x_4276_, lean_object* v_inst_4277_, lean_object* v_R_4278_, lean_object* v_a_4279_, lean_object* v_b_4280_, lean_object* v_c_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4274_, v___x_4275_, v___x_4276_, v_inst_4277_, v_R_4278_, v_a_4279_, v_b_4280_, v_c_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec_ref(v___x_4276_);
lean_dec_ref(v___x_4275_);
lean_dec(v_upperBound_4274_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4288_, lean_object* v_inst_4289_, lean_object* v_R_4290_, lean_object* v_a_4291_, lean_object* v_b_4292_, lean_object* v_c_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4288_, v_a_4291_, v_b_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4300_, lean_object* v_inst_4301_, lean_object* v_R_4302_, lean_object* v_a_4303_, lean_object* v_b_4304_, lean_object* v_c_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4300_, v_inst_4301_, v_R_4302_, v_a_4303_, v_b_4304_, v_c_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v_upperBound_4300_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4312_, size_t v_i_4313_, size_t v_stop_4314_, lean_object* v_b_4315_){
_start:
{
uint8_t v___x_4316_; 
v___x_4316_ = lean_usize_dec_eq(v_i_4313_, v_stop_4314_);
if (v___x_4316_ == 0)
{
size_t v___x_4317_; size_t v___x_4318_; lean_object* v___x_4319_; 
v___x_4317_ = ((size_t)1ULL);
v___x_4318_ = lean_usize_sub(v_i_4313_, v___x_4317_);
v___x_4319_ = lean_array_uget_borrowed(v_as_4312_, v___x_4318_);
if (lean_obj_tag(v___x_4319_) == 0)
{
v_i_4313_ = v___x_4318_;
goto _start;
}
else
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = lean_unsigned_to_nat(1u);
v___x_4322_ = lean_nat_add(v_b_4315_, v___x_4321_);
lean_dec(v_b_4315_);
v_i_4313_ = v___x_4318_;
v_b_4315_ = v___x_4322_;
goto _start;
}
}
else
{
return v_b_4315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4324_, lean_object* v_i_4325_, lean_object* v_stop_4326_, lean_object* v_b_4327_){
_start:
{
size_t v_i_boxed_4328_; size_t v_stop_boxed_4329_; lean_object* v_res_4330_; 
v_i_boxed_4328_ = lean_unbox_usize(v_i_4325_);
lean_dec(v_i_4325_);
v_stop_boxed_4329_ = lean_unbox_usize(v_stop_4326_);
lean_dec(v_stop_4326_);
v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4324_, v_i_boxed_4328_, v_stop_boxed_4329_, v_b_4327_);
lean_dec_ref(v_as_4324_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4331_){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4332_ = lean_unsigned_to_nat(0u);
v___x_4333_ = lean_array_get_size(v_perm_4331_);
v___x_4334_ = lean_nat_dec_lt(v___x_4332_, v___x_4333_);
if (v___x_4334_ == 0)
{
return v___x_4332_;
}
else
{
size_t v___x_4335_; size_t v___x_4336_; lean_object* v___x_4337_; 
v___x_4335_ = lean_usize_of_nat(v___x_4333_);
v___x_4336_ = ((size_t)0ULL);
v___x_4337_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4331_, v___x_4335_, v___x_4336_, v___x_4332_);
return v___x_4337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4338_);
lean_dec_ref(v_perm_4338_);
return v_res_4339_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4340_, lean_object* v_i_4341_){
_start:
{
lean_object* v___x_4342_; uint8_t v___x_4343_; 
v___x_4342_ = lean_array_get_size(v_perm_4340_);
v___x_4343_ = lean_nat_dec_lt(v_i_4341_, v___x_4342_);
if (v___x_4343_ == 0)
{
return v___x_4343_;
}
else
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_array_fget_borrowed(v_perm_4340_, v_i_4341_);
if (lean_obj_tag(v___x_4344_) == 0)
{
uint8_t v___x_4345_; 
v___x_4345_ = 0;
return v___x_4345_;
}
else
{
return v___x_4343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4346_, lean_object* v_i_4347_){
_start:
{
uint8_t v_res_4348_; lean_object* v_r_4349_; 
v_res_4348_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4346_, v_i_4347_);
lean_dec(v_i_4347_);
lean_dec_ref(v_perm_4346_);
v_r_4349_ = lean_box(v_res_4348_);
return v_r_4349_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v___f_4356_; lean_object* v___x_1076__overap_4357_; lean_object* v___x_4358_; 
v___f_4356_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_1076__overap_4357_ = lean_panic_fn_borrowed(v___f_4356_, v_msg_4350_);
lean_inc(v___y_4354_);
lean_inc_ref(v___y_4353_);
lean_inc(v___y_4352_);
lean_inc_ref(v___y_4351_);
v___x_4358_ = lean_apply_5(v___x_1076__overap_4357_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, lean_box(0));
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4366_, lean_object* v_msg_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4374_, lean_object* v_msg_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4374_, v_msg_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4382_, lean_object* v_maxFVars_x3f_4383_, lean_object* v_k_4384_, uint8_t v_cleanupAnnotations_4385_, uint8_t v_whnfType_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___f_4392_; lean_object* v___x_4393_; 
v___f_4392_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4392_, 0, v_k_4384_);
v___x_4393_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4382_, v_maxFVars_x3f_4383_, v___f_4392_, v_cleanupAnnotations_4385_, v_whnfType_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4393_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4393_);
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
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
v_a_4402_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4393_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4393_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4410_, lean_object* v_maxFVars_x3f_4411_, lean_object* v_k_4412_, lean_object* v_cleanupAnnotations_4413_, lean_object* v_whnfType_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4420_; uint8_t v_whnfType_boxed_4421_; lean_object* v_res_4422_; 
v_cleanupAnnotations_boxed_4420_ = lean_unbox(v_cleanupAnnotations_4413_);
v_whnfType_boxed_4421_ = lean_unbox(v_whnfType_4414_);
v_res_4422_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4410_, v_maxFVars_x3f_4411_, v_k_4412_, v_cleanupAnnotations_boxed_4420_, v_whnfType_boxed_4421_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4423_, lean_object* v_type_4424_, lean_object* v_maxFVars_x3f_4425_, lean_object* v_k_4426_, uint8_t v_cleanupAnnotations_4427_, uint8_t v_whnfType_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4424_, v_maxFVars_x3f_4425_, v_k_4426_, v_cleanupAnnotations_4427_, v_whnfType_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4435_, lean_object* v_type_4436_, lean_object* v_maxFVars_x3f_4437_, lean_object* v_k_4438_, lean_object* v_cleanupAnnotations_4439_, lean_object* v_whnfType_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4446_; uint8_t v_whnfType_boxed_4447_; lean_object* v_res_4448_; 
v_cleanupAnnotations_boxed_4446_ = lean_unbox(v_cleanupAnnotations_4439_);
v_whnfType_boxed_4447_ = lean_unbox(v_whnfType_4440_);
v_res_4448_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4435_, v_type_4436_, v_maxFVars_x3f_4437_, v_k_4438_, v_cleanupAnnotations_boxed_4446_, v_whnfType_boxed_4447_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
return v_res_4448_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4451_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4452_ = lean_unsigned_to_nat(6u);
v___x_4453_ = lean_unsigned_to_nat(329u);
v___x_4454_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4455_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4456_ = l_mkPanicMessageWithDecl(v___x_4455_, v___x_4454_, v___x_4453_, v___x_4452_, v___x_4451_);
return v___x_4456_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4460_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4461_ = lean_unsigned_to_nat(8u);
v___x_4462_ = lean_unsigned_to_nat(322u);
v___x_4463_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4464_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4465_ = l_mkPanicMessageWithDecl(v___x_4464_, v___x_4463_, v___x_4462_, v___x_4461_, v___x_4460_);
return v___x_4465_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4467_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4468_ = lean_unsigned_to_nat(8u);
v___x_4469_ = lean_unsigned_to_nat(325u);
v___x_4470_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4472_ = l_mkPanicMessageWithDecl(v___x_4471_, v___x_4470_, v___x_4469_, v___x_4468_, v___x_4467_);
return v___x_4472_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4474_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4475_ = lean_unsigned_to_nat(8u);
v___x_4476_ = lean_unsigned_to_nat(324u);
v___x_4477_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4478_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4479_ = l_mkPanicMessageWithDecl(v___x_4478_, v___x_4477_, v___x_4476_, v___x_4475_, v___x_4474_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4480_, lean_object* v_xs_4481_, lean_object* v_val_4482_, lean_object* v_i_4483_, lean_object* v_perm_4484_, lean_object* v_k_4485_, lean_object* v_xs_x27_4486_, lean_object* v_type_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v___x_4493_; uint8_t v___x_4494_; 
v___x_4493_ = lean_array_get_size(v_xs_x27_4486_);
v___x_4494_ = lean_nat_dec_eq(v___x_4493_, v___x_4480_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
lean_dec_ref(v_type_4487_);
lean_dec_ref(v_k_4485_);
lean_dec_ref(v_perm_4484_);
lean_dec_ref(v_xs_4481_);
v___x_4495_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4496_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4495_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4496_;
}
else
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v_x_4499_; lean_object* v___x_4500_; 
v___x_4497_ = l_Lean_instInhabitedExpr;
v___x_4498_ = lean_unsigned_to_nat(0u);
v_x_4499_ = lean_array_get_borrowed(v___x_4497_, v_xs_x27_4486_, v___x_4498_);
lean_inc(v___y_4491_);
lean_inc_ref(v___y_4490_);
lean_inc(v___y_4489_);
lean_inc_ref(v___y_4488_);
lean_inc(v_x_4499_);
v___x_4500_ = lean_infer_type(v_x_4499_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; uint8_t v___x_4502_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref(v___x_4500_);
v___x_4502_ = l_Lean_Expr_hasLooseBVars(v_a_4501_);
lean_dec(v_a_4501_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; uint8_t v___x_4504_; 
v___x_4503_ = lean_array_get_size(v_xs_4481_);
v___x_4504_ = lean_nat_dec_lt(v_val_4482_, v___x_4503_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; lean_object* v___x_4506_; 
lean_dec_ref(v_type_4487_);
lean_dec_ref(v_k_4485_);
lean_dec_ref(v_perm_4484_);
lean_dec_ref(v_xs_4481_);
v___x_4505_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4506_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4505_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4506_;
}
else
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4507_ = lean_nat_add(v_i_4483_, v___x_4480_);
lean_inc(v_x_4499_);
v___x_4508_ = lean_array_set(v_xs_4481_, v_val_4482_, v_x_4499_);
v___x_4509_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4484_, v_k_4485_, v___x_4507_, v_type_4487_, v___x_4508_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4509_;
}
}
else
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec_ref(v_type_4487_);
lean_dec_ref(v_k_4485_);
lean_dec_ref(v_perm_4484_);
lean_dec_ref(v_xs_4481_);
v___x_4510_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4511_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4510_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4511_;
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_dec_ref(v_type_4487_);
lean_dec_ref(v_k_4485_);
lean_dec_ref(v_perm_4484_);
lean_dec_ref(v_xs_4481_);
v_a_4512_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4500_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4500_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4520_, lean_object* v_xs_4521_, lean_object* v_val_4522_, lean_object* v_i_4523_, lean_object* v_perm_4524_, lean_object* v_k_4525_, lean_object* v_xs_x27_4526_, lean_object* v_type_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4520_, v_xs_4521_, v_val_4522_, v_i_4523_, v_perm_4524_, v_k_4525_, v_xs_x27_4526_, v_type_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec_ref(v_xs_x27_4526_);
lean_dec(v_i_4523_);
lean_dec(v_val_4522_);
lean_dec(v___x_4520_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4534_, lean_object* v_k_4535_, lean_object* v_i_4536_, lean_object* v_type_4537_, lean_object* v_xs_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v___x_4544_; uint8_t v___x_4545_; 
v___x_4544_ = lean_array_get_size(v_perm_4534_);
v___x_4545_ = lean_nat_dec_lt(v_i_4536_, v___x_4544_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; 
lean_dec_ref(v_type_4537_);
lean_dec(v_i_4536_);
lean_dec_ref(v_perm_4534_);
lean_inc(v_a_4542_);
lean_inc_ref(v_a_4541_);
lean_inc(v_a_4540_);
lean_inc_ref(v_a_4539_);
v___x_4546_ = lean_apply_6(v_k_4535_, v_xs_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, lean_box(0));
return v___x_4546_;
}
else
{
lean_object* v___x_4547_; 
v___x_4547_ = lean_array_fget_borrowed(v_perm_4534_, v_i_4536_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v___x_4548_; 
lean_inc(v_a_4542_);
lean_inc_ref(v_a_4541_);
lean_inc(v_a_4540_);
lean_inc_ref(v_a_4539_);
v___x_4548_ = lean_whnf(v_type_4537_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; uint8_t v___x_4550_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_a_4549_);
lean_dec_ref(v___x_4548_);
v___x_4550_ = l_Lean_Expr_isForall(v_a_4549_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
lean_dec(v_a_4549_);
lean_dec_ref(v_xs_4538_);
lean_dec(v_i_4536_);
lean_dec_ref(v_k_4535_);
lean_dec_ref(v_perm_4534_);
v___x_4551_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4552_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4551_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
return v___x_4552_;
}
else
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4553_ = lean_unsigned_to_nat(1u);
v___x_4554_ = lean_nat_add(v_i_4536_, v___x_4553_);
lean_dec(v_i_4536_);
v___x_4555_ = l_Lean_Expr_bindingBody_x21(v_a_4549_);
lean_dec(v_a_4549_);
v_i_4536_ = v___x_4554_;
v_type_4537_ = v___x_4555_;
goto _start;
}
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec_ref(v_xs_4538_);
lean_dec(v_i_4536_);
lean_dec_ref(v_k_4535_);
lean_dec_ref(v_perm_4534_);
v_a_4557_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4548_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4548_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
else
{
lean_object* v_val_4565_; lean_object* v___x_4566_; lean_object* v___f_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; lean_object* v___x_4570_; 
v_val_4565_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_val_4565_);
v___x_4566_ = lean_unsigned_to_nat(1u);
v___f_4567_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4567_, 0, v___x_4566_);
lean_closure_set(v___f_4567_, 1, v_xs_4538_);
lean_closure_set(v___f_4567_, 2, v_val_4565_);
lean_closure_set(v___f_4567_, 3, v_i_4536_);
lean_closure_set(v___f_4567_, 4, v_perm_4534_);
lean_closure_set(v___f_4567_, 5, v_k_4535_);
v___x_4568_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4569_ = 0;
v___x_4570_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4537_, v___x_4568_, v___f_4567_, v___x_4545_, v___x_4569_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
return v___x_4570_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4571_, lean_object* v_k_4572_, lean_object* v_i_4573_, lean_object* v_type_4574_, lean_object* v_xs_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4571_, v_k_4572_, v_i_4573_, v_type_4574_, v_xs_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
lean_dec(v_a_4579_);
lean_dec_ref(v_a_4578_);
lean_dec(v_a_4577_);
lean_dec_ref(v_a_4576_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4582_, lean_object* v_perm_4583_, lean_object* v_k_4584_, lean_object* v_i_4585_, lean_object* v_type_4586_, lean_object* v_xs_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4583_, v_k_4584_, v_i_4585_, v_type_4586_, v_xs_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4594_, lean_object* v_perm_4595_, lean_object* v_k_4596_, lean_object* v_i_4597_, lean_object* v_type_4598_, lean_object* v_xs_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4594_, v_perm_4595_, v_k_4596_, v_i_4597_, v_type_4598_, v_xs_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
return v_res_4605_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = lean_unsigned_to_nat(0u);
v___x_4607_ = l_Lean_Level_ofNat(v___x_4606_);
return v___x_4607_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4609_ = l_Lean_mkSort(v___x_4608_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4610_, lean_object* v_type_4611_, lean_object* v_k_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4618_ = lean_unsigned_to_nat(0u);
v___x_4619_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4610_);
v___x_4620_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4621_ = lean_mk_array(v___x_4619_, v___x_4620_);
v___x_4622_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4610_, v_k_4612_, v___x_4618_, v_type_4611_, v___x_4621_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4623_, lean_object* v_type_4624_, lean_object* v_k_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4623_, v_type_4624_, v_k_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4632_, lean_object* v_perm_4633_, lean_object* v_type_4634_, lean_object* v_k_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_){
_start:
{
lean_object* v___x_4641_; 
v___x_4641_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4633_, v_type_4634_, v_k_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4642_, lean_object* v_perm_4643_, lean_object* v_type_4644_, lean_object* v_k_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4642_, v_perm_4643_, v_type_4644_, v_k_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4652_, lean_object* v_runInBase_4653_, lean_object* v_b_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = lean_apply_1(v_k_4652_, v_b_4654_);
lean_inc(v___y_4658_);
lean_inc_ref(v___y_4657_);
lean_inc(v___y_4656_);
lean_inc_ref(v___y_4655_);
v___x_4661_ = lean_apply_7(v_runInBase_4653_, lean_box(0), v___x_4660_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, lean_box(0));
return v___x_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4662_, lean_object* v_runInBase_4663_, lean_object* v_b_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4662_, v_runInBase_4663_, v_b_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4671_, lean_object* v_perm_4672_, lean_object* v_type_4673_, lean_object* v_runInBase_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v___f_4680_; lean_object* v___x_4681_; 
v___f_4680_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4680_, 0, v_k_4671_);
lean_closure_set(v___f_4680_, 1, v_runInBase_4674_);
v___x_4681_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4672_, v_type_4673_, v___f_4680_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4682_, lean_object* v_perm_4683_, lean_object* v_type_4684_, lean_object* v_runInBase_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4682_, v_perm_4683_, v_type_4684_, v_runInBase_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4692_, lean_object* v_inst_4693_, lean_object* v_perm_4694_, lean_object* v_type_4695_, lean_object* v_k_4696_){
_start:
{
lean_object* v_toBind_4697_; lean_object* v_liftWith_4698_; lean_object* v_restoreM_4699_; lean_object* v___f_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
v_toBind_4697_ = lean_ctor_get(v_inst_4693_, 1);
lean_inc(v_toBind_4697_);
lean_dec_ref(v_inst_4693_);
v_liftWith_4698_ = lean_ctor_get(v_inst_4692_, 0);
lean_inc(v_liftWith_4698_);
v_restoreM_4699_ = lean_ctor_get(v_inst_4692_, 1);
lean_inc(v_restoreM_4699_);
lean_dec_ref(v_inst_4692_);
v___f_4700_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4700_, 0, v_k_4696_);
lean_closure_set(v___f_4700_, 1, v_perm_4694_);
lean_closure_set(v___f_4700_, 2, v_type_4695_);
v___x_4701_ = lean_apply_2(v_liftWith_4698_, lean_box(0), v___f_4700_);
v___x_4702_ = lean_apply_1(v_restoreM_4699_, lean_box(0));
v___x_4703_ = lean_apply_4(v_toBind_4697_, lean_box(0), lean_box(0), v___x_4701_, v___x_4702_);
return v___x_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4704_, lean_object* v_00_u03b1_4705_, lean_object* v_inst_4706_, lean_object* v_inst_4707_, lean_object* v_perm_4708_, lean_object* v_type_4709_, lean_object* v_k_4710_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4706_, v_inst_4707_, v_perm_4708_, v_type_4709_, v_k_4710_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v___f_4718_; lean_object* v___x_603__overap_4719_; lean_object* v___x_4720_; 
v___f_4718_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_603__overap_4719_ = lean_panic_fn_borrowed(v___f_4718_, v_msg_4712_);
lean_inc(v___y_4716_);
lean_inc_ref(v___y_4715_);
lean_inc(v___y_4714_);
lean_inc_ref(v___y_4713_);
v___x_4720_ = lean_apply_5(v___x_603__overap_4719_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, lean_box(0));
return v___x_4720_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
lean_dec(v___y_4725_);
lean_dec_ref(v___y_4724_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
return v_res_4727_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4730_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4731_ = lean_unsigned_to_nat(10u);
v___x_4732_ = lean_unsigned_to_nat(353u);
v___x_4733_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4734_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4735_ = l_mkPanicMessageWithDecl(v___x_4734_, v___x_4733_, v___x_4732_, v___x_4731_, v___x_4730_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4736_, lean_object* v_xs_4737_, lean_object* v_tail_4738_, lean_object* v_ys_4739_, lean_object* v_type_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4736_, v_xs_4737_, v_tail_4738_, v_ys_4739_, v_type_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
lean_dec(v___y_4744_);
lean_dec_ref(v___y_4743_);
lean_dec(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec_ref(v_ys_4739_);
lean_dec(v___x_4736_);
return v_res_4746_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4747_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4748_ = lean_unsigned_to_nat(8u);
v___x_4749_ = lean_unsigned_to_nat(349u);
v___x_4750_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4751_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4752_ = l_mkPanicMessageWithDecl(v___x_4751_, v___x_4750_, v___x_4749_, v___x_4748_, v___x_4747_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4753_, lean_object* v_x_4754_, lean_object* v_x_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
if (lean_obj_tag(v_x_4754_) == 0)
{
lean_object* v___x_4761_; 
lean_dec_ref(v_xs_4753_);
v___x_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4761_, 0, v_x_4755_);
return v___x_4761_;
}
else
{
lean_object* v_head_4762_; 
v_head_4762_ = lean_ctor_get(v_x_4754_, 0);
if (lean_obj_tag(v_head_4762_) == 0)
{
lean_object* v_tail_4763_; lean_object* v___x_4764_; lean_object* v___f_4765_; lean_object* v___x_4766_; uint8_t v___x_4767_; lean_object* v___x_4768_; 
v_tail_4763_ = lean_ctor_get(v_x_4754_, 1);
lean_inc(v_tail_4763_);
lean_dec_ref(v_x_4754_);
v___x_4764_ = lean_unsigned_to_nat(1u);
v___f_4765_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4765_, 0, v___x_4764_);
lean_closure_set(v___f_4765_, 1, v_xs_4753_);
lean_closure_set(v___f_4765_, 2, v_tail_4763_);
v___x_4766_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4767_ = 0;
v___x_4768_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4755_, v___x_4766_, v___f_4765_, v___x_4767_, v___x_4767_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_);
return v___x_4768_;
}
else
{
lean_object* v_tail_4769_; lean_object* v_val_4770_; lean_object* v___x_4771_; uint8_t v___x_4772_; 
lean_inc_ref(v_head_4762_);
v_tail_4769_ = lean_ctor_get(v_x_4754_, 1);
lean_inc(v_tail_4769_);
lean_dec_ref(v_x_4754_);
v_val_4770_ = lean_ctor_get(v_head_4762_, 0);
lean_inc(v_val_4770_);
lean_dec_ref(v_head_4762_);
v___x_4771_ = lean_array_get_size(v_xs_4753_);
v___x_4772_ = lean_nat_dec_lt(v_val_4770_, v___x_4771_);
if (v___x_4772_ == 0)
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
lean_dec(v_val_4770_);
lean_dec(v_tail_4769_);
lean_dec_ref(v_x_4755_);
lean_dec_ref(v_xs_4753_);
v___x_4773_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4774_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4773_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_);
return v___x_4774_;
}
else
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4775_ = l_Lean_instInhabitedExpr;
v___x_4776_ = lean_array_get_borrowed(v___x_4775_, v_xs_4753_, v_val_4770_);
lean_dec(v_val_4770_);
v___x_4777_ = lean_unsigned_to_nat(1u);
v___x_4778_ = lean_mk_empty_array_with_capacity(v___x_4777_);
lean_inc(v___x_4776_);
v___x_4779_ = lean_array_push(v___x_4778_, v___x_4776_);
v___x_4780_ = l_Lean_Meta_instantiateForall(v_x_4755_, v___x_4779_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_);
lean_dec_ref(v___x_4779_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref(v___x_4780_);
v_x_4754_ = v_tail_4769_;
v_x_4755_ = v_a_4781_;
goto _start;
}
else
{
lean_dec(v_tail_4769_);
lean_dec_ref(v_xs_4753_);
return v___x_4780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4783_, lean_object* v_xs_4784_, lean_object* v_tail_4785_, lean_object* v_ys_4786_, lean_object* v_type_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_){
_start:
{
lean_object* v___x_4793_; uint8_t v___x_4794_; 
v___x_4793_ = lean_array_get_size(v_ys_4786_);
v___x_4794_ = lean_nat_dec_eq(v___x_4793_, v___x_4783_);
if (v___x_4794_ == 0)
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_dec_ref(v_type_4787_);
lean_dec(v_tail_4785_);
lean_dec_ref(v_xs_4784_);
v___x_4795_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4796_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4795_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
return v___x_4796_;
}
else
{
lean_object* v___x_4797_; 
v___x_4797_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4784_, v_tail_4785_, v_type_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; uint8_t v___x_4799_; uint8_t v___x_4800_; lean_object* v___x_4801_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref(v___x_4797_);
v___x_4799_ = 0;
v___x_4800_ = 1;
v___x_4801_ = l_Lean_Meta_mkForallFVars(v_ys_4786_, v_a_4798_, v___x_4799_, v___x_4794_, v___x_4794_, v___x_4800_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
return v___x_4801_;
}
else
{
return v___x_4797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4802_, lean_object* v_x_4803_, lean_object* v_x_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4802_, v_x_4803_, v_x_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
return v_res_4810_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4813_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4814_ = lean_unsigned_to_nat(2u);
v___x_4815_ = lean_unsigned_to_nat(343u);
v___x_4816_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4817_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4818_ = l_mkPanicMessageWithDecl(v___x_4817_, v___x_4816_, v___x_4815_, v___x_4814_, v___x_4813_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4819_, lean_object* v_type_u2080_4820_, lean_object* v_xs_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; 
v___x_4827_ = lean_array_get_size(v_xs_4821_);
v___x_4828_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4819_);
v___x_4829_ = lean_nat_dec_eq(v___x_4827_, v___x_4828_);
lean_dec(v___x_4828_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
lean_dec_ref(v_xs_4821_);
lean_dec_ref(v_type_u2080_4820_);
lean_dec_ref(v_perm_4819_);
v___x_4830_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4831_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4830_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
return v___x_4831_;
}
else
{
lean_object* v_mask_4832_; lean_object* v___x_4833_; 
v_mask_4832_ = lean_array_to_list(v_perm_4819_);
v___x_4833_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4821_, v_mask_4832_, v_type_u2080_4820_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
return v___x_4833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4834_, lean_object* v_type_u2080_4835_, lean_object* v_xs_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4834_, v_type_u2080_4835_, v_xs_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4843_, lean_object* v_maxFVars_4844_, lean_object* v_k_4845_, uint8_t v_cleanupAnnotations_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
lean_object* v___f_4852_; uint8_t v___x_4853_; uint8_t v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___f_4852_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4852_, 0, v_k_4845_);
v___x_4853_ = 1;
v___x_4854_ = 0;
v___x_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4855_, 0, v_maxFVars_4844_);
v___x_4856_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4843_, v___x_4853_, v___x_4854_, v___x_4853_, v___x_4854_, v___x_4855_, v___f_4852_, v_cleanupAnnotations_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
lean_dec_ref(v___x_4855_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
v_a_4857_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4856_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4856_);
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
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
v_a_4865_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4856_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4856_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4873_, lean_object* v_maxFVars_4874_, lean_object* v_k_4875_, lean_object* v_cleanupAnnotations_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4882_; lean_object* v_res_4883_; 
v_cleanupAnnotations_boxed_4882_ = lean_unbox(v_cleanupAnnotations_4876_);
v_res_4883_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4873_, v_maxFVars_4874_, v_k_4875_, v_cleanupAnnotations_boxed_4882_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4884_, lean_object* v_e_4885_, lean_object* v_maxFVars_4886_, lean_object* v_k_4887_, uint8_t v_cleanupAnnotations_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_){
_start:
{
lean_object* v___x_4894_; 
v___x_4894_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4885_, v_maxFVars_4886_, v_k_4887_, v_cleanupAnnotations_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4895_, lean_object* v_e_4896_, lean_object* v_maxFVars_4897_, lean_object* v_k_4898_, lean_object* v_cleanupAnnotations_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4905_; lean_object* v_res_4906_; 
v_cleanupAnnotations_boxed_4905_ = lean_unbox(v_cleanupAnnotations_4899_);
v_res_4906_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4895_, v_e_4896_, v_maxFVars_4897_, v_k_4898_, v_cleanupAnnotations_boxed_4905_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
return v_res_4906_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4907_){
_start:
{
if (lean_obj_tag(v_x_4907_) == 0)
{
uint8_t v___x_4908_; 
v___x_4908_ = 1;
return v___x_4908_;
}
else
{
lean_object* v_head_4909_; 
v_head_4909_ = lean_ctor_get(v_x_4907_, 0);
if (lean_obj_tag(v_head_4909_) == 0)
{
lean_object* v_tail_4910_; 
v_tail_4910_ = lean_ctor_get(v_x_4907_, 1);
v_x_4907_ = v_tail_4910_;
goto _start;
}
else
{
uint8_t v___x_4912_; 
v___x_4912_ = 0;
return v___x_4912_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4913_){
_start:
{
uint8_t v_res_4914_; lean_object* v_r_4915_; 
v_res_4914_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4913_);
lean_dec(v_x_4913_);
v_r_4915_ = lean_box(v_res_4914_);
return v_r_4915_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v___x_4918_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4919_ = lean_unsigned_to_nat(12u);
v___x_4920_ = lean_unsigned_to_nat(376u);
v___x_4921_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4922_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4923_ = l_mkPanicMessageWithDecl(v___x_4922_, v___x_4921_, v___x_4920_, v___x_4919_, v___x_4918_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4924_, lean_object* v_xs_4925_, lean_object* v_tail_4926_, lean_object* v___x_4927_, lean_object* v___x_4928_, lean_object* v_ys_4929_, lean_object* v_value_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_){
_start:
{
uint8_t v___x_1310__boxed_4936_; uint8_t v___x_1311__boxed_4937_; lean_object* v_res_4938_; 
v___x_1310__boxed_4936_ = lean_unbox(v___x_4927_);
v___x_1311__boxed_4937_ = lean_unbox(v___x_4928_);
v_res_4938_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4924_, v_xs_4925_, v_tail_4926_, v___x_1310__boxed_4936_, v___x_1311__boxed_4937_, v_ys_4929_, v_value_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
lean_dec(v___y_4934_);
lean_dec_ref(v___y_4933_);
lean_dec(v___y_4932_);
lean_dec_ref(v___y_4931_);
lean_dec_ref(v_ys_4929_);
lean_dec(v___x_4924_);
return v_res_4938_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4939_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4940_ = lean_unsigned_to_nat(8u);
v___x_4941_ = lean_unsigned_to_nat(368u);
v___x_4942_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4943_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4944_ = l_mkPanicMessageWithDecl(v___x_4943_, v___x_4942_, v___x_4941_, v___x_4940_, v___x_4939_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4945_, lean_object* v_x_4946_, lean_object* v_x_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_){
_start:
{
if (lean_obj_tag(v_x_4946_) == 0)
{
lean_object* v___x_4953_; 
lean_dec_ref(v_xs_4945_);
v___x_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4953_, 0, v_x_4947_);
return v___x_4953_;
}
else
{
lean_object* v_head_4954_; 
v_head_4954_ = lean_ctor_get(v_x_4946_, 0);
if (lean_obj_tag(v_head_4954_) == 0)
{
lean_object* v_tail_4955_; uint8_t v___x_4956_; 
v_tail_4955_ = lean_ctor_get(v_x_4946_, 1);
lean_inc(v_tail_4955_);
lean_dec_ref(v_x_4946_);
v___x_4956_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4955_);
if (v___x_4956_ == 0)
{
uint8_t v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___f_4961_; lean_object* v___x_4962_; 
v___x_4957_ = 1;
v___x_4958_ = lean_unsigned_to_nat(1u);
v___x_4959_ = lean_box(v___x_4956_);
v___x_4960_ = lean_box(v___x_4957_);
v___f_4961_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4961_, 0, v___x_4958_);
lean_closure_set(v___f_4961_, 1, v_xs_4945_);
lean_closure_set(v___f_4961_, 2, v_tail_4955_);
lean_closure_set(v___f_4961_, 3, v___x_4959_);
lean_closure_set(v___f_4961_, 4, v___x_4960_);
v___x_4962_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4947_, v___x_4958_, v___f_4961_, v___x_4956_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_);
return v___x_4962_;
}
else
{
lean_object* v___x_4963_; 
lean_dec(v_tail_4955_);
lean_dec_ref(v_xs_4945_);
v___x_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4963_, 0, v_x_4947_);
return v___x_4963_;
}
}
else
{
lean_object* v_tail_4964_; lean_object* v_val_4965_; lean_object* v___x_4966_; uint8_t v___x_4967_; 
lean_inc_ref(v_head_4954_);
v_tail_4964_ = lean_ctor_get(v_x_4946_, 1);
lean_inc(v_tail_4964_);
lean_dec_ref(v_x_4946_);
v_val_4965_ = lean_ctor_get(v_head_4954_, 0);
lean_inc(v_val_4965_);
lean_dec_ref(v_head_4954_);
v___x_4966_ = lean_array_get_size(v_xs_4945_);
v___x_4967_ = lean_nat_dec_lt(v_val_4965_, v___x_4966_);
if (v___x_4967_ == 0)
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_dec(v_val_4965_);
lean_dec(v_tail_4964_);
lean_dec_ref(v_x_4947_);
lean_dec_ref(v_xs_4945_);
v___x_4968_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4969_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4968_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_);
return v___x_4969_;
}
else
{
lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4970_ = l_Lean_instInhabitedExpr;
v___x_4971_ = lean_array_get_borrowed(v___x_4970_, v_xs_4945_, v_val_4965_);
lean_dec(v_val_4965_);
v___x_4972_ = lean_unsigned_to_nat(1u);
v___x_4973_ = lean_mk_empty_array_with_capacity(v___x_4972_);
lean_inc(v___x_4971_);
v___x_4974_ = lean_array_push(v___x_4973_, v___x_4971_);
v___x_4975_ = l_Lean_Meta_instantiateLambda(v_x_4947_, v___x_4974_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_);
lean_dec_ref(v___x_4974_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
lean_dec_ref(v___x_4975_);
v_x_4946_ = v_tail_4964_;
v_x_4947_ = v_a_4976_;
goto _start;
}
else
{
lean_dec(v_tail_4964_);
lean_dec_ref(v_xs_4945_);
return v___x_4975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4978_, lean_object* v_xs_4979_, lean_object* v_tail_4980_, uint8_t v___x_4981_, uint8_t v___x_4982_, lean_object* v_ys_4983_, lean_object* v_value_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_){
_start:
{
lean_object* v___x_4990_; uint8_t v___x_4991_; 
v___x_4990_ = lean_array_get_size(v_ys_4983_);
v___x_4991_ = lean_nat_dec_eq(v___x_4990_, v___x_4978_);
if (v___x_4991_ == 0)
{
lean_object* v___x_4992_; lean_object* v___x_4993_; 
lean_dec_ref(v_value_4984_);
lean_dec(v_tail_4980_);
lean_dec_ref(v_xs_4979_);
v___x_4992_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4993_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4992_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
return v___x_4993_;
}
else
{
lean_object* v___x_4994_; 
v___x_4994_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4979_, v_tail_4980_, v_value_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v_a_4995_; uint8_t v___x_4996_; lean_object* v___x_4997_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_a_4995_);
lean_dec_ref(v___x_4994_);
v___x_4996_ = 1;
v___x_4997_ = l_Lean_Meta_mkLambdaFVars(v_ys_4983_, v_a_4995_, v___x_4981_, v___x_4982_, v___x_4981_, v___x_4982_, v___x_4996_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
return v___x_4997_;
}
else
{
return v___x_4994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4998_, lean_object* v_x_4999_, lean_object* v_x_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4998_, v_x_4999_, v_x_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_);
lean_dec(v_a_5004_);
lean_dec_ref(v_a_5003_);
lean_dec(v_a_5002_);
lean_dec_ref(v_a_5001_);
return v_res_5006_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5008_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5009_ = lean_unsigned_to_nat(2u);
v___x_5010_ = lean_unsigned_to_nat(362u);
v___x_5011_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5012_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5013_ = l_mkPanicMessageWithDecl(v___x_5012_, v___x_5011_, v___x_5010_, v___x_5009_, v___x_5008_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5014_, lean_object* v_value_u2080_5015_, lean_object* v_xs_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; uint8_t v___x_5024_; 
v___x_5022_ = lean_array_get_size(v_xs_5016_);
v___x_5023_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5014_);
v___x_5024_ = lean_nat_dec_eq(v___x_5022_, v___x_5023_);
lean_dec(v___x_5023_);
if (v___x_5024_ == 0)
{
lean_object* v___x_5025_; lean_object* v___x_5026_; 
lean_dec_ref(v_xs_5016_);
lean_dec_ref(v_value_u2080_5015_);
lean_dec_ref(v_perm_5014_);
v___x_5025_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5026_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5025_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
return v___x_5026_;
}
else
{
lean_object* v_mask_5027_; lean_object* v___x_5028_; 
v_mask_5027_ = lean_array_to_list(v_perm_5014_);
v___x_5028_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5016_, v_mask_5027_, v_value_u2080_5015_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_);
return v___x_5028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5029_, lean_object* v_value_u2080_5030_, lean_object* v_xs_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5029_, v_value_u2080_5030_, v_xs_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
lean_dec(v_a_5035_);
lean_dec_ref(v_a_5034_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
return v_res_5037_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5045_; 
v___x_5045_ = l_Array_instInhabited(lean_box(0));
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5046_){
_start:
{
lean_object* v___f_5047_; lean_object* v___f_5048_; lean_object* v___f_5049_; lean_object* v___f_5050_; lean_object* v___f_5051_; lean_object* v___f_5052_; lean_object* v___f_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___f_5047_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5048_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5049_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5050_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5051_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5052_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5053_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5054_, 0, v___f_5047_);
lean_ctor_set(v___x_5054_, 1, v___f_5048_);
v___x_5055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5055_, 0, v___x_5054_);
lean_ctor_set(v___x_5055_, 1, v___f_5049_);
lean_ctor_set(v___x_5055_, 2, v___f_5050_);
lean_ctor_set(v___x_5055_, 3, v___f_5051_);
lean_ctor_set(v___x_5055_, 4, v___f_5052_);
v___x_5056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5055_);
lean_ctor_set(v___x_5056_, 1, v___f_5053_);
v___x_5057_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5058_ = l_instInhabitedOfMonad___redArg(v___x_5056_, v___x_5057_);
v___x_5059_ = lean_panic_fn_borrowed(v___x_5058_, v_msg_5046_);
lean_dec(v___x_5058_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5060_, lean_object* v_msg_5061_){
_start:
{
lean_object* v___x_5062_; 
v___x_5062_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5061_);
return v___x_5062_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5065_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5066_ = lean_unsigned_to_nat(8u);
v___x_5067_ = lean_unsigned_to_nat(394u);
v___x_5068_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5069_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5070_ = l_mkPanicMessageWithDecl(v___x_5069_, v___x_5068_, v___x_5067_, v___x_5066_, v___x_5065_);
return v___x_5070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5071_, lean_object* v_x_5072_){
_start:
{
if (lean_obj_tag(v_x_5071_) == 0)
{
return v_x_5072_;
}
else
{
lean_object* v_head_5073_; lean_object* v_fst_5074_; 
v_head_5073_ = lean_ctor_get(v_x_5071_, 0);
v_fst_5074_ = lean_ctor_get(v_head_5073_, 0);
if (lean_obj_tag(v_fst_5074_) == 0)
{
lean_object* v_tail_5075_; 
v_tail_5075_ = lean_ctor_get(v_x_5071_, 1);
lean_inc(v_tail_5075_);
lean_dec_ref(v_x_5071_);
v_x_5071_ = v_tail_5075_;
goto _start;
}
else
{
lean_object* v_tail_5077_; lean_object* v_snd_5078_; lean_object* v_val_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; 
lean_inc_ref(v_fst_5074_);
lean_inc(v_head_5073_);
v_tail_5077_ = lean_ctor_get(v_x_5071_, 1);
lean_inc(v_tail_5077_);
lean_dec_ref(v_x_5071_);
v_snd_5078_ = lean_ctor_get(v_head_5073_, 1);
lean_inc(v_snd_5078_);
lean_dec(v_head_5073_);
v_val_5079_ = lean_ctor_get(v_fst_5074_, 0);
lean_inc(v_val_5079_);
lean_dec_ref(v_fst_5074_);
v___x_5080_ = lean_array_get_size(v_x_5072_);
v___x_5081_ = lean_nat_dec_lt(v_val_5079_, v___x_5080_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
lean_dec(v_val_5079_);
lean_dec(v_snd_5078_);
lean_dec(v_tail_5077_);
lean_dec_ref(v_x_5072_);
v___x_5082_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5083_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5082_);
return v___x_5083_;
}
else
{
lean_object* v___x_5084_; 
v___x_5084_ = lean_array_set(v_x_5072_, v_val_5079_, v_snd_5078_);
lean_dec(v_val_5079_);
v_x_5071_ = v_tail_5077_;
v_x_5072_ = v___x_5084_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5086_, lean_object* v_x_5087_, lean_object* v_x_5088_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5087_, v_x_5088_);
return v___x_5089_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5092_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5093_ = lean_unsigned_to_nat(2u);
v___x_5094_ = lean_unsigned_to_nat(384u);
v___x_5095_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5096_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5097_ = l_mkPanicMessageWithDecl(v___x_5096_, v___x_5095_, v___x_5094_, v___x_5093_, v___x_5092_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5100_, lean_object* v_xs_5101_){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
v___x_5102_ = lean_array_get_size(v_xs_5101_);
v___x_5103_ = lean_array_get_size(v_perm_5100_);
v___x_5104_ = lean_nat_dec_eq(v___x_5102_, v___x_5103_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5105_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5106_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5105_);
return v___x_5106_;
}
else
{
lean_object* v___x_5107_; uint8_t v___x_5108_; 
v___x_5107_ = lean_unsigned_to_nat(0u);
v___x_5108_ = lean_nat_dec_eq(v___x_5102_, v___x_5107_);
if (v___x_5108_ == 0)
{
lean_object* v_dummy_5109_; lean_object* v___x_5110_; lean_object* v_ys_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
v_dummy_5109_ = lean_array_fget_borrowed(v_xs_5101_, v___x_5107_);
v___x_5110_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5100_);
lean_inc(v_dummy_5109_);
v_ys_5111_ = lean_mk_array(v___x_5110_, v_dummy_5109_);
v___x_5112_ = l_Array_zip___redArg(v_perm_5100_, v_xs_5101_);
v___x_5113_ = lean_array_to_list(v___x_5112_);
v___x_5114_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5113_, v_ys_5111_);
return v___x_5114_;
}
else
{
lean_object* v___x_5115_; 
v___x_5115_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5116_, lean_object* v_xs_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5116_, v_xs_5117_);
lean_dec_ref(v_xs_5117_);
lean_dec_ref(v_perm_5116_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5119_, lean_object* v_perm_5120_, lean_object* v_xs_5121_){
_start:
{
lean_object* v___x_5122_; 
v___x_5122_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5120_, v_xs_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5123_, lean_object* v_perm_5124_, lean_object* v_xs_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5123_, v_perm_5124_, v_xs_5125_);
lean_dec_ref(v_xs_5125_);
lean_dec_ref(v_perm_5124_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5127_, lean_object* v_upperBound_5128_, lean_object* v_perm_5129_, lean_object* v_a_5130_, lean_object* v_b_5131_){
_start:
{
lean_object* v_a_5133_; uint8_t v___x_5140_; 
v___x_5140_ = lean_nat_dec_lt(v_a_5130_, v_upperBound_5128_);
if (v___x_5140_ == 0)
{
lean_dec(v_a_5130_);
return v_b_5131_;
}
else
{
lean_object* v___x_5141_; uint8_t v___x_5142_; 
v___x_5141_ = lean_array_get_size(v_perm_5129_);
v___x_5142_ = lean_nat_dec_lt(v_a_5130_, v___x_5141_);
if (v___x_5142_ == 0)
{
goto v___jp_5137_;
}
else
{
lean_object* v___x_5143_; 
v___x_5143_ = lean_array_fget_borrowed(v_perm_5129_, v_a_5130_);
if (lean_obj_tag(v___x_5143_) == 0)
{
goto v___jp_5137_;
}
else
{
v_a_5133_ = v_b_5131_;
goto v___jp_5132_;
}
}
}
v___jp_5132_:
{
lean_object* v___x_5134_; lean_object* v___x_5135_; 
v___x_5134_ = lean_unsigned_to_nat(1u);
v___x_5135_ = lean_nat_add(v_a_5130_, v___x_5134_);
lean_dec(v_a_5130_);
v_a_5130_ = v___x_5135_;
v_b_5131_ = v_a_5133_;
goto _start;
}
v___jp_5137_:
{
lean_object* v___x_5138_; lean_object* v___x_5139_; 
v___x_5138_ = lean_array_fget_borrowed(v_xs_5127_, v_a_5130_);
lean_inc(v___x_5138_);
v___x_5139_ = lean_array_push(v_b_5131_, v___x_5138_);
v_a_5133_ = v___x_5139_;
goto v___jp_5132_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5144_, lean_object* v_upperBound_5145_, lean_object* v_perm_5146_, lean_object* v_a_5147_, lean_object* v_b_5148_){
_start:
{
lean_object* v_res_5149_; 
v_res_5149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5144_, v_upperBound_5145_, v_perm_5146_, v_a_5147_, v_b_5148_);
lean_dec_ref(v_perm_5146_);
lean_dec(v_upperBound_5145_);
lean_dec_ref(v_xs_5144_);
return v_res_5149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5150_, lean_object* v_xs_5151_){
_start:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v_ys_5154_; lean_object* v___x_5155_; 
v___x_5152_ = lean_array_get_size(v_xs_5151_);
v___x_5153_ = lean_unsigned_to_nat(0u);
v_ys_5154_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5155_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5151_, v___x_5152_, v_perm_5150_, v___x_5153_, v_ys_5154_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5156_, lean_object* v_xs_5157_){
_start:
{
lean_object* v_res_5158_; 
v_res_5158_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5156_, v_xs_5157_);
lean_dec_ref(v_xs_5157_);
lean_dec_ref(v_perm_5156_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5159_, lean_object* v_perm_5160_, lean_object* v_xs_5161_){
_start:
{
lean_object* v___x_5162_; 
v___x_5162_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5160_, v_xs_5161_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5163_, lean_object* v_perm_5164_, lean_object* v_xs_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5163_, v_perm_5164_, v_xs_5165_);
lean_dec_ref(v_xs_5165_);
lean_dec_ref(v_perm_5164_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5167_, lean_object* v_xs_5168_, lean_object* v_upperBound_5169_, lean_object* v_perm_5170_, lean_object* v_inst_5171_, lean_object* v_R_5172_, lean_object* v_a_5173_, lean_object* v_b_5174_, lean_object* v_c_5175_){
_start:
{
lean_object* v___x_5176_; 
v___x_5176_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5168_, v_upperBound_5169_, v_perm_5170_, v_a_5173_, v_b_5174_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5177_, lean_object* v_xs_5178_, lean_object* v_upperBound_5179_, lean_object* v_perm_5180_, lean_object* v_inst_5181_, lean_object* v_R_5182_, lean_object* v_a_5183_, lean_object* v_b_5184_, lean_object* v_c_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5177_, v_xs_5178_, v_upperBound_5179_, v_perm_5180_, v_inst_5181_, v_R_5182_, v_a_5183_, v_b_5184_, v_c_5185_);
lean_dec_ref(v_perm_5180_);
lean_dec(v_upperBound_5179_);
lean_dec_ref(v_xs_5178_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object* v_msg_5187_){
_start:
{
lean_object* v___x_5188_; lean_object* v___x_5189_; 
v___x_5188_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5189_ = lean_panic_fn_borrowed(v___x_5188_, v_msg_5187_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_00_u03b1_5190_, lean_object* v_msg_5191_){
_start:
{
lean_object* v___x_5192_; 
v___x_5192_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v_msg_5191_);
return v___x_5192_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_as_5193_, size_t v_i_5194_, size_t v_stop_5195_){
_start:
{
uint8_t v___x_5196_; 
v___x_5196_ = lean_usize_dec_eq(v_i_5194_, v_stop_5195_);
if (v___x_5196_ == 0)
{
uint8_t v___x_5197_; lean_object* v___x_5198_; 
v___x_5197_ = 1;
v___x_5198_ = lean_array_uget_borrowed(v_as_5193_, v_i_5194_);
if (lean_obj_tag(v___x_5198_) == 0)
{
if (v___x_5196_ == 0)
{
size_t v___x_5199_; size_t v___x_5200_; 
v___x_5199_ = ((size_t)1ULL);
v___x_5200_ = lean_usize_add(v_i_5194_, v___x_5199_);
v_i_5194_ = v___x_5200_;
goto _start;
}
else
{
return v___x_5197_;
}
}
else
{
return v___x_5197_;
}
}
else
{
uint8_t v___x_5202_; 
v___x_5202_ = 0;
return v___x_5202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object* v_as_5203_, lean_object* v_i_5204_, lean_object* v_stop_5205_){
_start:
{
size_t v_i_boxed_5206_; size_t v_stop_boxed_5207_; uint8_t v_res_5208_; lean_object* v_r_5209_; 
v_i_boxed_5206_ = lean_unbox_usize(v_i_5204_);
lean_dec(v_i_5204_);
v_stop_boxed_5207_ = lean_unbox_usize(v_stop_5205_);
lean_dec(v_stop_5205_);
v_res_5208_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v_as_5203_, v_i_boxed_5206_, v_stop_boxed_5207_);
lean_dec_ref(v_as_5203_);
v_r_5209_ = lean_box(v_res_5208_);
return v_r_5209_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5212_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5213_ = lean_unsigned_to_nat(12u);
v___x_5214_ = lean_unsigned_to_nat(433u);
v___x_5215_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5216_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5217_ = l_mkPanicMessageWithDecl(v___x_5216_, v___x_5215_, v___x_5214_, v___x_5213_, v___x_5212_);
return v___x_5217_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5219_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5220_ = lean_unsigned_to_nat(10u);
v___x_5221_ = lean_unsigned_to_nat(425u);
v___x_5222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5223_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5224_ = l_mkPanicMessageWithDecl(v___x_5223_, v___x_5222_, v___x_5221_, v___x_5220_, v___x_5219_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5225_, lean_object* v_fixedArgs_5226_, lean_object* v_varyingArgs_5227_, lean_object* v_i_5228_, lean_object* v_j_5229_, lean_object* v_xs_5230_){
_start:
{
lean_object* v_lower_5232_; lean_object* v_upper_5233_; lean_object* v___y_5238_; lean_object* v___y_5239_; lean_object* v___y_5240_; lean_object* v_lower_5248_; lean_object* v_upper_5249_; lean_object* v___x_5257_; uint8_t v___x_5258_; 
v___x_5257_ = lean_array_get_size(v_perm_5225_);
v___x_5258_ = lean_nat_dec_lt(v_i_5228_, v___x_5257_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; lean_object* v___x_5260_; uint8_t v___x_5261_; 
lean_dec(v_i_5228_);
lean_dec_ref(v_perm_5225_);
v___x_5259_ = lean_unsigned_to_nat(0u);
v___x_5260_ = lean_array_get_size(v_varyingArgs_5227_);
v___x_5261_ = lean_nat_dec_le(v_j_5229_, v___x_5259_);
if (v___x_5261_ == 0)
{
v_lower_5232_ = v_j_5229_;
v_upper_5233_ = v___x_5260_;
goto v___jp_5231_;
}
else
{
lean_dec(v_j_5229_);
v_lower_5232_ = v___x_5259_;
v_upper_5233_ = v___x_5260_;
goto v___jp_5231_;
}
}
else
{
lean_object* v___x_5262_; 
v___x_5262_ = lean_array_fget_borrowed(v_perm_5225_, v_i_5228_);
if (lean_obj_tag(v___x_5262_) == 1)
{
lean_object* v_val_5263_; lean_object* v___x_5264_; uint8_t v___x_5265_; 
v_val_5263_ = lean_ctor_get(v___x_5262_, 0);
v___x_5264_ = lean_array_get_size(v_fixedArgs_5226_);
v___x_5265_ = lean_nat_dec_lt(v_val_5263_, v___x_5264_);
if (v___x_5265_ == 0)
{
lean_object* v___x_5266_; lean_object* v___x_5267_; 
lean_dec_ref(v_xs_5230_);
lean_dec(v_j_5229_);
lean_dec(v_i_5228_);
lean_dec_ref(v_varyingArgs_5227_);
lean_dec_ref(v_perm_5225_);
v___x_5266_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5267_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5266_);
return v___x_5267_;
}
else
{
lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; 
v___x_5268_ = lean_unsigned_to_nat(1u);
v___x_5269_ = lean_nat_add(v_i_5228_, v___x_5268_);
lean_dec(v_i_5228_);
v___x_5270_ = lean_array_fget_borrowed(v_fixedArgs_5226_, v_val_5263_);
lean_inc(v___x_5270_);
v___x_5271_ = lean_array_push(v_xs_5230_, v___x_5270_);
v_i_5228_ = v___x_5269_;
v_xs_5230_ = v___x_5271_;
goto _start;
}
}
else
{
lean_object* v___x_5273_; uint8_t v___x_5274_; 
v___x_5273_ = lean_array_get_size(v_varyingArgs_5227_);
v___x_5274_ = lean_nat_dec_lt(v_j_5229_, v___x_5273_);
if (v___x_5274_ == 0)
{
lean_object* v___x_5275_; uint8_t v___x_5276_; 
lean_dec(v_j_5229_);
lean_dec_ref(v_varyingArgs_5227_);
v___x_5275_ = lean_unsigned_to_nat(0u);
v___x_5276_ = lean_nat_dec_le(v_i_5228_, v___x_5275_);
if (v___x_5276_ == 0)
{
v_lower_5248_ = v_i_5228_;
v_upper_5249_ = v___x_5257_;
goto v___jp_5247_;
}
else
{
lean_dec(v_i_5228_);
v_lower_5248_ = v___x_5275_;
v_upper_5249_ = v___x_5257_;
goto v___jp_5247_;
}
}
else
{
lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5277_ = lean_unsigned_to_nat(1u);
v___x_5278_ = lean_nat_add(v_i_5228_, v___x_5277_);
lean_dec(v_i_5228_);
v___x_5279_ = lean_nat_add(v_j_5229_, v___x_5277_);
v___x_5280_ = lean_array_fget_borrowed(v_varyingArgs_5227_, v_j_5229_);
lean_dec(v_j_5229_);
lean_inc(v___x_5280_);
v___x_5281_ = lean_array_push(v_xs_5230_, v___x_5280_);
v_i_5228_ = v___x_5278_;
v_j_5229_ = v___x_5279_;
v_xs_5230_ = v___x_5281_;
goto _start;
}
}
}
v___jp_5231_:
{
lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5234_ = l_Array_toSubarray___redArg(v_varyingArgs_5227_, v_lower_5232_, v_upper_5233_);
v___x_5235_ = l_Subarray_copy___redArg(v___x_5234_);
v___x_5236_ = l_Array_append___redArg(v_xs_5230_, v___x_5235_);
lean_dec_ref(v___x_5235_);
return v___x_5236_;
}
v___jp_5237_:
{
uint8_t v___x_5241_; 
v___x_5241_ = lean_nat_dec_lt(v___y_5238_, v___y_5240_);
if (v___x_5241_ == 0)
{
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
lean_dec(v___y_5238_);
return v_xs_5230_;
}
else
{
size_t v___x_5242_; size_t v___x_5243_; uint8_t v___x_5244_; 
v___x_5242_ = lean_usize_of_nat(v___y_5238_);
lean_dec(v___y_5238_);
v___x_5243_ = lean_usize_of_nat(v___y_5240_);
lean_dec(v___y_5240_);
v___x_5244_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v___y_5239_, v___x_5242_, v___x_5243_);
lean_dec_ref(v___y_5239_);
if (v___x_5244_ == 0)
{
return v_xs_5230_;
}
else
{
lean_object* v___x_5245_; lean_object* v___x_5246_; 
lean_dec_ref(v_xs_5230_);
v___x_5245_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5246_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5245_);
return v___x_5246_;
}
}
}
v___jp_5247_:
{
lean_object* v___x_5250_; lean_object* v_array_5251_; lean_object* v_start_5252_; lean_object* v_stop_5253_; uint8_t v___x_5254_; 
v___x_5250_ = l_Array_toSubarray___redArg(v_perm_5225_, v_lower_5248_, v_upper_5249_);
v_array_5251_ = lean_ctor_get(v___x_5250_, 0);
lean_inc_ref(v_array_5251_);
v_start_5252_ = lean_ctor_get(v___x_5250_, 1);
lean_inc(v_start_5252_);
v_stop_5253_ = lean_ctor_get(v___x_5250_, 2);
lean_inc(v_stop_5253_);
lean_dec_ref(v___x_5250_);
v___x_5254_ = lean_nat_dec_lt(v_start_5252_, v_stop_5253_);
if (v___x_5254_ == 0)
{
lean_dec(v_stop_5253_);
lean_dec(v_start_5252_);
lean_dec_ref(v_array_5251_);
return v_xs_5230_;
}
else
{
lean_object* v___x_5255_; uint8_t v___x_5256_; 
v___x_5255_ = lean_array_get_size(v_array_5251_);
v___x_5256_ = lean_nat_dec_le(v_stop_5253_, v___x_5255_);
if (v___x_5256_ == 0)
{
lean_dec(v_stop_5253_);
v___y_5238_ = v_start_5252_;
v___y_5239_ = v_array_5251_;
v___y_5240_ = v___x_5255_;
goto v___jp_5237_;
}
else
{
v___y_5238_ = v_start_5252_;
v___y_5239_ = v_array_5251_;
v___y_5240_ = v_stop_5253_;
goto v___jp_5237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5283_, lean_object* v_fixedArgs_5284_, lean_object* v_varyingArgs_5285_, lean_object* v_i_5286_, lean_object* v_j_5287_, lean_object* v_xs_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5283_, v_fixedArgs_5284_, v_varyingArgs_5285_, v_i_5286_, v_j_5287_, v_xs_5288_);
lean_dec_ref(v_fixedArgs_5284_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5290_, lean_object* v_perm_5291_, lean_object* v_fixedArgs_5292_, lean_object* v_varyingArgs_5293_, lean_object* v_i_5294_, lean_object* v_j_5295_, lean_object* v_xs_5296_){
_start:
{
lean_object* v___x_5297_; 
v___x_5297_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5291_, v_fixedArgs_5292_, v_varyingArgs_5293_, v_i_5294_, v_j_5295_, v_xs_5296_);
return v___x_5297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5298_, lean_object* v_perm_5299_, lean_object* v_fixedArgs_5300_, lean_object* v_varyingArgs_5301_, lean_object* v_i_5302_, lean_object* v_j_5303_, lean_object* v_xs_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5298_, v_perm_5299_, v_fixedArgs_5300_, v_varyingArgs_5301_, v_i_5302_, v_j_5303_, v_xs_5304_);
lean_dec_ref(v_fixedArgs_5300_);
return v_res_5305_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5308_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5309_ = lean_unsigned_to_nat(2u);
v___x_5310_ = lean_unsigned_to_nat(416u);
v___x_5311_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5312_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5313_ = l_mkPanicMessageWithDecl(v___x_5312_, v___x_5311_, v___x_5310_, v___x_5309_, v___x_5308_);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5314_, lean_object* v_fixedArgs_5315_, lean_object* v_varyingArgs_5316_){
_start:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; uint8_t v___x_5319_; 
v___x_5317_ = lean_array_get_size(v_fixedArgs_5315_);
v___x_5318_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5314_);
v___x_5319_ = lean_nat_dec_eq(v___x_5317_, v___x_5318_);
lean_dec(v___x_5318_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; lean_object* v___x_5321_; 
lean_dec_ref(v_varyingArgs_5316_);
lean_dec_ref(v_perm_5314_);
v___x_5320_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5321_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5320_);
return v___x_5321_;
}
else
{
lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___x_5322_ = lean_unsigned_to_nat(0u);
v___x_5323_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5324_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5314_, v_fixedArgs_5315_, v_varyingArgs_5316_, v___x_5322_, v___x_5322_, v___x_5323_);
return v___x_5324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5325_, lean_object* v_fixedArgs_5326_, lean_object* v_varyingArgs_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5325_, v_fixedArgs_5326_, v_varyingArgs_5327_);
lean_dec_ref(v_fixedArgs_5326_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5329_, lean_object* v_perm_5330_, lean_object* v_fixedArgs_5331_, lean_object* v_varyingArgs_5332_){
_start:
{
lean_object* v___x_5333_; 
v___x_5333_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5330_, v_fixedArgs_5331_, v_varyingArgs_5332_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5334_, lean_object* v_perm_5335_, lean_object* v_fixedArgs_5336_, lean_object* v_varyingArgs_5337_){
_start:
{
lean_object* v_res_5338_; 
v_res_5338_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5334_, v_perm_5335_, v_fixedArgs_5336_, v_varyingArgs_5337_);
lean_dec_ref(v_fixedArgs_5336_);
return v_res_5338_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5339_, lean_object* v_x_5340_){
_start:
{
if (lean_obj_tag(v_x_5339_) == 0)
{
if (lean_obj_tag(v_x_5340_) == 0)
{
uint8_t v___x_5341_; 
v___x_5341_ = 1;
return v___x_5341_;
}
else
{
uint8_t v___x_5342_; 
v___x_5342_ = 0;
return v___x_5342_;
}
}
else
{
if (lean_obj_tag(v_x_5340_) == 0)
{
uint8_t v___x_5343_; 
v___x_5343_ = 0;
return v___x_5343_;
}
else
{
lean_object* v_val_5344_; lean_object* v_val_5345_; uint8_t v___x_5346_; 
v_val_5344_ = lean_ctor_get(v_x_5339_, 0);
v_val_5345_ = lean_ctor_get(v_x_5340_, 0);
v___x_5346_ = lean_nat_dec_eq(v_val_5344_, v_val_5345_);
return v___x_5346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5347_, lean_object* v_x_5348_){
_start:
{
uint8_t v_res_5349_; lean_object* v_r_5350_; 
v_res_5349_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5347_, v_x_5348_);
lean_dec(v_x_5348_);
lean_dec(v_x_5347_);
v_r_5350_ = lean_box(v_res_5349_);
return v_r_5350_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5351_, lean_object* v_ys_5352_, lean_object* v_x_5353_){
_start:
{
lean_object* v_zero_5354_; uint8_t v_isZero_5355_; 
v_zero_5354_ = lean_unsigned_to_nat(0u);
v_isZero_5355_ = lean_nat_dec_eq(v_x_5353_, v_zero_5354_);
if (v_isZero_5355_ == 1)
{
lean_dec(v_x_5353_);
return v_isZero_5355_;
}
else
{
lean_object* v_one_5356_; lean_object* v_n_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; uint8_t v___x_5360_; 
v_one_5356_ = lean_unsigned_to_nat(1u);
v_n_5357_ = lean_nat_sub(v_x_5353_, v_one_5356_);
lean_dec(v_x_5353_);
v___x_5358_ = lean_array_fget_borrowed(v_xs_5351_, v_n_5357_);
v___x_5359_ = lean_array_fget_borrowed(v_ys_5352_, v_n_5357_);
v___x_5360_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5358_, v___x_5359_);
if (v___x_5360_ == 0)
{
lean_dec(v_n_5357_);
return v___x_5360_;
}
else
{
v_x_5353_ = v_n_5357_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5362_, lean_object* v_ys_5363_, lean_object* v_x_5364_){
_start:
{
uint8_t v_res_5365_; lean_object* v_r_5366_; 
v_res_5365_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5362_, v_ys_5363_, v_x_5364_);
lean_dec_ref(v_ys_5363_);
lean_dec_ref(v_xs_5362_);
v_r_5366_ = lean_box(v_res_5365_);
return v_r_5366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5367_, size_t v_i_5368_, lean_object* v_bs_5369_){
_start:
{
uint8_t v___x_5370_; 
v___x_5370_ = lean_usize_dec_lt(v_i_5368_, v_sz_5367_);
if (v___x_5370_ == 0)
{
return v_bs_5369_;
}
else
{
lean_object* v_v_5371_; lean_object* v___x_5372_; lean_object* v_bs_x27_5373_; lean_object* v___x_5374_; size_t v___x_5375_; size_t v___x_5376_; lean_object* v___x_5377_; 
v_v_5371_ = lean_array_uget(v_bs_5369_, v_i_5368_);
v___x_5372_ = lean_unsigned_to_nat(0u);
v_bs_x27_5373_ = lean_array_uset(v_bs_5369_, v_i_5368_, v___x_5372_);
v___x_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5374_, 0, v_v_5371_);
v___x_5375_ = ((size_t)1ULL);
v___x_5376_ = lean_usize_add(v_i_5368_, v___x_5375_);
v___x_5377_ = lean_array_uset(v_bs_x27_5373_, v_i_5368_, v___x_5374_);
v_i_5368_ = v___x_5376_;
v_bs_5369_ = v___x_5377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5379_, lean_object* v_i_5380_, lean_object* v_bs_5381_){
_start:
{
size_t v_sz_boxed_5382_; size_t v_i_boxed_5383_; lean_object* v_res_5384_; 
v_sz_boxed_5382_ = lean_unbox_usize(v_sz_5379_);
lean_dec(v_sz_5379_);
v_i_boxed_5383_ = lean_unbox_usize(v_i_5380_);
lean_dec(v_i_5380_);
v_res_5384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5382_, v_i_boxed_5383_, v_bs_5381_);
return v_res_5384_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5385_, lean_object* v_as_5386_, size_t v_i_5387_, size_t v_stop_5388_){
_start:
{
uint8_t v___x_5389_; 
v___x_5389_ = lean_usize_dec_eq(v_i_5387_, v_stop_5388_);
if (v___x_5389_ == 0)
{
lean_object* v_numFixed_5390_; uint8_t v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; size_t v_sz_5394_; size_t v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; uint8_t v___x_5403_; 
v_numFixed_5390_ = lean_ctor_get(v_fixedParamPerms_5385_, 0);
v___x_5391_ = 1;
v___x_5392_ = lean_array_uget_borrowed(v_as_5386_, v_i_5387_);
lean_inc(v_numFixed_5390_);
v___x_5393_ = l_Array_range(v_numFixed_5390_);
v_sz_5394_ = lean_array_size(v___x_5393_);
v___x_5395_ = ((size_t)0ULL);
v___x_5396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5394_, v___x_5395_, v___x_5393_);
v___x_5397_ = lean_array_get_size(v___x_5392_);
v___x_5398_ = lean_nat_sub(v___x_5397_, v_numFixed_5390_);
v___x_5399_ = lean_box(0);
v___x_5400_ = lean_mk_array(v___x_5398_, v___x_5399_);
v___x_5401_ = l_Array_append___redArg(v___x_5396_, v___x_5400_);
lean_dec_ref(v___x_5400_);
v___x_5402_ = lean_array_get_size(v___x_5401_);
v___x_5403_ = lean_nat_dec_eq(v___x_5397_, v___x_5402_);
if (v___x_5403_ == 0)
{
lean_dec_ref(v___x_5401_);
lean_dec_ref(v_fixedParamPerms_5385_);
return v___x_5391_;
}
else
{
uint8_t v___x_5404_; 
v___x_5404_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5392_, v___x_5401_, v___x_5397_);
lean_dec_ref(v___x_5401_);
if (v___x_5404_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5385_);
return v___x_5391_;
}
else
{
if (v___x_5389_ == 0)
{
size_t v___x_5405_; size_t v___x_5406_; 
v___x_5405_ = ((size_t)1ULL);
v___x_5406_ = lean_usize_add(v_i_5387_, v___x_5405_);
v_i_5387_ = v___x_5406_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5385_);
return v___x_5391_;
}
}
}
}
else
{
uint8_t v___x_5408_; 
lean_dec_ref(v_fixedParamPerms_5385_);
v___x_5408_ = 0;
return v___x_5408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5409_, lean_object* v_as_5410_, lean_object* v_i_5411_, lean_object* v_stop_5412_){
_start:
{
size_t v_i_boxed_5413_; size_t v_stop_boxed_5414_; uint8_t v_res_5415_; lean_object* v_r_5416_; 
v_i_boxed_5413_ = lean_unbox_usize(v_i_5411_);
lean_dec(v_i_5411_);
v_stop_boxed_5414_ = lean_unbox_usize(v_stop_5412_);
lean_dec(v_stop_5412_);
v_res_5415_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5409_, v_as_5410_, v_i_boxed_5413_, v_stop_boxed_5414_);
lean_dec_ref(v_as_5410_);
v_r_5416_ = lean_box(v_res_5415_);
return v_r_5416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5417_){
_start:
{
lean_object* v_perms_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; uint8_t v___x_5421_; 
v_perms_5418_ = lean_ctor_get(v_fixedParamPerms_5417_, 1);
lean_inc_ref(v_perms_5418_);
v___x_5419_ = lean_unsigned_to_nat(0u);
v___x_5420_ = lean_array_get_size(v_perms_5418_);
v___x_5421_ = lean_nat_dec_lt(v___x_5419_, v___x_5420_);
if (v___x_5421_ == 0)
{
uint8_t v___x_5422_; 
lean_dec_ref(v_perms_5418_);
lean_dec_ref(v_fixedParamPerms_5417_);
v___x_5422_ = 1;
return v___x_5422_;
}
else
{
if (v___x_5421_ == 0)
{
lean_dec_ref(v_perms_5418_);
lean_dec_ref(v_fixedParamPerms_5417_);
return v___x_5421_;
}
else
{
size_t v___x_5423_; size_t v___x_5424_; uint8_t v___x_5425_; 
v___x_5423_ = ((size_t)0ULL);
v___x_5424_ = lean_usize_of_nat(v___x_5420_);
v___x_5425_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5417_, v_perms_5418_, v___x_5423_, v___x_5424_);
lean_dec_ref(v_perms_5418_);
if (v___x_5425_ == 0)
{
return v___x_5421_;
}
else
{
uint8_t v___x_5426_; 
v___x_5426_ = 0;
return v___x_5426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5427_){
_start:
{
uint8_t v_res_5428_; lean_object* v_r_5429_; 
v_res_5428_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5427_);
v_r_5429_ = lean_box(v_res_5428_);
return v_r_5429_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5430_, lean_object* v_ys_5431_, lean_object* v_hsz_5432_, lean_object* v_x_5433_, lean_object* v_x_5434_){
_start:
{
uint8_t v___x_5435_; 
v___x_5435_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5430_, v_ys_5431_, v_x_5433_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5436_, lean_object* v_ys_5437_, lean_object* v_hsz_5438_, lean_object* v_x_5439_, lean_object* v_x_5440_){
_start:
{
uint8_t v_res_5441_; lean_object* v_r_5442_; 
v_res_5441_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5436_, v_ys_5437_, v_hsz_5438_, v_x_5439_, v_x_5440_);
lean_dec_ref(v_ys_5437_);
lean_dec_ref(v_xs_5436_);
v_r_5442_ = lean_box(v_res_5441_);
return v_r_5442_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5443_; 
v___x_5443_ = l_Array_instInhabited(lean_box(0));
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5444_){
_start:
{
lean_object* v___f_5445_; lean_object* v___f_5446_; lean_object* v___f_5447_; lean_object* v___f_5448_; lean_object* v___f_5449_; lean_object* v___f_5450_; lean_object* v___f_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___f_5445_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5446_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5447_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5448_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5449_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5450_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5451_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5452_, 0, v___f_5445_);
lean_ctor_set(v___x_5452_, 1, v___f_5446_);
v___x_5453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5453_, 0, v___x_5452_);
lean_ctor_set(v___x_5453_, 1, v___f_5447_);
lean_ctor_set(v___x_5453_, 2, v___f_5448_);
lean_ctor_set(v___x_5453_, 3, v___f_5449_);
lean_ctor_set(v___x_5453_, 4, v___f_5450_);
v___x_5454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5454_, 0, v___x_5453_);
lean_ctor_set(v___x_5454_, 1, v___f_5451_);
v___x_5455_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5456_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5456_);
lean_ctor_set(v___x_5457_, 1, v___x_5456_);
v___x_5458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5458_, 0, v___x_5455_);
lean_ctor_set(v___x_5458_, 1, v___x_5457_);
v___x_5459_ = l_instInhabitedOfMonad___redArg(v___x_5454_, v___x_5458_);
v___x_5460_ = lean_panic_fn_borrowed(v___x_5459_, v_msg_5444_);
lean_dec(v___x_5459_);
return v___x_5460_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5461_; 
v___x_5461_ = l_Array_instInhabited(lean_box(0));
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5462_){
_start:
{
lean_object* v___f_5463_; lean_object* v___f_5464_; lean_object* v___f_5465_; lean_object* v___f_5466_; lean_object* v___f_5467_; lean_object* v___f_5468_; lean_object* v___f_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; 
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
v___x_5473_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5473_);
v___x_5475_ = l_instInhabitedOfMonad___redArg(v___x_5472_, v___x_5474_);
v___x_5476_ = lean_panic_fn_borrowed(v___x_5475_, v_msg_5462_);
lean_dec(v___x_5475_);
return v___x_5476_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5477_, lean_object* v_a_5478_, lean_object* v_b_5479_){
_start:
{
lean_object* v_a_5481_; uint8_t v___x_5485_; 
v___x_5485_ = lean_nat_dec_lt(v_a_5478_, v_upperBound_5477_);
if (v___x_5485_ == 0)
{
lean_dec(v_a_5478_);
return v_b_5479_;
}
else
{
lean_object* v_snd_5486_; lean_object* v_snd_5487_; lean_object* v_snd_5488_; lean_object* v_snd_5489_; lean_object* v_fst_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5602_; 
v_snd_5486_ = lean_ctor_get(v_b_5479_, 1);
lean_inc(v_snd_5486_);
v_snd_5487_ = lean_ctor_get(v_snd_5486_, 1);
lean_inc(v_snd_5487_);
v_snd_5488_ = lean_ctor_get(v_snd_5487_, 1);
lean_inc(v_snd_5488_);
v_snd_5489_ = lean_ctor_get(v_snd_5488_, 1);
lean_inc(v_snd_5489_);
v_fst_5490_ = lean_ctor_get(v_b_5479_, 0);
v_isSharedCheck_5602_ = !lean_is_exclusive(v_b_5479_);
if (v_isSharedCheck_5602_ == 0)
{
lean_object* v_unused_5603_; 
v_unused_5603_ = lean_ctor_get(v_b_5479_, 1);
lean_dec(v_unused_5603_);
v___x_5492_ = v_b_5479_;
v_isShared_5493_ = v_isSharedCheck_5602_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_fst_5490_);
lean_dec(v_b_5479_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5602_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v_fst_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5600_; 
v_fst_5494_ = lean_ctor_get(v_snd_5486_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v_snd_5486_);
if (v_isSharedCheck_5600_ == 0)
{
lean_object* v_unused_5601_; 
v_unused_5601_ = lean_ctor_get(v_snd_5486_, 1);
lean_dec(v_unused_5601_);
v___x_5496_ = v_snd_5486_;
v_isShared_5497_ = v_isSharedCheck_5600_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_fst_5494_);
lean_dec(v_snd_5486_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5600_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v_fst_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5598_; 
v_fst_5498_ = lean_ctor_get(v_snd_5487_, 0);
v_isSharedCheck_5598_ = !lean_is_exclusive(v_snd_5487_);
if (v_isSharedCheck_5598_ == 0)
{
lean_object* v_unused_5599_; 
v_unused_5599_ = lean_ctor_get(v_snd_5487_, 1);
lean_dec(v_unused_5599_);
v___x_5500_ = v_snd_5487_;
v_isShared_5501_ = v_isSharedCheck_5598_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_fst_5498_);
lean_dec(v_snd_5487_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5598_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v_fst_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5596_; 
v_fst_5502_ = lean_ctor_get(v_snd_5488_, 0);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_snd_5488_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v_snd_5488_, 1);
lean_dec(v_unused_5597_);
v___x_5504_ = v_snd_5488_;
v_isShared_5505_ = v_isSharedCheck_5596_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_fst_5502_);
lean_dec(v_snd_5488_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5596_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v_array_5506_; lean_object* v_start_5507_; lean_object* v_stop_5508_; uint8_t v___x_5509_; 
v_array_5506_ = lean_ctor_get(v_snd_5489_, 0);
v_start_5507_ = lean_ctor_get(v_snd_5489_, 1);
v_stop_5508_ = lean_ctor_get(v_snd_5489_, 2);
v___x_5509_ = lean_nat_dec_lt(v_start_5507_, v_stop_5508_);
if (v___x_5509_ == 0)
{
lean_object* v___x_5511_; 
lean_dec(v_a_5478_);
if (v_isShared_5505_ == 0)
{
v___x_5511_ = v___x_5504_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_fst_5502_);
lean_ctor_set(v_reuseFailAlloc_5521_, 1, v_snd_5489_);
v___x_5511_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
lean_object* v___x_5513_; 
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 1, v___x_5511_);
v___x_5513_ = v___x_5500_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_fst_5498_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v___x_5511_);
v___x_5513_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
lean_object* v___x_5515_; 
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 1, v___x_5513_);
v___x_5515_ = v___x_5496_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_fst_5494_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5513_);
v___x_5515_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
lean_object* v___x_5517_; 
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 1, v___x_5515_);
v___x_5517_ = v___x_5492_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_fst_5490_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5515_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
}
else
{
lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5592_; 
lean_inc(v_stop_5508_);
lean_inc(v_start_5507_);
lean_inc_ref(v_array_5506_);
v_isSharedCheck_5592_ = !lean_is_exclusive(v_snd_5489_);
if (v_isSharedCheck_5592_ == 0)
{
lean_object* v_unused_5593_; lean_object* v_unused_5594_; lean_object* v_unused_5595_; 
v_unused_5593_ = lean_ctor_get(v_snd_5489_, 2);
lean_dec(v_unused_5593_);
v_unused_5594_ = lean_ctor_get(v_snd_5489_, 1);
lean_dec(v_unused_5594_);
v_unused_5595_ = lean_ctor_get(v_snd_5489_, 0);
lean_dec(v_unused_5595_);
v___x_5523_ = v_snd_5489_;
v_isShared_5524_ = v_isSharedCheck_5592_;
goto v_resetjp_5522_;
}
else
{
lean_dec(v_snd_5489_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5592_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v_array_5525_; lean_object* v_start_5526_; lean_object* v_stop_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5532_; 
v_array_5525_ = lean_ctor_get(v_fst_5502_, 0);
v_start_5526_ = lean_ctor_get(v_fst_5502_, 1);
v_stop_5527_ = lean_ctor_get(v_fst_5502_, 2);
v___x_5528_ = lean_array_fget(v_array_5506_, v_start_5507_);
v___x_5529_ = lean_unsigned_to_nat(1u);
v___x_5530_ = lean_nat_add(v_start_5507_, v___x_5529_);
lean_dec(v_start_5507_);
if (v_isShared_5524_ == 0)
{
lean_ctor_set(v___x_5523_, 1, v___x_5530_);
v___x_5532_ = v___x_5523_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_array_5506_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v___x_5530_);
lean_ctor_set(v_reuseFailAlloc_5591_, 2, v_stop_5508_);
v___x_5532_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
uint8_t v___x_5533_; 
v___x_5533_ = lean_nat_dec_lt(v_start_5526_, v_stop_5527_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5535_; 
lean_dec(v___x_5528_);
lean_dec(v_a_5478_);
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 1, v___x_5532_);
v___x_5535_ = v___x_5504_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_fst_5502_);
lean_ctor_set(v_reuseFailAlloc_5545_, 1, v___x_5532_);
v___x_5535_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
lean_object* v___x_5537_; 
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 1, v___x_5535_);
v___x_5537_ = v___x_5500_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_fst_5498_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v___x_5535_);
v___x_5537_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v___x_5539_; 
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 1, v___x_5537_);
v___x_5539_ = v___x_5496_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_fst_5494_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
lean_object* v___x_5541_; 
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 1, v___x_5539_);
v___x_5541_ = v___x_5492_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_fst_5490_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v___x_5539_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
}
else
{
lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5587_; 
lean_inc(v_stop_5527_);
lean_inc(v_start_5526_);
lean_inc_ref(v_array_5525_);
v_isSharedCheck_5587_ = !lean_is_exclusive(v_fst_5502_);
if (v_isSharedCheck_5587_ == 0)
{
lean_object* v_unused_5588_; lean_object* v_unused_5589_; lean_object* v_unused_5590_; 
v_unused_5588_ = lean_ctor_get(v_fst_5502_, 2);
lean_dec(v_unused_5588_);
v_unused_5589_ = lean_ctor_get(v_fst_5502_, 1);
lean_dec(v_unused_5589_);
v_unused_5590_ = lean_ctor_get(v_fst_5502_, 0);
lean_dec(v_unused_5590_);
v___x_5547_ = v_fst_5502_;
v_isShared_5548_ = v_isSharedCheck_5587_;
goto v_resetjp_5546_;
}
else
{
lean_dec(v_fst_5502_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5587_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5552_; 
v___x_5549_ = lean_array_fget(v_array_5525_, v_start_5526_);
v___x_5550_ = lean_nat_add(v_start_5526_, v___x_5529_);
lean_dec(v_start_5526_);
if (v_isShared_5548_ == 0)
{
lean_ctor_set(v___x_5547_, 1, v___x_5550_);
v___x_5552_ = v___x_5547_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_array_5525_);
lean_ctor_set(v_reuseFailAlloc_5586_, 1, v___x_5550_);
lean_ctor_set(v_reuseFailAlloc_5586_, 2, v_stop_5527_);
v___x_5552_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
uint8_t v___x_5553_; 
v___x_5553_ = lean_unbox(v___x_5549_);
lean_dec(v___x_5549_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5559_; 
v___x_5554_ = lean_array_get_size(v_fst_5498_);
v___x_5555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5554_);
v___x_5556_ = lean_array_push(v_fst_5490_, v___x_5555_);
v___x_5557_ = lean_array_push(v_fst_5498_, v___x_5528_);
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 1, v___x_5532_);
lean_ctor_set(v___x_5504_, 0, v___x_5552_);
v___x_5559_ = v___x_5504_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5569_, 1, v___x_5532_);
v___x_5559_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
lean_object* v___x_5561_; 
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 1, v___x_5559_);
lean_ctor_set(v___x_5500_, 0, v___x_5557_);
v___x_5561_ = v___x_5500_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5557_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v___x_5559_);
v___x_5561_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___x_5563_; 
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 1, v___x_5561_);
v___x_5563_ = v___x_5496_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v_fst_5494_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v___x_5561_);
v___x_5563_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___x_5565_; 
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 1, v___x_5563_);
lean_ctor_set(v___x_5492_, 0, v___x_5556_);
v___x_5565_ = v___x_5492_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v___x_5556_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5563_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
v_a_5481_ = v___x_5565_;
goto v___jp_5480_;
}
}
}
}
}
else
{
lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5575_; 
v___x_5570_ = lean_box(0);
v___x_5571_ = lean_array_push(v_fst_5490_, v___x_5570_);
v___x_5572_ = l_Lean_Expr_fvarId_x21(v___x_5528_);
lean_dec(v___x_5528_);
v___x_5573_ = lean_array_push(v_fst_5494_, v___x_5572_);
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 1, v___x_5532_);
lean_ctor_set(v___x_5504_, 0, v___x_5552_);
v___x_5575_ = v___x_5504_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v___x_5532_);
v___x_5575_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
lean_object* v___x_5577_; 
if (v_isShared_5501_ == 0)
{
lean_ctor_set(v___x_5500_, 1, v___x_5575_);
v___x_5577_ = v___x_5500_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_fst_5498_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v___x_5575_);
v___x_5577_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
lean_object* v___x_5579_; 
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 1, v___x_5577_);
lean_ctor_set(v___x_5496_, 0, v___x_5573_);
v___x_5579_ = v___x_5496_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5583_, 1, v___x_5577_);
v___x_5579_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
lean_object* v___x_5581_; 
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 1, v___x_5579_);
lean_ctor_set(v___x_5492_, 0, v___x_5571_);
v___x_5581_ = v___x_5492_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v___x_5571_);
lean_ctor_set(v_reuseFailAlloc_5582_, 1, v___x_5579_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
v_a_5481_ = v___x_5581_;
goto v___jp_5480_;
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
v___jp_5480_:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5482_ = lean_unsigned_to_nat(1u);
v___x_5483_ = lean_nat_add(v_a_5478_, v___x_5482_);
lean_dec(v_a_5478_);
v_a_5478_ = v___x_5483_;
v_b_5479_ = v_a_5481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5604_, lean_object* v_a_5605_, lean_object* v_b_5606_){
_start:
{
lean_object* v_res_5607_; 
v_res_5607_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5604_, v_a_5605_, v_b_5606_);
lean_dec(v_upperBound_5604_);
return v_res_5607_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5608_, size_t v_i_5609_, size_t v_stop_5610_){
_start:
{
uint8_t v___x_5611_; 
v___x_5611_ = lean_usize_dec_eq(v_i_5609_, v_stop_5610_);
if (v___x_5611_ == 0)
{
uint8_t v___x_5612_; lean_object* v___x_5613_; uint8_t v___x_5614_; 
v___x_5612_ = 1;
v___x_5613_ = lean_array_uget_borrowed(v_as_5608_, v_i_5609_);
v___x_5614_ = l_Lean_Expr_isFVar(v___x_5613_);
if (v___x_5614_ == 0)
{
return v___x_5612_;
}
else
{
if (v___x_5611_ == 0)
{
size_t v___x_5615_; size_t v___x_5616_; 
v___x_5615_ = ((size_t)1ULL);
v___x_5616_ = lean_usize_add(v_i_5609_, v___x_5615_);
v_i_5609_ = v___x_5616_;
goto _start;
}
else
{
return v___x_5612_;
}
}
}
else
{
uint8_t v___x_5618_; 
v___x_5618_ = 0;
return v___x_5618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5619_, lean_object* v_i_5620_, lean_object* v_stop_5621_){
_start:
{
size_t v_i_boxed_5622_; size_t v_stop_boxed_5623_; uint8_t v_res_5624_; lean_object* v_r_5625_; 
v_i_boxed_5622_ = lean_unbox_usize(v_i_5620_);
lean_dec(v_i_5620_);
v_stop_boxed_5623_ = lean_unbox_usize(v_stop_5621_);
lean_dec(v_stop_5621_);
v_res_5624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5619_, v_i_boxed_5622_, v_stop_boxed_5623_);
lean_dec_ref(v_as_5619_);
v_r_5625_ = lean_box(v_res_5624_);
return v_r_5625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5626_, size_t v_sz_5627_, size_t v_i_5628_, lean_object* v_bs_5629_){
_start:
{
uint8_t v___x_5630_; 
v___x_5630_ = lean_usize_dec_lt(v_i_5628_, v_sz_5627_);
if (v___x_5630_ == 0)
{
return v_bs_5629_;
}
else
{
lean_object* v_v_5631_; lean_object* v___x_5632_; lean_object* v_bs_x27_5633_; lean_object* v___y_5635_; 
v_v_5631_ = lean_array_uget(v_bs_5629_, v_i_5628_);
v___x_5632_ = lean_unsigned_to_nat(0u);
v_bs_x27_5633_ = lean_array_uset(v_bs_5629_, v_i_5628_, v___x_5632_);
if (lean_obj_tag(v_v_5631_) == 0)
{
v___y_5635_ = v_v_5631_;
goto v___jp_5634_;
}
else
{
lean_object* v_val_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
v_val_5640_ = lean_ctor_get(v_v_5631_, 0);
lean_inc(v_val_5640_);
lean_dec_ref(v_v_5631_);
v___x_5641_ = lean_box(0);
v___x_5642_ = lean_array_get_borrowed(v___x_5641_, v___x_5626_, v_val_5640_);
lean_dec(v_val_5640_);
lean_inc(v___x_5642_);
v___y_5635_ = v___x_5642_;
goto v___jp_5634_;
}
v___jp_5634_:
{
size_t v___x_5636_; size_t v___x_5637_; lean_object* v___x_5638_; 
v___x_5636_ = ((size_t)1ULL);
v___x_5637_ = lean_usize_add(v_i_5628_, v___x_5636_);
v___x_5638_ = lean_array_uset(v_bs_x27_5633_, v_i_5628_, v___y_5635_);
v_i_5628_ = v___x_5637_;
v_bs_5629_ = v___x_5638_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5643_, lean_object* v_sz_5644_, lean_object* v_i_5645_, lean_object* v_bs_5646_){
_start:
{
size_t v_sz_boxed_5647_; size_t v_i_boxed_5648_; lean_object* v_res_5649_; 
v_sz_boxed_5647_ = lean_unbox_usize(v_sz_5644_);
lean_dec(v_sz_5644_);
v_i_boxed_5648_ = lean_unbox_usize(v_i_5645_);
lean_dec(v_i_5645_);
v_res_5649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5643_, v_sz_boxed_5647_, v_i_boxed_5648_, v_bs_5646_);
lean_dec_ref(v___x_5643_);
return v_res_5649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5650_, size_t v_sz_5651_, size_t v_i_5652_, lean_object* v_bs_5653_){
_start:
{
uint8_t v___x_5654_; 
v___x_5654_ = lean_usize_dec_lt(v_i_5652_, v_sz_5651_);
if (v___x_5654_ == 0)
{
return v_bs_5653_;
}
else
{
lean_object* v_v_5655_; lean_object* v___x_5656_; lean_object* v_bs_x27_5657_; size_t v_sz_5658_; size_t v___x_5659_; lean_object* v___x_5660_; size_t v___x_5661_; size_t v___x_5662_; lean_object* v___x_5663_; 
v_v_5655_ = lean_array_uget(v_bs_5653_, v_i_5652_);
v___x_5656_ = lean_unsigned_to_nat(0u);
v_bs_x27_5657_ = lean_array_uset(v_bs_5653_, v_i_5652_, v___x_5656_);
v_sz_5658_ = lean_array_size(v_v_5655_);
v___x_5659_ = ((size_t)0ULL);
v___x_5660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5650_, v_sz_5658_, v___x_5659_, v_v_5655_);
v___x_5661_ = ((size_t)1ULL);
v___x_5662_ = lean_usize_add(v_i_5652_, v___x_5661_);
v___x_5663_ = lean_array_uset(v_bs_x27_5657_, v_i_5652_, v___x_5660_);
v_i_5652_ = v___x_5662_;
v_bs_5653_ = v___x_5663_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5665_, lean_object* v_sz_5666_, lean_object* v_i_5667_, lean_object* v_bs_5668_){
_start:
{
size_t v_sz_boxed_5669_; size_t v_i_boxed_5670_; lean_object* v_res_5671_; 
v_sz_boxed_5669_ = lean_unbox_usize(v_sz_5666_);
lean_dec(v_sz_5666_);
v_i_boxed_5670_ = lean_unbox_usize(v_i_5667_);
lean_dec(v_i_5667_);
v_res_5671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5665_, v_sz_boxed_5669_, v_i_boxed_5670_, v_bs_5668_);
lean_dec_ref(v___x_5665_);
return v_res_5671_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; 
v___x_5674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5675_ = lean_unsigned_to_nat(6u);
v___x_5676_ = lean_unsigned_to_nat(463u);
v___x_5677_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5678_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5679_ = l_mkPanicMessageWithDecl(v___x_5678_, v___x_5677_, v___x_5676_, v___x_5675_, v___x_5674_);
return v___x_5679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5680_, lean_object* v_as_5681_, size_t v_sz_5682_, size_t v_i_5683_, lean_object* v_b_5684_){
_start:
{
lean_object* v_a_5686_; uint8_t v___x_5690_; 
v___x_5690_ = lean_usize_dec_lt(v_i_5683_, v_sz_5682_);
if (v___x_5690_ == 0)
{
return v_b_5684_;
}
else
{
lean_object* v_a_5691_; lean_object* v___x_5692_; uint8_t v_changed_5693_; 
v_a_5691_ = lean_array_uget_borrowed(v_as_5681_, v_i_5683_);
v___x_5692_ = lean_array_get_size(v___x_5680_);
v_changed_5693_ = lean_nat_dec_lt(v_a_5691_, v___x_5692_);
if (v_changed_5693_ == 0)
{
lean_object* v___x_5694_; lean_object* v___x_5695_; 
lean_dec_ref(v_b_5684_);
v___x_5694_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5695_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5694_);
if (lean_obj_tag(v___x_5695_) == 0)
{
lean_object* v_a_5696_; 
v_a_5696_ = lean_ctor_get(v___x_5695_, 0);
lean_inc(v_a_5696_);
lean_dec_ref(v___x_5695_);
return v_a_5696_;
}
else
{
lean_object* v_a_5697_; 
v_a_5697_ = lean_ctor_get(v___x_5695_, 0);
lean_inc(v_a_5697_);
lean_dec_ref(v___x_5695_);
v_a_5686_ = v_a_5697_;
goto v___jp_5685_;
}
}
else
{
lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5698_ = lean_box(0);
v___x_5699_ = lean_array_get_borrowed(v___x_5698_, v___x_5680_, v_a_5691_);
if (lean_obj_tag(v___x_5699_) == 1)
{
lean_object* v_val_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; 
v_val_5700_ = lean_ctor_get(v___x_5699_, 0);
v___x_5701_ = lean_box(v_changed_5693_);
v___x_5702_ = lean_array_set(v_b_5684_, v_val_5700_, v___x_5701_);
v_a_5686_ = v___x_5702_;
goto v___jp_5685_;
}
else
{
v_a_5686_ = v_b_5684_;
goto v___jp_5685_;
}
}
}
v___jp_5685_:
{
size_t v___x_5687_; size_t v___x_5688_; 
v___x_5687_ = ((size_t)1ULL);
v___x_5688_ = lean_usize_add(v_i_5683_, v___x_5687_);
v_i_5683_ = v___x_5688_;
v_b_5684_ = v_a_5686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5703_, lean_object* v_as_5704_, lean_object* v_sz_5705_, lean_object* v_i_5706_, lean_object* v_b_5707_){
_start:
{
size_t v_sz_boxed_5708_; size_t v_i_boxed_5709_; lean_object* v_res_5710_; 
v_sz_boxed_5708_ = lean_unbox_usize(v_sz_5705_);
lean_dec(v_sz_5705_);
v_i_boxed_5709_ = lean_unbox_usize(v_i_5706_);
lean_dec(v_i_5706_);
v_res_5710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5703_, v_as_5704_, v_sz_boxed_5708_, v_i_boxed_5709_, v_b_5707_);
lean_dec_ref(v_as_5704_);
lean_dec_ref(v___x_5703_);
return v_res_5710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5711_, lean_object* v_a_5712_, lean_object* v_b_5713_){
_start:
{
uint8_t v___x_5714_; 
v___x_5714_ = lean_nat_dec_lt(v_a_5712_, v_upperBound_5711_);
if (v___x_5714_ == 0)
{
lean_dec(v_a_5712_);
return v_b_5713_;
}
else
{
lean_object* v_snd_5715_; lean_object* v_snd_5716_; lean_object* v_fst_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5783_; 
v_snd_5715_ = lean_ctor_get(v_b_5713_, 1);
lean_inc(v_snd_5715_);
v_snd_5716_ = lean_ctor_get(v_snd_5715_, 1);
lean_inc(v_snd_5716_);
v_fst_5717_ = lean_ctor_get(v_b_5713_, 0);
v_isSharedCheck_5783_ = !lean_is_exclusive(v_b_5713_);
if (v_isSharedCheck_5783_ == 0)
{
lean_object* v_unused_5784_; 
v_unused_5784_ = lean_ctor_get(v_b_5713_, 1);
lean_dec(v_unused_5784_);
v___x_5719_ = v_b_5713_;
v_isShared_5720_ = v_isSharedCheck_5783_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_fst_5717_);
lean_dec(v_b_5713_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5783_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v_fst_5721_; lean_object* v___x_5723_; uint8_t v_isShared_5724_; uint8_t v_isSharedCheck_5781_; 
v_fst_5721_ = lean_ctor_get(v_snd_5715_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v_snd_5715_);
if (v_isSharedCheck_5781_ == 0)
{
lean_object* v_unused_5782_; 
v_unused_5782_ = lean_ctor_get(v_snd_5715_, 1);
lean_dec(v_unused_5782_);
v___x_5723_ = v_snd_5715_;
v_isShared_5724_ = v_isSharedCheck_5781_;
goto v_resetjp_5722_;
}
else
{
lean_inc(v_fst_5721_);
lean_dec(v_snd_5715_);
v___x_5723_ = lean_box(0);
v_isShared_5724_ = v_isSharedCheck_5781_;
goto v_resetjp_5722_;
}
v_resetjp_5722_:
{
lean_object* v_array_5725_; lean_object* v_start_5726_; lean_object* v_stop_5727_; uint8_t v___x_5728_; 
v_array_5725_ = lean_ctor_get(v_snd_5716_, 0);
v_start_5726_ = lean_ctor_get(v_snd_5716_, 1);
v_stop_5727_ = lean_ctor_get(v_snd_5716_, 2);
v___x_5728_ = lean_nat_dec_lt(v_start_5726_, v_stop_5727_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5730_; 
lean_dec(v_a_5712_);
if (v_isShared_5724_ == 0)
{
v___x_5730_ = v___x_5723_;
goto v_reusejp_5729_;
}
else
{
lean_object* v_reuseFailAlloc_5734_; 
v_reuseFailAlloc_5734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5734_, 0, v_fst_5721_);
lean_ctor_set(v_reuseFailAlloc_5734_, 1, v_snd_5716_);
v___x_5730_ = v_reuseFailAlloc_5734_;
goto v_reusejp_5729_;
}
v_reusejp_5729_:
{
lean_object* v___x_5732_; 
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 1, v___x_5730_);
v___x_5732_ = v___x_5719_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5733_; 
v_reuseFailAlloc_5733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5733_, 0, v_fst_5717_);
lean_ctor_set(v_reuseFailAlloc_5733_, 1, v___x_5730_);
v___x_5732_ = v_reuseFailAlloc_5733_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
return v___x_5732_;
}
}
}
else
{
lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5777_; 
lean_inc(v_stop_5727_);
lean_inc(v_start_5726_);
lean_inc_ref(v_array_5725_);
v_isSharedCheck_5777_ = !lean_is_exclusive(v_snd_5716_);
if (v_isSharedCheck_5777_ == 0)
{
lean_object* v_unused_5778_; lean_object* v_unused_5779_; lean_object* v_unused_5780_; 
v_unused_5778_ = lean_ctor_get(v_snd_5716_, 2);
lean_dec(v_unused_5778_);
v_unused_5779_ = lean_ctor_get(v_snd_5716_, 1);
lean_dec(v_unused_5779_);
v_unused_5780_ = lean_ctor_get(v_snd_5716_, 0);
lean_dec(v_unused_5780_);
v___x_5736_ = v_snd_5716_;
v_isShared_5737_ = v_isSharedCheck_5777_;
goto v_resetjp_5735_;
}
else
{
lean_dec(v_snd_5716_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5777_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v_array_5738_; lean_object* v_start_5739_; lean_object* v_stop_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5745_; 
v_array_5738_ = lean_ctor_get(v_fst_5721_, 0);
v_start_5739_ = lean_ctor_get(v_fst_5721_, 1);
v_stop_5740_ = lean_ctor_get(v_fst_5721_, 2);
v___x_5741_ = lean_array_fget(v_array_5725_, v_start_5726_);
v___x_5742_ = lean_unsigned_to_nat(1u);
v___x_5743_ = lean_nat_add(v_start_5726_, v___x_5742_);
lean_dec(v_start_5726_);
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 1, v___x_5743_);
v___x_5745_ = v___x_5736_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_array_5725_);
lean_ctor_set(v_reuseFailAlloc_5776_, 1, v___x_5743_);
lean_ctor_set(v_reuseFailAlloc_5776_, 2, v_stop_5727_);
v___x_5745_ = v_reuseFailAlloc_5776_;
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
lean_dec(v_a_5712_);
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 1, v___x_5745_);
v___x_5748_ = v___x_5723_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_fst_5721_);
lean_ctor_set(v_reuseFailAlloc_5752_, 1, v___x_5745_);
v___x_5748_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
lean_object* v___x_5750_; 
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 1, v___x_5748_);
v___x_5750_ = v___x_5719_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_fst_5717_);
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
lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5772_; 
lean_inc(v_stop_5740_);
lean_inc(v_start_5739_);
lean_inc_ref(v_array_5738_);
v_isSharedCheck_5772_ = !lean_is_exclusive(v_fst_5721_);
if (v_isSharedCheck_5772_ == 0)
{
lean_object* v_unused_5773_; lean_object* v_unused_5774_; lean_object* v_unused_5775_; 
v_unused_5773_ = lean_ctor_get(v_fst_5721_, 2);
lean_dec(v_unused_5773_);
v_unused_5774_ = lean_ctor_get(v_fst_5721_, 1);
lean_dec(v_unused_5774_);
v_unused_5775_ = lean_ctor_get(v_fst_5721_, 0);
lean_dec(v_unused_5775_);
v___x_5754_ = v_fst_5721_;
v_isShared_5755_ = v_isSharedCheck_5772_;
goto v_resetjp_5753_;
}
else
{
lean_dec(v_fst_5721_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5772_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5759_; 
v___x_5756_ = lean_array_fget(v_array_5738_, v_start_5739_);
v___x_5757_ = lean_nat_add(v_start_5739_, v___x_5742_);
lean_dec(v_start_5739_);
if (v_isShared_5755_ == 0)
{
lean_ctor_set(v___x_5754_, 1, v___x_5757_);
v___x_5759_ = v___x_5754_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_array_5738_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v___x_5757_);
lean_ctor_set(v_reuseFailAlloc_5771_, 2, v_stop_5740_);
v___x_5759_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
size_t v_sz_5760_; size_t v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5764_; 
v_sz_5760_ = lean_array_size(v___x_5756_);
v___x_5761_ = ((size_t)0ULL);
v___x_5762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5741_, v___x_5756_, v_sz_5760_, v___x_5761_, v_fst_5717_);
lean_dec(v___x_5756_);
lean_dec(v___x_5741_);
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 1, v___x_5745_);
lean_ctor_set(v___x_5723_, 0, v___x_5759_);
v___x_5764_ = v___x_5723_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v___x_5759_);
lean_ctor_set(v_reuseFailAlloc_5770_, 1, v___x_5745_);
v___x_5764_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
lean_object* v___x_5766_; 
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 1, v___x_5764_);
lean_ctor_set(v___x_5719_, 0, v___x_5762_);
v___x_5766_ = v___x_5719_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5769_; 
v_reuseFailAlloc_5769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5769_, 0, v___x_5762_);
lean_ctor_set(v_reuseFailAlloc_5769_, 1, v___x_5764_);
v___x_5766_ = v_reuseFailAlloc_5769_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
lean_object* v___x_5767_; 
v___x_5767_ = lean_nat_add(v_a_5712_, v___x_5742_);
lean_dec(v_a_5712_);
v_a_5712_ = v___x_5767_;
v_b_5713_ = v___x_5766_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_5785_, lean_object* v_a_5786_, lean_object* v_b_5787_){
_start:
{
lean_object* v_res_5788_; 
v_res_5788_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_5785_, v_a_5786_, v_b_5787_);
lean_dec(v_upperBound_5785_);
return v_res_5788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5789_, uint8_t v___x_5790_, lean_object* v_as_5791_, size_t v_sz_5792_, size_t v_i_5793_, lean_object* v_b_5794_){
_start:
{
lean_object* v_a_5796_; uint8_t v___x_5800_; 
v___x_5800_ = lean_usize_dec_lt(v_i_5793_, v_sz_5792_);
if (v___x_5800_ == 0)
{
return v_b_5794_;
}
else
{
lean_object* v_fst_5801_; lean_object* v_snd_5802_; lean_object* v___x_5804_; uint8_t v_isShared_5805_; uint8_t v_isSharedCheck_5823_; 
v_fst_5801_ = lean_ctor_get(v_b_5794_, 0);
v_snd_5802_ = lean_ctor_get(v_b_5794_, 1);
v_isSharedCheck_5823_ = !lean_is_exclusive(v_b_5794_);
if (v_isSharedCheck_5823_ == 0)
{
v___x_5804_ = v_b_5794_;
v_isShared_5805_ = v_isSharedCheck_5823_;
goto v_resetjp_5803_;
}
else
{
lean_inc(v_snd_5802_);
lean_inc(v_fst_5801_);
lean_dec(v_b_5794_);
v___x_5804_ = lean_box(0);
v_isShared_5805_ = v_isSharedCheck_5823_;
goto v_resetjp_5803_;
}
v_resetjp_5803_:
{
lean_object* v_a_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v_a_5810_ = lean_array_uget_borrowed(v_as_5791_, v_i_5793_);
v___x_5811_ = lean_box(0);
v___x_5812_ = lean_array_get_borrowed(v___x_5811_, v___x_5789_, v_a_5810_);
if (lean_obj_tag(v___x_5812_) == 1)
{
lean_object* v_val_5813_; uint8_t v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; uint8_t v___x_5817_; 
v_val_5813_ = lean_ctor_get(v___x_5812_, 0);
v___x_5814_ = 0;
v___x_5815_ = lean_box(v___x_5814_);
v___x_5816_ = lean_array_get(v___x_5815_, v_fst_5801_, v_val_5813_);
lean_dec(v___x_5815_);
v___x_5817_ = lean_unbox(v___x_5816_);
lean_dec(v___x_5816_);
if (v___x_5817_ == 0)
{
if (v___x_5790_ == 0)
{
goto v___jp_5806_;
}
else
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; 
lean_del_object(v___x_5804_);
lean_dec(v_snd_5802_);
v___x_5818_ = lean_box(v___x_5790_);
v___x_5819_ = lean_array_set(v_fst_5801_, v_val_5813_, v___x_5818_);
v___x_5820_ = lean_box(v___x_5790_);
v___x_5821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5819_);
lean_ctor_set(v___x_5821_, 1, v___x_5820_);
v_a_5796_ = v___x_5821_;
goto v___jp_5795_;
}
}
else
{
goto v___jp_5806_;
}
}
else
{
lean_object* v___x_5822_; 
lean_del_object(v___x_5804_);
v___x_5822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5822_, 0, v_fst_5801_);
lean_ctor_set(v___x_5822_, 1, v_snd_5802_);
v_a_5796_ = v___x_5822_;
goto v___jp_5795_;
}
v___jp_5806_:
{
lean_object* v___x_5808_; 
if (v_isShared_5805_ == 0)
{
v___x_5808_ = v___x_5804_;
goto v_reusejp_5807_;
}
else
{
lean_object* v_reuseFailAlloc_5809_; 
v_reuseFailAlloc_5809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5809_, 0, v_fst_5801_);
lean_ctor_set(v_reuseFailAlloc_5809_, 1, v_snd_5802_);
v___x_5808_ = v_reuseFailAlloc_5809_;
goto v_reusejp_5807_;
}
v_reusejp_5807_:
{
v_a_5796_ = v___x_5808_;
goto v___jp_5795_;
}
}
}
}
v___jp_5795_:
{
size_t v___x_5797_; size_t v___x_5798_; 
v___x_5797_ = ((size_t)1ULL);
v___x_5798_ = lean_usize_add(v_i_5793_, v___x_5797_);
v_i_5793_ = v___x_5798_;
v_b_5794_ = v_a_5796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5824_, lean_object* v___x_5825_, lean_object* v_as_5826_, lean_object* v_sz_5827_, lean_object* v_i_5828_, lean_object* v_b_5829_){
_start:
{
uint8_t v___x_8471__boxed_5830_; size_t v_sz_boxed_5831_; size_t v_i_boxed_5832_; lean_object* v_res_5833_; 
v___x_8471__boxed_5830_ = lean_unbox(v___x_5825_);
v_sz_boxed_5831_ = lean_unbox_usize(v_sz_5827_);
lean_dec(v_sz_5827_);
v_i_boxed_5832_ = lean_unbox_usize(v_i_5828_);
lean_dec(v_i_5828_);
v_res_5833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5824_, v___x_8471__boxed_5830_, v_as_5826_, v_sz_boxed_5831_, v_i_boxed_5832_, v_b_5829_);
lean_dec_ref(v_as_5826_);
lean_dec_ref(v___x_5824_);
return v_res_5833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5834_, lean_object* v___x_5835_, lean_object* v_fixedParamPerms_5836_, lean_object* v_next_5837_, lean_object* v_a_5838_, lean_object* v_b_5839_){
_start:
{
lean_object* v_a_5841_; uint8_t v___x_5845_; 
v___x_5845_ = lean_nat_dec_lt(v_a_5838_, v_upperBound_5834_);
if (v___x_5845_ == 0)
{
lean_dec(v_a_5838_);
return v_b_5839_;
}
else
{
lean_object* v_fst_5846_; lean_object* v_snd_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5883_; 
v_fst_5846_ = lean_ctor_get(v_b_5839_, 0);
v_snd_5847_ = lean_ctor_get(v_b_5839_, 1);
v_isSharedCheck_5883_ = !lean_is_exclusive(v_b_5839_);
if (v_isSharedCheck_5883_ == 0)
{
v___x_5849_ = v_b_5839_;
v_isShared_5850_ = v_isSharedCheck_5883_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_snd_5847_);
lean_inc(v_fst_5846_);
lean_dec(v_b_5839_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5883_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5851_; 
v___x_5851_ = lean_array_fget_borrowed(v___x_5835_, v_a_5838_);
if (lean_obj_tag(v___x_5851_) == 1)
{
lean_object* v_val_5852_; uint8_t v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; uint8_t v___x_5856_; 
v_val_5852_ = lean_ctor_get(v___x_5851_, 0);
v___x_5853_ = 0;
v___x_5854_ = lean_box(v___x_5853_);
v___x_5855_ = lean_array_get(v___x_5854_, v_fst_5846_, v_val_5852_);
lean_dec(v___x_5854_);
v___x_5856_ = lean_unbox(v___x_5855_);
if (v___x_5856_ == 0)
{
lean_object* v___x_5858_; 
lean_dec(v___x_5855_);
if (v_isShared_5850_ == 0)
{
v___x_5858_ = v___x_5849_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_fst_5846_);
lean_ctor_set(v_reuseFailAlloc_5859_, 1, v_snd_5847_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
v_a_5841_ = v___x_5858_;
goto v___jp_5840_;
}
}
else
{
lean_object* v_revDeps_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5865_; 
v_revDeps_5860_ = lean_ctor_get(v_fixedParamPerms_5836_, 2);
v___x_5861_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5862_ = lean_array_get_borrowed(v___x_5861_, v_revDeps_5860_, v_next_5837_);
v___x_5863_ = lean_array_get_borrowed(v___x_5861_, v___x_5862_, v_a_5838_);
if (v_isShared_5850_ == 0)
{
v___x_5865_ = v___x_5849_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5879_; 
v_reuseFailAlloc_5879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5879_, 0, v_fst_5846_);
lean_ctor_set(v_reuseFailAlloc_5879_, 1, v_snd_5847_);
v___x_5865_ = v_reuseFailAlloc_5879_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
size_t v_sz_5866_; size_t v___x_5867_; uint8_t v___x_5868_; lean_object* v___x_5869_; lean_object* v_fst_5870_; lean_object* v_snd_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
v_sz_5866_ = lean_array_size(v___x_5863_);
v___x_5867_ = ((size_t)0ULL);
v___x_5868_ = lean_unbox(v___x_5855_);
lean_dec(v___x_5855_);
v___x_5869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5835_, v___x_5868_, v___x_5863_, v_sz_5866_, v___x_5867_, v___x_5865_);
v_fst_5870_ = lean_ctor_get(v___x_5869_, 0);
v_snd_5871_ = lean_ctor_get(v___x_5869_, 1);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5869_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5869_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_snd_5871_);
lean_inc(v_fst_5870_);
lean_dec(v___x_5869_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_fst_5870_);
lean_ctor_set(v_reuseFailAlloc_5877_, 1, v_snd_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
v_a_5841_ = v___x_5876_;
goto v___jp_5840_;
}
}
}
}
}
else
{
lean_object* v___x_5881_; 
if (v_isShared_5850_ == 0)
{
v___x_5881_ = v___x_5849_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v_fst_5846_);
lean_ctor_set(v_reuseFailAlloc_5882_, 1, v_snd_5847_);
v___x_5881_ = v_reuseFailAlloc_5882_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
v_a_5841_ = v___x_5881_;
goto v___jp_5840_;
}
}
}
}
v___jp_5840_:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; 
v___x_5842_ = lean_unsigned_to_nat(1u);
v___x_5843_ = lean_nat_add(v_a_5838_, v___x_5842_);
lean_dec(v_a_5838_);
v_a_5838_ = v___x_5843_;
v_b_5839_ = v_a_5841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5884_, lean_object* v___x_5885_, lean_object* v_fixedParamPerms_5886_, lean_object* v_next_5887_, lean_object* v_a_5888_, lean_object* v_b_5889_){
_start:
{
lean_object* v_res_5890_; 
v_res_5890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5884_, v___x_5885_, v_fixedParamPerms_5886_, v_next_5887_, v_a_5888_, v_b_5889_);
lean_dec(v_next_5887_);
lean_dec_ref(v_fixedParamPerms_5886_);
lean_dec_ref(v___x_5885_);
lean_dec(v_upperBound_5884_);
return v_res_5890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5891_, lean_object* v___x_5892_, lean_object* v_fixedParamPerms_5893_, lean_object* v_a_5894_, lean_object* v_b_5895_){
_start:
{
uint8_t v___x_5896_; 
v___x_5896_ = lean_nat_dec_lt(v_a_5894_, v_upperBound_5891_);
if (v___x_5896_ == 0)
{
lean_dec(v_a_5894_);
return v_b_5895_;
}
else
{
lean_object* v_fst_5897_; lean_object* v_snd_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5921_; 
v_fst_5897_ = lean_ctor_get(v_b_5895_, 0);
v_snd_5898_ = lean_ctor_get(v_b_5895_, 1);
v_isSharedCheck_5921_ = !lean_is_exclusive(v_b_5895_);
if (v_isSharedCheck_5921_ == 0)
{
v___x_5900_ = v_b_5895_;
v_isShared_5901_ = v_isSharedCheck_5921_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_snd_5898_);
lean_inc(v_fst_5897_);
lean_dec(v_b_5895_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5921_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5906_; 
v___x_5902_ = lean_array_fget_borrowed(v___x_5892_, v_a_5894_);
v___x_5903_ = lean_array_get_size(v___x_5902_);
v___x_5904_ = lean_unsigned_to_nat(0u);
if (v_isShared_5901_ == 0)
{
v___x_5906_ = v___x_5900_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_fst_5897_);
lean_ctor_set(v_reuseFailAlloc_5920_, 1, v_snd_5898_);
v___x_5906_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
lean_object* v___x_5907_; lean_object* v_fst_5908_; lean_object* v_snd_5909_; lean_object* v___x_5911_; uint8_t v_isShared_5912_; uint8_t v_isSharedCheck_5919_; 
v___x_5907_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5903_, v___x_5902_, v_fixedParamPerms_5893_, v_a_5894_, v___x_5904_, v___x_5906_);
v_fst_5908_ = lean_ctor_get(v___x_5907_, 0);
v_snd_5909_ = lean_ctor_get(v___x_5907_, 1);
v_isSharedCheck_5919_ = !lean_is_exclusive(v___x_5907_);
if (v_isSharedCheck_5919_ == 0)
{
v___x_5911_ = v___x_5907_;
v_isShared_5912_ = v_isSharedCheck_5919_;
goto v_resetjp_5910_;
}
else
{
lean_inc(v_snd_5909_);
lean_inc(v_fst_5908_);
lean_dec(v___x_5907_);
v___x_5911_ = lean_box(0);
v_isShared_5912_ = v_isSharedCheck_5919_;
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
lean_object* v_reuseFailAlloc_5918_; 
v_reuseFailAlloc_5918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5918_, 0, v_fst_5908_);
lean_ctor_set(v_reuseFailAlloc_5918_, 1, v_snd_5909_);
v___x_5914_ = v_reuseFailAlloc_5918_;
goto v_reusejp_5913_;
}
v_reusejp_5913_:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; 
v___x_5915_ = lean_unsigned_to_nat(1u);
v___x_5916_ = lean_nat_add(v_a_5894_, v___x_5915_);
lean_dec(v_a_5894_);
v_a_5894_ = v___x_5916_;
v_b_5895_ = v___x_5914_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5922_, lean_object* v___x_5923_, lean_object* v_fixedParamPerms_5924_, lean_object* v_a_5925_, lean_object* v_b_5926_){
_start:
{
lean_object* v_res_5927_; 
v_res_5927_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5922_, v___x_5923_, v_fixedParamPerms_5924_, v_a_5925_, v_b_5926_);
lean_dec_ref(v_fixedParamPerms_5924_);
lean_dec_ref(v___x_5923_);
lean_dec(v_upperBound_5922_);
return v_res_5927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_5928_, lean_object* v___x_5929_, lean_object* v_fixedParamPerms_5930_, lean_object* v_b_5931_){
_start:
{
lean_object* v_snd_5932_; uint8_t v___x_5933_; 
v_snd_5932_ = lean_ctor_get(v_b_5931_, 1);
v___x_5933_ = lean_unbox(v_snd_5932_);
if (v___x_5933_ == 0)
{
lean_object* v_fst_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5941_; 
lean_inc(v_snd_5932_);
v_fst_5934_ = lean_ctor_get(v_b_5931_, 0);
v_isSharedCheck_5941_ = !lean_is_exclusive(v_b_5931_);
if (v_isSharedCheck_5941_ == 0)
{
lean_object* v_unused_5942_; 
v_unused_5942_ = lean_ctor_get(v_b_5931_, 1);
lean_dec(v_unused_5942_);
v___x_5936_ = v_b_5931_;
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_fst_5934_);
lean_dec(v_b_5931_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
lean_object* v___x_5939_; 
if (v_isShared_5937_ == 0)
{
v___x_5939_ = v___x_5936_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_fst_5934_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v_snd_5932_);
v___x_5939_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
return v___x_5939_;
}
}
}
else
{
lean_object* v_fst_5943_; lean_object* v___x_5945_; uint8_t v_isShared_5946_; uint8_t v_isSharedCheck_5964_; 
v_fst_5943_ = lean_ctor_get(v_b_5931_, 0);
v_isSharedCheck_5964_ = !lean_is_exclusive(v_b_5931_);
if (v_isSharedCheck_5964_ == 0)
{
lean_object* v_unused_5965_; 
v_unused_5965_ = lean_ctor_get(v_b_5931_, 1);
lean_dec(v_unused_5965_);
v___x_5945_ = v_b_5931_;
v_isShared_5946_ = v_isSharedCheck_5964_;
goto v_resetjp_5944_;
}
else
{
lean_inc(v_fst_5943_);
lean_dec(v_b_5931_);
v___x_5945_ = lean_box(0);
v_isShared_5946_ = v_isSharedCheck_5964_;
goto v_resetjp_5944_;
}
v_resetjp_5944_:
{
uint8_t v_changed_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5951_; 
v_changed_5947_ = 0;
v___x_5948_ = lean_unsigned_to_nat(0u);
v___x_5949_ = lean_box(v_changed_5947_);
if (v_isShared_5946_ == 0)
{
lean_ctor_set(v___x_5945_, 1, v___x_5949_);
v___x_5951_ = v___x_5945_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5963_; 
v_reuseFailAlloc_5963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5963_, 0, v_fst_5943_);
lean_ctor_set(v_reuseFailAlloc_5963_, 1, v___x_5949_);
v___x_5951_ = v_reuseFailAlloc_5963_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
lean_object* v___x_5952_; lean_object* v_fst_5953_; lean_object* v_snd_5954_; lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_5962_; 
v___x_5952_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5928_, v___x_5929_, v_fixedParamPerms_5930_, v___x_5948_, v___x_5951_);
v_fst_5953_ = lean_ctor_get(v___x_5952_, 0);
v_snd_5954_ = lean_ctor_get(v___x_5952_, 1);
v_isSharedCheck_5962_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_5962_ == 0)
{
v___x_5956_ = v___x_5952_;
v_isShared_5957_ = v_isSharedCheck_5962_;
goto v_resetjp_5955_;
}
else
{
lean_inc(v_snd_5954_);
lean_inc(v_fst_5953_);
lean_dec(v___x_5952_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_5962_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
lean_object* v___x_5959_; 
if (v_isShared_5957_ == 0)
{
v___x_5959_ = v___x_5956_;
goto v_reusejp_5958_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_fst_5953_);
lean_ctor_set(v_reuseFailAlloc_5961_, 1, v_snd_5954_);
v___x_5959_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5958_;
}
v_reusejp_5958_:
{
v_b_5931_ = v___x_5959_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_5966_, lean_object* v___x_5967_, lean_object* v_fixedParamPerms_5968_, lean_object* v_b_5969_){
_start:
{
lean_object* v_res_5970_; 
v_res_5970_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_5966_, v___x_5967_, v_fixedParamPerms_5968_, v_b_5969_);
lean_dec_ref(v_fixedParamPerms_5968_);
lean_dec_ref(v___x_5967_);
lean_dec(v___x_5966_);
return v_res_5970_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5972_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_5973_ = lean_unsigned_to_nat(2u);
v___x_5974_ = lean_unsigned_to_nat(457u);
v___x_5975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5977_ = l_mkPanicMessageWithDecl(v___x_5976_, v___x_5975_, v___x_5974_, v___x_5973_, v___x_5972_);
return v___x_5977_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; 
v___x_5979_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_5980_ = lean_unsigned_to_nat(2u);
v___x_5981_ = lean_unsigned_to_nat(458u);
v___x_5982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5983_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5984_ = l_mkPanicMessageWithDecl(v___x_5983_, v___x_5982_, v___x_5981_, v___x_5980_, v___x_5979_);
return v___x_5984_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; 
v___x_5986_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_5987_ = lean_unsigned_to_nat(2u);
v___x_5988_ = lean_unsigned_to_nat(456u);
v___x_5989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5990_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5991_ = l_mkPanicMessageWithDecl(v___x_5990_, v___x_5989_, v___x_5988_, v___x_5987_, v___x_5986_);
return v___x_5991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_5992_, lean_object* v_xs_5993_, lean_object* v_toErase_5994_){
_start:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; uint8_t v___x_6080_; 
v___x_5995_ = lean_unsigned_to_nat(0u);
v___x_5996_ = lean_array_get_size(v_xs_5993_);
v___x_6080_ = lean_nat_dec_lt(v___x_5995_, v___x_5996_);
if (v___x_6080_ == 0)
{
goto v___jp_5997_;
}
else
{
if (v___x_6080_ == 0)
{
goto v___jp_5997_;
}
else
{
size_t v___x_6081_; size_t v___x_6082_; uint8_t v___x_6083_; 
v___x_6081_ = ((size_t)0ULL);
v___x_6082_ = lean_usize_of_nat(v___x_5996_);
v___x_6083_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_5993_, v___x_6081_, v___x_6082_);
if (v___x_6083_ == 0)
{
goto v___jp_5997_;
}
else
{
lean_object* v___x_6084_; lean_object* v___x_6085_; 
lean_dec_ref(v_toErase_5994_);
lean_dec_ref(v_xs_5993_);
lean_dec_ref(v_fixedParamPerms_5992_);
v___x_6084_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6085_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6084_);
return v___x_6085_;
}
}
}
v___jp_5997_:
{
lean_object* v_numFixed_5998_; lean_object* v_perms_5999_; lean_object* v_revDeps_6000_; uint8_t v___x_6001_; 
v_numFixed_5998_ = lean_ctor_get(v_fixedParamPerms_5992_, 0);
v_perms_5999_ = lean_ctor_get(v_fixedParamPerms_5992_, 1);
lean_inc_ref(v_perms_5999_);
v_revDeps_6000_ = lean_ctor_get(v_fixedParamPerms_5992_, 2);
lean_inc_ref(v_revDeps_6000_);
v___x_6001_ = lean_nat_dec_eq(v_numFixed_5998_, v___x_5996_);
if (v___x_6001_ == 0)
{
lean_object* v___x_6002_; lean_object* v___x_6003_; 
lean_dec_ref(v_revDeps_6000_);
lean_dec_ref(v_perms_5999_);
lean_dec_ref(v_toErase_5994_);
lean_dec_ref(v_xs_5993_);
lean_dec_ref(v_fixedParamPerms_5992_);
v___x_6002_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6003_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6002_);
return v___x_6003_;
}
else
{
lean_object* v___x_6004_; lean_object* v___x_6005_; uint8_t v_changed_6006_; 
v___x_6004_ = lean_array_get_size(v_toErase_5994_);
v___x_6005_ = lean_array_get_size(v_perms_5999_);
v_changed_6006_ = lean_nat_dec_eq(v___x_6004_, v___x_6005_);
if (v_changed_6006_ == 0)
{
lean_object* v___x_6007_; lean_object* v___x_6008_; 
lean_dec_ref(v_revDeps_6000_);
lean_dec_ref(v_perms_5999_);
lean_dec_ref(v_toErase_5994_);
lean_dec_ref(v_xs_5993_);
lean_dec_ref(v_fixedParamPerms_5992_);
v___x_6007_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6008_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6007_);
return v___x_6008_;
}
else
{
uint8_t v_changed_6009_; lean_object* v___x_6010_; lean_object* v_mask_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v_fst_6017_; lean_object* v___x_6019_; uint8_t v_isShared_6020_; uint8_t v_isSharedCheck_6078_; 
v_changed_6009_ = 0;
v___x_6010_ = lean_box(v_changed_6009_);
lean_inc(v_numFixed_5998_);
v_mask_6011_ = lean_mk_array(v_numFixed_5998_, v___x_6010_);
v___x_6012_ = l_Array_toSubarray___redArg(v_toErase_5994_, v___x_5995_, v___x_6004_);
lean_inc_ref(v_perms_5999_);
v___x_6013_ = l_Array_toSubarray___redArg(v_perms_5999_, v___x_5995_, v___x_6005_);
v___x_6014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6012_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6015_, 0, v_mask_6011_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6004_, v___x_5995_, v___x_6015_);
v_fst_6017_ = lean_ctor_get(v___x_6016_, 0);
v_isSharedCheck_6078_ = !lean_is_exclusive(v___x_6016_);
if (v_isSharedCheck_6078_ == 0)
{
lean_object* v_unused_6079_; 
v_unused_6079_ = lean_ctor_get(v___x_6016_, 1);
lean_dec(v_unused_6079_);
v___x_6019_ = v___x_6016_;
v_isShared_6020_ = v_isSharedCheck_6078_;
goto v_resetjp_6018_;
}
else
{
lean_inc(v_fst_6017_);
lean_dec(v___x_6016_);
v___x_6019_ = lean_box(0);
v_isShared_6020_ = v_isSharedCheck_6078_;
goto v_resetjp_6018_;
}
v_resetjp_6018_:
{
lean_object* v___x_6021_; lean_object* v___x_6023_; 
v___x_6021_ = lean_box(v_changed_6006_);
if (v_isShared_6020_ == 0)
{
lean_ctor_set(v___x_6019_, 1, v___x_6021_);
v___x_6023_ = v___x_6019_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6077_; 
v_reuseFailAlloc_6077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6077_, 0, v_fst_6017_);
lean_ctor_set(v_reuseFailAlloc_6077_, 1, v___x_6021_);
v___x_6023_ = v_reuseFailAlloc_6077_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
lean_object* v___x_6024_; lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6073_; 
v___x_6024_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6005_, v_perms_5999_, v_fixedParamPerms_5992_, v___x_6023_);
v_isSharedCheck_6073_ = !lean_is_exclusive(v_fixedParamPerms_5992_);
if (v_isSharedCheck_6073_ == 0)
{
lean_object* v_unused_6074_; lean_object* v_unused_6075_; lean_object* v_unused_6076_; 
v_unused_6074_ = lean_ctor_get(v_fixedParamPerms_5992_, 2);
lean_dec(v_unused_6074_);
v_unused_6075_ = lean_ctor_get(v_fixedParamPerms_5992_, 1);
lean_dec(v_unused_6075_);
v_unused_6076_ = lean_ctor_get(v_fixedParamPerms_5992_, 0);
lean_dec(v_unused_6076_);
v___x_6026_ = v_fixedParamPerms_5992_;
v_isShared_6027_ = v_isSharedCheck_6073_;
goto v_resetjp_6025_;
}
else
{
lean_dec(v_fixedParamPerms_5992_);
v___x_6026_ = lean_box(0);
v_isShared_6027_ = v_isSharedCheck_6073_;
goto v_resetjp_6025_;
}
v_resetjp_6025_:
{
lean_object* v_fst_6028_; lean_object* v___x_6030_; uint8_t v_isShared_6031_; uint8_t v_isSharedCheck_6071_; 
v_fst_6028_ = lean_ctor_get(v___x_6024_, 0);
v_isSharedCheck_6071_ = !lean_is_exclusive(v___x_6024_);
if (v_isSharedCheck_6071_ == 0)
{
lean_object* v_unused_6072_; 
v_unused_6072_ = lean_ctor_get(v___x_6024_, 1);
lean_dec(v_unused_6072_);
v___x_6030_ = v___x_6024_;
v_isShared_6031_ = v_isSharedCheck_6071_;
goto v_resetjp_6029_;
}
else
{
lean_inc(v_fst_6028_);
lean_dec(v___x_6024_);
v___x_6030_ = lean_box(0);
v_isShared_6031_ = v_isSharedCheck_6071_;
goto v_resetjp_6029_;
}
v_resetjp_6029_:
{
lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6037_; 
v___x_6032_ = lean_array_get_size(v_fst_6028_);
v___x_6033_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6034_ = l_Array_toSubarray___redArg(v_fst_6028_, v___x_5995_, v___x_6032_);
v___x_6035_ = l_Array_toSubarray___redArg(v_xs_5993_, v___x_5995_, v___x_5996_);
if (v_isShared_6031_ == 0)
{
lean_ctor_set(v___x_6030_, 1, v___x_6035_);
lean_ctor_set(v___x_6030_, 0, v___x_6034_);
v___x_6037_ = v___x_6030_;
goto v_reusejp_6036_;
}
else
{
lean_object* v_reuseFailAlloc_6070_; 
v_reuseFailAlloc_6070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6070_, 0, v___x_6034_);
lean_ctor_set(v_reuseFailAlloc_6070_, 1, v___x_6035_);
v___x_6037_ = v_reuseFailAlloc_6070_;
goto v_reusejp_6036_;
}
v_reusejp_6036_:
{
lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v_snd_6042_; lean_object* v_snd_6043_; lean_object* v_fst_6044_; lean_object* v_fst_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6068_; 
v___x_6038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6033_);
lean_ctor_set(v___x_6038_, 1, v___x_6037_);
v___x_6039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6033_);
lean_ctor_set(v___x_6039_, 1, v___x_6038_);
v___x_6040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6033_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6032_, v___x_5995_, v___x_6040_);
v_snd_6042_ = lean_ctor_get(v___x_6041_, 1);
lean_inc(v_snd_6042_);
v_snd_6043_ = lean_ctor_get(v_snd_6042_, 1);
lean_inc(v_snd_6043_);
v_fst_6044_ = lean_ctor_get(v___x_6041_, 0);
lean_inc(v_fst_6044_);
lean_dec_ref(v___x_6041_);
v_fst_6045_ = lean_ctor_get(v_snd_6042_, 0);
v_isSharedCheck_6068_ = !lean_is_exclusive(v_snd_6042_);
if (v_isSharedCheck_6068_ == 0)
{
lean_object* v_unused_6069_; 
v_unused_6069_ = lean_ctor_get(v_snd_6042_, 1);
lean_dec(v_unused_6069_);
v___x_6047_ = v_snd_6042_;
v_isShared_6048_ = v_isSharedCheck_6068_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_fst_6045_);
lean_dec(v_snd_6042_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6068_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v_fst_6049_; lean_object* v___x_6051_; uint8_t v_isShared_6052_; uint8_t v_isSharedCheck_6066_; 
v_fst_6049_ = lean_ctor_get(v_snd_6043_, 0);
v_isSharedCheck_6066_ = !lean_is_exclusive(v_snd_6043_);
if (v_isSharedCheck_6066_ == 0)
{
lean_object* v_unused_6067_; 
v_unused_6067_ = lean_ctor_get(v_snd_6043_, 1);
lean_dec(v_unused_6067_);
v___x_6051_ = v_snd_6043_;
v_isShared_6052_ = v_isSharedCheck_6066_;
goto v_resetjp_6050_;
}
else
{
lean_inc(v_fst_6049_);
lean_dec(v_snd_6043_);
v___x_6051_ = lean_box(0);
v_isShared_6052_ = v_isSharedCheck_6066_;
goto v_resetjp_6050_;
}
v_resetjp_6050_:
{
lean_object* v___x_6053_; size_t v_sz_6054_; size_t v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6058_; 
v___x_6053_ = lean_array_get_size(v_fst_6049_);
v_sz_6054_ = lean_array_size(v_perms_5999_);
v___x_6055_ = ((size_t)0ULL);
v___x_6056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6044_, v_sz_6054_, v___x_6055_, v_perms_5999_);
lean_dec(v_fst_6044_);
if (v_isShared_6027_ == 0)
{
lean_ctor_set(v___x_6026_, 1, v___x_6056_);
lean_ctor_set(v___x_6026_, 0, v___x_6053_);
v___x_6058_ = v___x_6026_;
goto v_reusejp_6057_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v___x_6053_);
lean_ctor_set(v_reuseFailAlloc_6065_, 1, v___x_6056_);
lean_ctor_set(v_reuseFailAlloc_6065_, 2, v_revDeps_6000_);
v___x_6058_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6057_;
}
v_reusejp_6057_:
{
lean_object* v___x_6060_; 
if (v_isShared_6052_ == 0)
{
lean_ctor_set(v___x_6051_, 1, v_fst_6045_);
v___x_6060_ = v___x_6051_;
goto v_reusejp_6059_;
}
else
{
lean_object* v_reuseFailAlloc_6064_; 
v_reuseFailAlloc_6064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_fst_6049_);
lean_ctor_set(v_reuseFailAlloc_6064_, 1, v_fst_6045_);
v___x_6060_ = v_reuseFailAlloc_6064_;
goto v_reusejp_6059_;
}
v_reusejp_6059_:
{
lean_object* v___x_6062_; 
if (v_isShared_6048_ == 0)
{
lean_ctor_set(v___x_6047_, 1, v___x_6060_);
lean_ctor_set(v___x_6047_, 0, v___x_6058_);
v___x_6062_ = v___x_6047_;
goto v_reusejp_6061_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v___x_6058_);
lean_ctor_set(v_reuseFailAlloc_6063_, 1, v___x_6060_);
v___x_6062_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6061_;
}
v_reusejp_6061_:
{
return v___x_6062_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6086_, lean_object* v___x_6087_, lean_object* v_fixedParamPerms_6088_, lean_object* v_next_6089_, lean_object* v_inst_6090_, lean_object* v_R_6091_, lean_object* v_a_6092_, lean_object* v_b_6093_, lean_object* v_c_6094_){
_start:
{
lean_object* v___x_6095_; 
v___x_6095_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6086_, v___x_6087_, v_fixedParamPerms_6088_, v_next_6089_, v_a_6092_, v_b_6093_);
return v___x_6095_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6096_, lean_object* v___x_6097_, lean_object* v_fixedParamPerms_6098_, lean_object* v_next_6099_, lean_object* v_inst_6100_, lean_object* v_R_6101_, lean_object* v_a_6102_, lean_object* v_b_6103_, lean_object* v_c_6104_){
_start:
{
lean_object* v_res_6105_; 
v_res_6105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6096_, v___x_6097_, v_fixedParamPerms_6098_, v_next_6099_, v_inst_6100_, v_R_6101_, v_a_6102_, v_b_6103_, v_c_6104_);
lean_dec(v_next_6099_);
lean_dec_ref(v_fixedParamPerms_6098_);
lean_dec_ref(v___x_6097_);
lean_dec(v_upperBound_6096_);
return v_res_6105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6106_, lean_object* v___x_6107_, lean_object* v_fixedParamPerms_6108_, lean_object* v_inst_6109_, lean_object* v_R_6110_, lean_object* v_a_6111_, lean_object* v_b_6112_, lean_object* v_c_6113_){
_start:
{
lean_object* v___x_6114_; 
v___x_6114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6106_, v___x_6107_, v_fixedParamPerms_6108_, v_a_6111_, v_b_6112_);
return v___x_6114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6115_, lean_object* v___x_6116_, lean_object* v_fixedParamPerms_6117_, lean_object* v_inst_6118_, lean_object* v_R_6119_, lean_object* v_a_6120_, lean_object* v_b_6121_, lean_object* v_c_6122_){
_start:
{
lean_object* v_res_6123_; 
v_res_6123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6115_, v___x_6116_, v_fixedParamPerms_6117_, v_inst_6118_, v_R_6119_, v_a_6120_, v_b_6121_, v_c_6122_);
lean_dec_ref(v_fixedParamPerms_6117_);
lean_dec_ref(v___x_6116_);
lean_dec(v_upperBound_6115_);
return v_res_6123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6124_, lean_object* v_inst_6125_, lean_object* v_R_6126_, lean_object* v_a_6127_, lean_object* v_b_6128_, lean_object* v_c_6129_){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6124_, v_a_6127_, v_b_6128_);
return v___x_6130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6131_, lean_object* v_inst_6132_, lean_object* v_R_6133_, lean_object* v_a_6134_, lean_object* v_b_6135_, lean_object* v_c_6136_){
_start:
{
lean_object* v_res_6137_; 
v_res_6137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6131_, v_inst_6132_, v_R_6133_, v_a_6134_, v_b_6135_, v_c_6136_);
lean_dec(v_upperBound_6131_);
return v_res_6137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6138_, lean_object* v_inst_6139_, lean_object* v_R_6140_, lean_object* v_a_6141_, lean_object* v_b_6142_, lean_object* v_c_6143_){
_start:
{
lean_object* v___x_6144_; 
v___x_6144_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6138_, v_a_6141_, v_b_6142_);
return v___x_6144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6145_, lean_object* v_inst_6146_, lean_object* v_R_6147_, lean_object* v_a_6148_, lean_object* v_b_6149_, lean_object* v_c_6150_){
_start:
{
lean_object* v_res_6151_; 
v_res_6151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6145_, v_inst_6146_, v_R_6147_, v_a_6148_, v_b_6149_, v_c_6150_);
lean_dec(v_upperBound_6145_);
return v_res_6151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6209_; uint8_t v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; 
v___x_6209_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6210_ = 0;
v___x_6211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6212_ = l_Lean_registerTraceClass(v___x_6209_, v___x_6210_, v___x_6211_);
return v___x_6212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6213_){
_start:
{
lean_object* v_res_6214_; 
v_res_6214_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6214_;
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
