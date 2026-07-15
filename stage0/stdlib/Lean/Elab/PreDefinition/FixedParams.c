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
lean_object* lean_usize_to_nat(size_t);
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
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_box(0);
v___x_672_ = lean_unsigned_to_nat(16u);
v___x_673_ = lean_mk_array(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(lean_object* v_e_677_, lean_object* v_fvarId_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; uint8_t v_fst_683_; lean_object* v_mctx_684_; lean_object* v___y_702_; lean_object* v_mctx_707_; lean_object* v___f_708_; lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_681_ = lean_st_ref_get(v___y_679_);
v_mctx_707_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref_n(v_mctx_707_, 2);
lean_dec(v___x_681_);
v___f_708_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0));
v___f_709_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_709_, 0, v_fvarId_678_);
v___x_710_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_mctx_707_);
v___x_712_ = l_Lean_Expr_hasFVar(v_e_677_);
if (v___x_712_ == 0)
{
uint8_t v___x_713_; 
v___x_713_ = l_Lean_Expr_hasMVar(v_e_677_);
if (v___x_713_ == 0)
{
lean_dec_ref_known(v___x_711_, 2);
lean_dec_ref(v___f_709_);
lean_dec_ref(v_e_677_);
v_fst_683_ = v___x_713_;
v_mctx_684_ = v_mctx_707_;
goto v___jp_682_;
}
else
{
lean_object* v___x_714_; 
lean_dec_ref(v_mctx_707_);
v___x_714_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_709_, v___f_708_, v_e_677_, v___x_711_);
v___y_702_ = v___x_714_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_715_; 
lean_dec_ref(v_mctx_707_);
v___x_715_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_709_, v___f_708_, v_e_677_, v___x_711_);
v___y_702_ = v___x_715_;
goto v___jp_701_;
}
v___jp_682_:
{
lean_object* v___x_685_; lean_object* v_cache_686_; lean_object* v_zetaDeltaFVarIds_687_; lean_object* v_postponed_688_; lean_object* v_diag_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_699_; 
v___x_685_ = lean_st_ref_take(v___y_679_);
v_cache_686_ = lean_ctor_get(v___x_685_, 1);
v_zetaDeltaFVarIds_687_ = lean_ctor_get(v___x_685_, 2);
v_postponed_688_ = lean_ctor_get(v___x_685_, 3);
v_diag_689_ = lean_ctor_get(v___x_685_, 4);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v___x_685_, 0);
lean_dec(v_unused_700_);
v___x_691_ = v___x_685_;
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_diag_689_);
lean_inc(v_postponed_688_);
lean_inc(v_zetaDeltaFVarIds_687_);
lean_inc(v_cache_686_);
lean_dec(v___x_685_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v_mctx_684_);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_mctx_684_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_cache_686_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_zetaDeltaFVarIds_687_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_postponed_688_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_diag_689_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_st_ref_set(v___y_679_, v___x_694_);
v___x_696_ = lean_box(v_fst_683_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
v___jp_701_:
{
lean_object* v_snd_703_; lean_object* v_fst_704_; lean_object* v_mctx_705_; uint8_t v___x_706_; 
v_snd_703_ = lean_ctor_get(v___y_702_, 1);
lean_inc(v_snd_703_);
v_fst_704_ = lean_ctor_get(v___y_702_, 0);
lean_inc(v_fst_704_);
lean_dec_ref(v___y_702_);
v_mctx_705_ = lean_ctor_get(v_snd_703_, 1);
lean_inc_ref(v_mctx_705_);
lean_dec(v_snd_703_);
v___x_706_ = lean_unbox(v_fst_704_);
lean_dec(v_fst_704_);
v_fst_683_ = v___x_706_;
v_mctx_684_ = v_mctx_705_;
goto v___jp_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___boxed(lean_object* v_e_716_, lean_object* v_fvarId_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_716_, v_fvarId_717_, v___y_718_);
lean_dec(v___y_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(lean_object* v_e_721_, lean_object* v_fvarId_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_721_, v_fvarId_722_, v___y_724_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___boxed(lean_object* v_e_729_, lean_object* v_fvarId_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(v_e_729_, v_fvarId_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(lean_object* v_k_737_, lean_object* v_b_738_, lean_object* v_c_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; 
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
v___x_745_ = lean_apply_7(v_k_737_, v_b_738_, v_c_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, lean_box(0));
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed(lean_object* v_k_746_, lean_object* v_b_747_, lean_object* v_c_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(v_k_746_, v_b_747_, v_c_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(lean_object* v_e_755_, lean_object* v_k_756_, uint8_t v_cleanupAnnotations_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___f_763_; uint8_t v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_763_, 0, v_k_756_);
v___x_764_ = 1;
v___x_765_ = 0;
v___x_766_ = lean_box(0);
v___x_767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_755_, v___x_764_, v___x_765_, v___x_764_, v___x_765_, v___x_766_, v___f_763_, v_cleanupAnnotations_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_a_776_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_767_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_767_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___boxed(lean_object* v_e_784_, lean_object* v_k_785_, lean_object* v_cleanupAnnotations_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_792_; lean_object* v_res_793_; 
v_cleanupAnnotations_boxed_792_ = lean_unbox(v_cleanupAnnotations_786_);
v_res_793_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_784_, v_k_785_, v_cleanupAnnotations_boxed_792_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(lean_object* v_00_u03b1_794_, lean_object* v_e_795_, lean_object* v_k_796_, uint8_t v_cleanupAnnotations_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_795_, v_k_796_, v_cleanupAnnotations_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___boxed(lean_object* v_00_u03b1_804_, lean_object* v_e_805_, lean_object* v_k_806_, lean_object* v_cleanupAnnotations_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_813_; lean_object* v_res_814_; 
v_cleanupAnnotations_boxed_813_ = lean_unbox(v_cleanupAnnotations_807_);
v_res_814_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(v_00_u03b1_804_, v_e_805_, v_k_806_, v_cleanupAnnotations_boxed_813_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(lean_object* v_upperBound_815_, lean_object* v_xs_816_, lean_object* v_next_817_, lean_object* v_a_818_, lean_object* v_b_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = lean_nat_dec_lt(v_a_818_, v_upperBound_815_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec(v_a_818_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v_b_819_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_array_fget_borrowed(v_xs_816_, v_a_818_);
lean_inc(v___y_823_);
lean_inc_ref(v___y_822_);
lean_inc(v___y_821_);
lean_inc_ref(v___y_820_);
lean_inc(v___x_827_);
v___x_828_ = lean_infer_type(v___x_827_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
v___x_830_ = lean_array_fget_borrowed(v_xs_816_, v_next_817_);
v___x_831_ = l_Lean_Expr_fvarId_x21(v___x_830_);
v___x_832_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_a_829_, v___x_831_, v___y_821_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v_a_835_; uint8_t v___x_839_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_839_ = lean_unbox(v_a_833_);
lean_dec(v_a_833_);
if (v___x_839_ == 0)
{
v_a_835_ = v_b_819_;
goto v___jp_834_;
}
else
{
lean_object* v___x_840_; 
lean_inc(v_a_818_);
v___x_840_ = lean_array_push(v_b_819_, v_a_818_);
v_a_835_ = v___x_840_;
goto v___jp_834_;
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_add(v_a_818_, v___x_836_);
lean_dec(v_a_818_);
v_a_818_ = v___x_837_;
v_b_819_ = v_a_835_;
goto _start;
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v_b_819_);
lean_dec(v_a_818_);
v_a_841_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_832_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_832_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v_b_819_);
lean_dec(v_a_818_);
v_a_849_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_828_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_828_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg___boxed(lean_object* v_upperBound_857_, lean_object* v_xs_858_, lean_object* v_next_859_, lean_object* v_a_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_857_, v_xs_858_, v_next_859_, v_a_860_, v_b_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v_next_859_);
lean_dec_ref(v_xs_858_);
lean_dec(v_upperBound_857_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(lean_object* v_upperBound_870_, lean_object* v___x_871_, lean_object* v_xs_872_, lean_object* v_a_873_, lean_object* v_b_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = lean_nat_dec_lt(v_a_873_, v_upperBound_870_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_a_873_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v_b_874_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_nat_add(v_a_873_, v___x_882_);
v___x_884_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___closed__0));
lean_inc(v___x_883_);
v___x_885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v___x_871_, v_xs_872_, v_a_873_, v___x_883_, v___x_884_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v_a_873_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_array_push(v_b_874_, v_a_886_);
v_a_873_ = v___x_883_;
v_b_874_ = v___x_887_;
goto _start;
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v___x_883_);
lean_dec_ref(v_b_874_);
v_a_889_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_885_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_885_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___boxed(lean_object* v_upperBound_897_, lean_object* v___x_898_, lean_object* v_xs_899_, lean_object* v_a_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_897_, v___x_898_, v_xs_899_, v_a_900_, v_b_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_xs_899_);
lean_dec(v___x_898_);
lean_dec(v_upperBound_897_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0(lean_object* v_xs_910_, lean_object* v_x_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_revDeps_919_; lean_object* v___x_920_; 
v___x_917_ = lean_array_get_size(v_xs_910_);
v___x_918_ = lean_unsigned_to_nat(0u);
v_revDeps_919_ = ((lean_object*)(l_Lean_Elab_getParamRevDeps___lam__0___closed__0));
v___x_920_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v___x_917_, v___x_917_, v_xs_910_, v___x_918_, v_revDeps_919_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0___boxed(lean_object* v_xs_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Elab_getParamRevDeps___lam__0(v_xs_921_, v_x_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec_ref(v_x_922_);
lean_dec_ref(v_xs_921_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps(lean_object* v_value_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___f_936_; uint8_t v___x_937_; lean_object* v___x_938_; 
v___f_936_ = ((lean_object*)(l_Lean_Elab_getParamRevDeps___closed__0));
v___x_937_ = 1;
v___x_938_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_930_, v___f_936_, v___x_937_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___boxed(lean_object* v_value_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Elab_getParamRevDeps(v_value_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(lean_object* v_upperBound_946_, lean_object* v_xs_947_, lean_object* v_next_948_, lean_object* v_inst_949_, lean_object* v_R_950_, lean_object* v_a_951_, lean_object* v_b_952_, lean_object* v_c_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_946_, v_xs_947_, v_next_948_, v_a_951_, v_b_952_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___boxed(lean_object* v_upperBound_960_, lean_object* v_xs_961_, lean_object* v_next_962_, lean_object* v_inst_963_, lean_object* v_R_964_, lean_object* v_a_965_, lean_object* v_b_966_, lean_object* v_c_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(v_upperBound_960_, v_xs_961_, v_next_962_, v_inst_963_, v_R_964_, v_a_965_, v_b_966_, v_c_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_next_962_);
lean_dec_ref(v_xs_961_);
lean_dec(v_upperBound_960_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(lean_object* v_upperBound_974_, lean_object* v___x_975_, lean_object* v_xs_976_, lean_object* v_inst_977_, lean_object* v_R_978_, lean_object* v_a_979_, lean_object* v_b_980_, lean_object* v_c_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_974_, v___x_975_, v_xs_976_, v_a_979_, v_b_980_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___boxed(lean_object* v_upperBound_988_, lean_object* v___x_989_, lean_object* v_xs_990_, lean_object* v_inst_991_, lean_object* v_R_992_, lean_object* v_a_993_, lean_object* v_b_994_, lean_object* v_c_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(v_upperBound_988_, v___x_989_, v_xs_990_, v_inst_991_, v_R_992_, v_a_993_, v_b_994_, v_c_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec_ref(v_xs_990_);
lean_dec(v___x_989_);
lean_dec(v_upperBound_988_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___f_1009_; lean_object* v___x_32928__overap_1010_; lean_object* v___x_1011_; 
v___f_1009_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_32928__overap_1010_ = lean_panic_fn_borrowed(v___f_1009_, v_msg_1003_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
v___x_1011_ = lean_apply_5(v___x_32928__overap_1010_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, lean_box(0));
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object* v_msg_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_msg_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t v_sz_1019_, size_t v_i_1020_, lean_object* v_bs_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_usize_dec_lt(v_i_1020_, v_sz_1019_);
if (v___x_1022_ == 0)
{
return v_bs_1021_;
}
else
{
lean_object* v_v_1023_; lean_object* v___x_1024_; lean_object* v_bs_x27_1025_; lean_object* v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v_v_1023_ = lean_array_uget(v_bs_1021_, v_i_1020_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v_bs_x27_1025_ = lean_array_uset(v_bs_1021_, v_i_1020_, v___x_1024_);
v___x_1026_ = lean_array_get_size(v_v_1023_);
lean_dec(v_v_1023_);
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = lean_usize_add(v_i_1020_, v___x_1027_);
v___x_1029_ = lean_array_uset(v_bs_x27_1025_, v_i_1020_, v___x_1026_);
v_i_1020_ = v___x_1028_;
v_bs_1021_ = v___x_1029_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object* v_sz_1031_, lean_object* v_i_1032_, lean_object* v_bs_1033_){
_start:
{
size_t v_sz_boxed_1034_; size_t v_i_boxed_1035_; lean_object* v_res_1036_; 
v_sz_boxed_1034_ = lean_unbox_usize(v_sz_1031_);
lean_dec(v_sz_1031_);
v_i_boxed_1035_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_res_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_boxed_1034_, v_i_boxed_1035_, v_bs_1033_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t v_sz_1037_, size_t v_i_1038_, lean_object* v_bs_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_usize_dec_lt(v_i_1038_, v_sz_1037_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_bs_1039_);
return v___x_1046_;
}
else
{
lean_object* v_v_1047_; lean_object* v_value_1048_; lean_object* v___x_1049_; 
v_v_1047_ = lean_array_uget_borrowed(v_bs_1039_, v_i_1038_);
v_value_1048_ = lean_ctor_get(v_v_1047_, 7);
lean_inc_ref(v_value_1048_);
v___x_1049_ = l_Lean_Elab_getParamRevDeps(v_value_1048_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v_bs_x27_1052_; size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref_known(v___x_1049_, 1);
v___x_1051_ = lean_unsigned_to_nat(0u);
v_bs_x27_1052_ = lean_array_uset(v_bs_1039_, v_i_1038_, v___x_1051_);
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_add(v_i_1038_, v___x_1053_);
v___x_1055_ = lean_array_uset(v_bs_x27_1052_, v_i_1038_, v_a_1050_);
v_i_1038_ = v___x_1054_;
v_bs_1039_ = v___x_1055_;
goto _start;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_bs_1039_);
v_a_1057_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1049_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1049_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object* v_sz_1065_, lean_object* v_i_1066_, lean_object* v_bs_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
size_t v_sz_boxed_1073_; size_t v_i_boxed_1074_; lean_object* v_res_1075_; 
v_sz_boxed_1073_ = lean_unbox_usize(v_sz_1065_);
lean_dec(v_sz_1065_);
v_i_boxed_1074_ = lean_unbox_usize(v_i_1066_);
lean_dec(v_i_1066_);
v_res_1075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_boxed_1073_, v_i_boxed_1074_, v_bs_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(lean_object* v_msgData_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; lean_object* v_env_1083_; lean_object* v___x_1084_; lean_object* v_mctx_1085_; lean_object* v_lctx_1086_; lean_object* v_options_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1082_ = lean_st_ref_get(v___y_1080_);
v_env_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_env_1083_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_st_ref_get(v___y_1078_);
v_mctx_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_mctx_1085_);
lean_dec(v___x_1084_);
v_lctx_1086_ = lean_ctor_get(v___y_1077_, 2);
v_options_1087_ = lean_ctor_get(v___y_1079_, 2);
lean_inc_ref(v_options_1087_);
lean_inc_ref(v_lctx_1086_);
v___x_1088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1088_, 0, v_env_1083_);
lean_ctor_set(v___x_1088_, 1, v_mctx_1085_);
lean_ctor_set(v___x_1088_, 2, v_lctx_1086_);
lean_ctor_set(v___x_1088_, 3, v_options_1087_);
v___x_1089_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_msgData_1076_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2___boxed(lean_object* v_msgData_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msgData_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1098_; double v___x_1099_; 
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_float_of_nat(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object* v_cls_1103_, lean_object* v_msg_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_ref_1110_; lean_object* v___x_1111_; lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1156_; 
v_ref_1110_ = lean_ctor_get(v___y_1107_, 5);
v___x_1111_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1156_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1156_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v_traceState_1117_; lean_object* v_env_1118_; lean_object* v_nextMacroScope_1119_; lean_object* v_ngen_1120_; lean_object* v_auxDeclNGen_1121_; lean_object* v_cache_1122_; lean_object* v_messages_1123_; lean_object* v_infoState_1124_; lean_object* v_snapshotTasks_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1155_; 
v___x_1116_ = lean_st_ref_take(v___y_1108_);
v_traceState_1117_ = lean_ctor_get(v___x_1116_, 4);
v_env_1118_ = lean_ctor_get(v___x_1116_, 0);
v_nextMacroScope_1119_ = lean_ctor_get(v___x_1116_, 1);
v_ngen_1120_ = lean_ctor_get(v___x_1116_, 2);
v_auxDeclNGen_1121_ = lean_ctor_get(v___x_1116_, 3);
v_cache_1122_ = lean_ctor_get(v___x_1116_, 5);
v_messages_1123_ = lean_ctor_get(v___x_1116_, 6);
v_infoState_1124_ = lean_ctor_get(v___x_1116_, 7);
v_snapshotTasks_1125_ = lean_ctor_get(v___x_1116_, 8);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1127_ = v___x_1116_;
v_isShared_1128_ = v_isSharedCheck_1155_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_snapshotTasks_1125_);
lean_inc(v_infoState_1124_);
lean_inc(v_messages_1123_);
lean_inc(v_cache_1122_);
lean_inc(v_traceState_1117_);
lean_inc(v_auxDeclNGen_1121_);
lean_inc(v_ngen_1120_);
lean_inc(v_nextMacroScope_1119_);
lean_inc(v_env_1118_);
lean_dec(v___x_1116_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1155_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
uint64_t v_tid_1129_; lean_object* v_traces_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1154_; 
v_tid_1129_ = lean_ctor_get_uint64(v_traceState_1117_, sizeof(void*)*1);
v_traces_1130_ = lean_ctor_get(v_traceState_1117_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_traceState_1117_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1132_ = v_traceState_1117_;
v_isShared_1133_ = v_isSharedCheck_1154_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_traces_1130_);
lean_dec(v_traceState_1117_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1154_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; double v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_1136_ = 0;
v___x_1137_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_1138_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1138_, 0, v_cls_1103_);
lean_ctor_set(v___x_1138_, 1, v___x_1134_);
lean_ctor_set(v___x_1138_, 2, v___x_1137_);
lean_ctor_set_float(v___x_1138_, sizeof(void*)*3, v___x_1135_);
lean_ctor_set_float(v___x_1138_, sizeof(void*)*3 + 8, v___x_1135_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*3 + 16, v___x_1136_);
v___x_1139_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_1140_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v_a_1112_);
lean_ctor_set(v___x_1140_, 2, v___x_1139_);
lean_inc(v_ref_1110_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_ref_1110_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_PersistentArray_push___redArg(v_traces_1130_, v___x_1141_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1142_);
v___x_1144_ = v___x_1132_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1142_);
lean_ctor_set_uint64(v_reuseFailAlloc_1153_, sizeof(void*)*1, v_tid_1129_);
v___x_1144_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 4, v___x_1144_);
v___x_1146_ = v___x_1127_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_env_1118_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_nextMacroScope_1119_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_ngen_1120_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_auxDeclNGen_1121_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1152_, 5, v_cache_1122_);
lean_ctor_set(v_reuseFailAlloc_1152_, 6, v_messages_1123_);
lean_ctor_set(v_reuseFailAlloc_1152_, 7, v_infoState_1124_);
lean_ctor_set(v_reuseFailAlloc_1152_, 8, v_snapshotTasks_1125_);
v___x_1146_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1147_ = lean_st_ref_set(v___y_1108_, v___x_1146_);
v___x_1148_ = lean_box(0);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1148_);
v___x_1150_ = v___x_1114_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_1157_, lean_object* v_msg_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_1157_, v_msg_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object* v_00_u03b1_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_apply_1(v_x_1166_, lean_box(0));
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object* v_00_u03b1_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(v_00_u03b1_1174_, v_x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object* v_x_1182_, lean_object* v_x_1183_){
_start:
{
if (lean_obj_tag(v_x_1183_) == 0)
{
return v_x_1182_;
}
else
{
lean_object* v_key_1184_; lean_object* v_value_1185_; lean_object* v_tail_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1209_; 
v_key_1184_ = lean_ctor_get(v_x_1183_, 0);
v_value_1185_ = lean_ctor_get(v_x_1183_, 1);
v_tail_1186_ = lean_ctor_get(v_x_1183_, 2);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_x_1183_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1188_ = v_x_1183_;
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_tail_1186_);
lean_inc(v_value_1185_);
lean_inc(v_key_1184_);
lean_dec(v_x_1183_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1209_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; uint64_t v___x_1191_; uint64_t v___x_1192_; uint64_t v___x_1193_; uint64_t v_fold_1194_; uint64_t v___x_1195_; uint64_t v___x_1196_; uint64_t v___x_1197_; size_t v___x_1198_; size_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1190_ = lean_array_get_size(v_x_1182_);
v___x_1191_ = l_Lean_ExprStructEq_hash(v_key_1184_);
v___x_1192_ = 32ULL;
v___x_1193_ = lean_uint64_shift_right(v___x_1191_, v___x_1192_);
v_fold_1194_ = lean_uint64_xor(v___x_1191_, v___x_1193_);
v___x_1195_ = 16ULL;
v___x_1196_ = lean_uint64_shift_right(v_fold_1194_, v___x_1195_);
v___x_1197_ = lean_uint64_xor(v_fold_1194_, v___x_1196_);
v___x_1198_ = lean_uint64_to_usize(v___x_1197_);
v___x_1199_ = lean_usize_of_nat(v___x_1190_);
v___x_1200_ = ((size_t)1ULL);
v___x_1201_ = lean_usize_sub(v___x_1199_, v___x_1200_);
v___x_1202_ = lean_usize_land(v___x_1198_, v___x_1201_);
v___x_1203_ = lean_array_uget_borrowed(v_x_1182_, v___x_1202_);
lean_inc(v___x_1203_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 2, v___x_1203_);
v___x_1205_ = v___x_1188_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_key_1184_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_value_1185_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_array_uset(v_x_1182_, v___x_1202_, v___x_1205_);
v_x_1182_ = v___x_1206_;
v_x_1183_ = v_tail_1186_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object* v_i_1210_, lean_object* v_source_1211_, lean_object* v_target_1212_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_array_get_size(v_source_1211_);
v___x_1214_ = lean_nat_dec_lt(v_i_1210_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_dec_ref(v_source_1211_);
lean_dec(v_i_1210_);
return v_target_1212_;
}
else
{
lean_object* v_es_1215_; lean_object* v___x_1216_; lean_object* v_source_1217_; lean_object* v_target_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_es_1215_ = lean_array_fget(v_source_1211_, v_i_1210_);
v___x_1216_ = lean_box(0);
v_source_1217_ = lean_array_fset(v_source_1211_, v_i_1210_, v___x_1216_);
v_target_1218_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_target_1212_, v_es_1215_);
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_nat_add(v_i_1210_, v___x_1219_);
lean_dec(v_i_1210_);
v_i_1210_ = v___x_1220_;
v_source_1211_ = v_source_1217_;
v_target_1212_ = v_target_1218_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object* v_data_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_nbuckets_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1223_ = lean_array_get_size(v_data_1222_);
v___x_1224_ = lean_unsigned_to_nat(2u);
v_nbuckets_1225_ = lean_nat_mul(v___x_1223_, v___x_1224_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_mk_array(v_nbuckets_1225_, v___x_1227_);
v___x_1229_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1226_, v_data_1222_, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object* v_a_1230_, lean_object* v_b_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_dec(v_b_1231_);
lean_dec_ref(v_a_1230_);
return v_x_1232_;
}
else
{
lean_object* v_key_1233_; lean_object* v_value_1234_; lean_object* v_tail_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1247_; 
v_key_1233_ = lean_ctor_get(v_x_1232_, 0);
v_value_1234_ = lean_ctor_get(v_x_1232_, 1);
v_tail_1235_ = lean_ctor_get(v_x_1232_, 2);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_x_1232_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1237_ = v_x_1232_;
v_isShared_1238_ = v_isSharedCheck_1247_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_tail_1235_);
lean_inc(v_value_1234_);
lean_inc(v_key_1233_);
lean_dec(v_x_1232_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1247_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
uint8_t v___x_1239_; 
v___x_1239_ = l_Lean_ExprStructEq_beq(v_key_1233_, v_a_1230_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1230_, v_b_1231_, v_tail_1235_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 2, v___x_1240_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_key_1233_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_value_1234_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
else
{
lean_object* v___x_1245_; 
lean_dec(v_value_1234_);
lean_dec(v_key_1233_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_b_1231_);
lean_ctor_set(v___x_1237_, 0, v_a_1230_);
v___x_1245_ = v___x_1237_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1230_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_b_1231_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_tail_1235_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_a_1248_, lean_object* v_x_1249_){
_start:
{
if (lean_obj_tag(v_x_1249_) == 0)
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
else
{
lean_object* v_key_1251_; lean_object* v_tail_1252_; uint8_t v___x_1253_; 
v_key_1251_ = lean_ctor_get(v_x_1249_, 0);
v_tail_1252_ = lean_ctor_get(v_x_1249_, 2);
v___x_1253_ = l_Lean_ExprStructEq_beq(v_key_1251_, v_a_1248_);
if (v___x_1253_ == 0)
{
v_x_1249_ = v_tail_1252_;
goto _start;
}
else
{
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_a_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1255_, v_x_1256_);
lean_dec(v_x_1256_);
lean_dec_ref(v_a_1255_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_){
_start:
{
lean_object* v_size_1262_; lean_object* v_buckets_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1306_; 
v_size_1262_ = lean_ctor_get(v_m_1259_, 0);
v_buckets_1263_ = lean_ctor_get(v_m_1259_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_m_1259_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1265_ = v_m_1259_;
v_isShared_1266_ = v_isSharedCheck_1306_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_buckets_1263_);
lean_inc(v_size_1262_);
lean_dec(v_m_1259_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1306_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; uint64_t v___x_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v_fold_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; size_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; lean_object* v_bkt_1280_; uint8_t v___x_1281_; 
v___x_1267_ = lean_array_get_size(v_buckets_1263_);
v___x_1268_ = l_Lean_ExprStructEq_hash(v_a_1260_);
v___x_1269_ = 32ULL;
v___x_1270_ = lean_uint64_shift_right(v___x_1268_, v___x_1269_);
v_fold_1271_ = lean_uint64_xor(v___x_1268_, v___x_1270_);
v___x_1272_ = 16ULL;
v___x_1273_ = lean_uint64_shift_right(v_fold_1271_, v___x_1272_);
v___x_1274_ = lean_uint64_xor(v_fold_1271_, v___x_1273_);
v___x_1275_ = lean_uint64_to_usize(v___x_1274_);
v___x_1276_ = lean_usize_of_nat(v___x_1267_);
v___x_1277_ = ((size_t)1ULL);
v___x_1278_ = lean_usize_sub(v___x_1276_, v___x_1277_);
v___x_1279_ = lean_usize_land(v___x_1275_, v___x_1278_);
v_bkt_1280_ = lean_array_uget_borrowed(v_buckets_1263_, v___x_1279_);
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1260_, v_bkt_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v_size_x27_1283_; lean_object* v___x_1284_; lean_object* v_buckets_x27_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1282_ = lean_unsigned_to_nat(1u);
v_size_x27_1283_ = lean_nat_add(v_size_1262_, v___x_1282_);
lean_dec(v_size_1262_);
lean_inc(v_bkt_1280_);
v___x_1284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1284_, 0, v_a_1260_);
lean_ctor_set(v___x_1284_, 1, v_b_1261_);
lean_ctor_set(v___x_1284_, 2, v_bkt_1280_);
v_buckets_x27_1285_ = lean_array_uset(v_buckets_1263_, v___x_1279_, v___x_1284_);
v___x_1286_ = lean_unsigned_to_nat(4u);
v___x_1287_ = lean_nat_mul(v_size_x27_1283_, v___x_1286_);
v___x_1288_ = lean_unsigned_to_nat(3u);
v___x_1289_ = lean_nat_div(v___x_1287_, v___x_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_array_get_size(v_buckets_x27_1285_);
v___x_1291_ = lean_nat_dec_le(v___x_1289_, v___x_1290_);
lean_dec(v___x_1289_);
if (v___x_1291_ == 0)
{
lean_object* v_val_1292_; lean_object* v___x_1294_; 
v_val_1292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_buckets_x27_1285_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v_val_1292_);
lean_ctor_set(v___x_1265_, 0, v_size_x27_1283_);
v___x_1294_ = v___x_1265_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_size_x27_1283_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_val_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
else
{
lean_object* v___x_1297_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v_buckets_x27_1285_);
lean_ctor_set(v___x_1265_, 0, v_size_x27_1283_);
v___x_1297_ = v___x_1265_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_size_x27_1283_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_buckets_x27_1285_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v___x_1299_; lean_object* v_buckets_x27_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_inc(v_bkt_1280_);
v___x_1299_ = lean_box(0);
v_buckets_x27_1300_ = lean_array_uset(v_buckets_1263_, v___x_1279_, v___x_1299_);
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1260_, v_b_1261_, v_bkt_1280_);
v___x_1302_ = lean_array_uset(v_buckets_x27_1300_, v___x_1279_, v___x_1301_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v___x_1302_);
v___x_1304_ = v___x_1265_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_size_1262_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1307_, lean_object* v_e_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_st_ref_take(v_a_1307_);
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1311_, v_e_1308_, v_a_1309_);
v___x_1313_ = lean_st_ref_set(v_a_1307_, v___x_1312_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1315_, lean_object* v_e_1316_, lean_object* v_a_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1315_, v_e_1316_, v_a_1317_);
lean_dec(v_a_1315_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1320_, lean_object* v___y_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
lean_inc(v___y_1324_);
lean_inc_ref(v___y_1323_);
lean_inc(v___y_1321_);
v___x_1328_ = lean_apply_7(v_k_1320_, v_b_1322_, v___y_1321_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, lean_box(0));
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1329_, lean_object* v___y_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1329_, v___y_1330_, v_b_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1330_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1338_, uint8_t v_bi_1339_, lean_object* v_type_1340_, lean_object* v_k_1341_, uint8_t v_kind_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___f_1349_; lean_object* v___x_1350_; 
lean_inc(v___y_1343_);
v___f_1349_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1349_, 0, v_k_1341_);
lean_closure_set(v___f_1349_, 1, v___y_1343_);
v___x_1350_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1338_, v_bi_1339_, v_type_1340_, v___f_1349_, v_kind_1342_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
if (lean_obj_tag(v___x_1350_) == 0)
{
return v___x_1350_;
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1359_, lean_object* v_bi_1360_, lean_object* v_type_1361_, lean_object* v_k_1362_, lean_object* v_kind_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_bi_boxed_1370_; uint8_t v_kind_boxed_1371_; lean_object* v_res_1372_; 
v_bi_boxed_1370_ = lean_unbox(v_bi_1360_);
v_kind_boxed_1371_ = lean_unbox(v_kind_1363_);
v_res_1372_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1359_, v_bi_boxed_1370_, v_type_1361_, v_k_1362_, v_kind_boxed_1371_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object* v___x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1373_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object* v___x_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1387_, lean_object* v_type_1388_, lean_object* v_val_1389_, lean_object* v_k_1390_, uint8_t v_nondep_1391_, uint8_t v_kind_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___f_1399_; lean_object* v___x_1400_; 
lean_inc(v___y_1393_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1399_, 0, v_k_1390_);
lean_closure_set(v___f_1399_, 1, v___y_1393_);
v___x_1400_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1387_, v_type_1388_, v_val_1389_, v___f_1399_, v_nondep_1391_, v_kind_1392_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1400_) == 0)
{
return v___x_1400_;
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1409_, lean_object* v_type_1410_, lean_object* v_val_1411_, lean_object* v_k_1412_, lean_object* v_nondep_1413_, lean_object* v_kind_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v_nondep_boxed_1421_; uint8_t v_kind_boxed_1422_; lean_object* v_res_1423_; 
v_nondep_boxed_1421_ = lean_unbox(v_nondep_1413_);
v_kind_boxed_1422_ = lean_unbox(v_kind_1414_);
v_res_1423_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1409_, v_type_1410_, v_val_1411_, v_k_1412_, v_nondep_boxed_1421_, v_kind_boxed_1422_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_apply_1(v_x_1425_, lean_box(0));
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1433_, lean_object* v_x_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1433_, v_x_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1440_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = l_Lean_maxRecDepthErrorMessage;
v___x_1447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
return v___x_1447_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1449_ = l_Lean_MessageData_ofFormat(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1451_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1452_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
lean_ctor_set(v___x_1452_, 1, v___x_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1453_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_ref_1453_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___y_1469_; lean_object* v_fileName_1478_; lean_object* v_fileMap_1479_; lean_object* v_options_1480_; lean_object* v_currRecDepth_1481_; lean_object* v_maxRecDepth_1482_; lean_object* v_ref_1483_; lean_object* v_currNamespace_1484_; lean_object* v_openDecls_1485_; lean_object* v_initHeartbeats_1486_; lean_object* v_maxHeartbeats_1487_; lean_object* v_quotContext_1488_; lean_object* v_currMacroScope_1489_; uint8_t v_diag_1490_; lean_object* v_cancelTk_x3f_1491_; uint8_t v_suppressElabErrors_1492_; lean_object* v_inheritedTraceOptions_1493_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v_fileName_1478_ = lean_ctor_get(v___y_1465_, 0);
v_fileMap_1479_ = lean_ctor_get(v___y_1465_, 1);
v_options_1480_ = lean_ctor_get(v___y_1465_, 2);
v_currRecDepth_1481_ = lean_ctor_get(v___y_1465_, 3);
v_maxRecDepth_1482_ = lean_ctor_get(v___y_1465_, 4);
v_ref_1483_ = lean_ctor_get(v___y_1465_, 5);
v_currNamespace_1484_ = lean_ctor_get(v___y_1465_, 6);
v_openDecls_1485_ = lean_ctor_get(v___y_1465_, 7);
v_initHeartbeats_1486_ = lean_ctor_get(v___y_1465_, 8);
v_maxHeartbeats_1487_ = lean_ctor_get(v___y_1465_, 9);
v_quotContext_1488_ = lean_ctor_get(v___y_1465_, 10);
v_currMacroScope_1489_ = lean_ctor_get(v___y_1465_, 11);
v_diag_1490_ = lean_ctor_get_uint8(v___y_1465_, sizeof(void*)*14);
v_cancelTk_x3f_1491_ = lean_ctor_get(v___y_1465_, 12);
v_suppressElabErrors_1492_ = lean_ctor_get_uint8(v___y_1465_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1493_ = lean_ctor_get(v___y_1465_, 13);
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_nat_dec_eq(v_maxRecDepth_1482_, v___x_1499_);
if (v___x_1500_ == 0)
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_nat_dec_eq(v_currRecDepth_1481_, v_maxRecDepth_1482_);
if (v___x_1501_ == 0)
{
goto v___jp_1494_;
}
else
{
lean_object* v___x_1502_; 
lean_dec_ref(v_x_1461_);
lean_inc(v_ref_1483_);
v___x_1502_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1483_);
v___y_1469_ = v___x_1502_;
goto v___jp_1468_;
}
}
else
{
goto v___jp_1494_;
}
v___jp_1468_:
{
if (lean_obj_tag(v___y_1469_) == 0)
{
return v___y_1469_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___y_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___y_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___y_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___y_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
v___jp_1494_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_nat_add(v_currRecDepth_1481_, v___x_1495_);
lean_inc_ref(v_inheritedTraceOptions_1493_);
lean_inc(v_cancelTk_x3f_1491_);
lean_inc(v_currMacroScope_1489_);
lean_inc(v_quotContext_1488_);
lean_inc(v_maxHeartbeats_1487_);
lean_inc(v_initHeartbeats_1486_);
lean_inc(v_openDecls_1485_);
lean_inc(v_currNamespace_1484_);
lean_inc(v_ref_1483_);
lean_inc(v_maxRecDepth_1482_);
lean_inc_ref(v_options_1480_);
lean_inc_ref(v_fileMap_1479_);
lean_inc_ref(v_fileName_1478_);
v___x_1497_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1497_, 0, v_fileName_1478_);
lean_ctor_set(v___x_1497_, 1, v_fileMap_1479_);
lean_ctor_set(v___x_1497_, 2, v_options_1480_);
lean_ctor_set(v___x_1497_, 3, v___x_1496_);
lean_ctor_set(v___x_1497_, 4, v_maxRecDepth_1482_);
lean_ctor_set(v___x_1497_, 5, v_ref_1483_);
lean_ctor_set(v___x_1497_, 6, v_currNamespace_1484_);
lean_ctor_set(v___x_1497_, 7, v_openDecls_1485_);
lean_ctor_set(v___x_1497_, 8, v_initHeartbeats_1486_);
lean_ctor_set(v___x_1497_, 9, v_maxHeartbeats_1487_);
lean_ctor_set(v___x_1497_, 10, v_quotContext_1488_);
lean_ctor_set(v___x_1497_, 11, v_currMacroScope_1489_);
lean_ctor_set(v___x_1497_, 12, v_cancelTk_x3f_1491_);
lean_ctor_set(v___x_1497_, 13, v_inheritedTraceOptions_1493_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*14, v_diag_1490_);
lean_ctor_set_uint8(v___x_1497_, sizeof(void*)*14 + 1, v_suppressElabErrors_1492_);
lean_inc(v___y_1466_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v___y_1462_);
v___x_1498_ = lean_apply_6(v_x_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___x_1497_, v___y_1466_, lean_box(0));
v___y_1469_ = v___x_1498_;
goto v___jp_1468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1511_, lean_object* v_x_1512_){
_start:
{
if (lean_obj_tag(v_x_1512_) == 0)
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_box(0);
return v___x_1513_;
}
else
{
lean_object* v_key_1514_; lean_object* v_value_1515_; lean_object* v_tail_1516_; uint8_t v___x_1517_; 
v_key_1514_ = lean_ctor_get(v_x_1512_, 0);
v_value_1515_ = lean_ctor_get(v_x_1512_, 1);
v_tail_1516_ = lean_ctor_get(v_x_1512_, 2);
v___x_1517_ = l_Lean_ExprStructEq_beq(v_key_1514_, v_a_1511_);
if (v___x_1517_ == 0)
{
v_x_1512_ = v_tail_1516_;
goto _start;
}
else
{
lean_object* v___x_1519_; 
lean_inc(v_value_1515_);
v___x_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_value_1515_);
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1520_, lean_object* v_x_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1520_, v_x_1521_);
lean_dec(v_x_1521_);
lean_dec_ref(v_a_1520_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_buckets_1525_; lean_object* v___x_1526_; uint64_t v___x_1527_; uint64_t v___x_1528_; uint64_t v___x_1529_; uint64_t v_fold_1530_; uint64_t v___x_1531_; uint64_t v___x_1532_; uint64_t v___x_1533_; size_t v___x_1534_; size_t v___x_1535_; size_t v___x_1536_; size_t v___x_1537_; size_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_buckets_1525_ = lean_ctor_get(v_m_1523_, 1);
v___x_1526_ = lean_array_get_size(v_buckets_1525_);
v___x_1527_ = l_Lean_ExprStructEq_hash(v_a_1524_);
v___x_1528_ = 32ULL;
v___x_1529_ = lean_uint64_shift_right(v___x_1527_, v___x_1528_);
v_fold_1530_ = lean_uint64_xor(v___x_1527_, v___x_1529_);
v___x_1531_ = 16ULL;
v___x_1532_ = lean_uint64_shift_right(v_fold_1530_, v___x_1531_);
v___x_1533_ = lean_uint64_xor(v_fold_1530_, v___x_1532_);
v___x_1534_ = lean_uint64_to_usize(v___x_1533_);
v___x_1535_ = lean_usize_of_nat(v___x_1526_);
v___x_1536_ = ((size_t)1ULL);
v___x_1537_ = lean_usize_sub(v___x_1535_, v___x_1536_);
v___x_1538_ = lean_usize_land(v___x_1534_, v___x_1537_);
v___x_1539_ = lean_array_uget_borrowed(v_buckets_1525_, v___x_1538_);
v___x_1540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1524_, v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1541_, v_a_1542_);
lean_dec_ref(v_a_1542_);
lean_dec_ref(v_m_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1547_, lean_object* v_pre_1548_, lean_object* v_post_1549_, uint8_t v_usedLetOnly_1550_, uint8_t v_skipConstInApp_1551_, uint8_t v_skipInstances_1552_, lean_object* v_body_1553_, lean_object* v_x_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_array_push(v_fvars_1547_, v_x_1554_);
v___x_1562_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1548_, v_post_1549_, v_usedLetOnly_1550_, v_skipConstInApp_1551_, v_skipInstances_1552_, v___x_1561_, v_body_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1563_, lean_object* v_pre_1564_, lean_object* v_post_1565_, lean_object* v_usedLetOnly_1566_, lean_object* v_skipConstInApp_1567_, lean_object* v_skipInstances_1568_, lean_object* v_body_1569_, lean_object* v_x_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v_usedLetOnly_boxed_1577_; uint8_t v_skipConstInApp_boxed_1578_; uint8_t v_skipInstances_boxed_1579_; lean_object* v_res_1580_; 
v_usedLetOnly_boxed_1577_ = lean_unbox(v_usedLetOnly_1566_);
v_skipConstInApp_boxed_1578_ = lean_unbox(v_skipConstInApp_1567_);
v_skipInstances_boxed_1579_ = lean_unbox(v_skipInstances_1568_);
v_res_1580_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1563_, v_pre_1564_, v_post_1565_, v_usedLetOnly_boxed_1577_, v_skipConstInApp_boxed_1578_, v_skipInstances_boxed_1579_, v_body_1569_, v_x_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1581_, lean_object* v_post_1582_, uint8_t v_usedLetOnly_1583_, uint8_t v_skipConstInApp_1584_, uint8_t v_skipInstances_1585_, lean_object* v_e_1586_, lean_object* v_a_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; 
lean_inc_ref(v_post_1582_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc_ref(v_e_1586_);
v___x_1593_ = lean_apply_6(v_post_1582_, v_e_1586_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, lean_box(0));
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1612_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1612_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1612_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
switch(lean_obj_tag(v_a_1594_))
{
case 0:
{
lean_object* v_e_1598_; lean_object* v___x_1600_; 
lean_dec_ref(v_e_1586_);
lean_dec_ref(v_post_1582_);
lean_dec_ref(v_pre_1581_);
v_e_1598_ = lean_ctor_get(v_a_1594_, 0);
lean_inc_ref(v_e_1598_);
lean_dec_ref_known(v_a_1594_, 1);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_e_1598_);
v___x_1600_ = v___x_1596_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_e_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
case 1:
{
lean_object* v_e_1602_; lean_object* v___x_1603_; 
lean_del_object(v___x_1596_);
lean_dec_ref(v_e_1586_);
v_e_1602_ = lean_ctor_get(v_a_1594_, 0);
lean_inc_ref(v_e_1602_);
lean_dec_ref_known(v_a_1594_, 1);
v___x_1603_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1581_, v_post_1582_, v_usedLetOnly_1583_, v_skipConstInApp_1584_, v_skipInstances_1585_, v_e_1602_, v_a_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1603_;
}
default: 
{
lean_object* v_e_x3f_1604_; 
lean_dec_ref(v_post_1582_);
lean_dec_ref(v_pre_1581_);
v_e_x3f_1604_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_e_x3f_1604_);
lean_dec_ref_known(v_a_1594_, 1);
if (lean_obj_tag(v_e_x3f_1604_) == 0)
{
lean_object* v___x_1606_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_e_1586_);
v___x_1606_ = v___x_1596_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_e_1586_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
else
{
lean_object* v_val_1608_; lean_object* v___x_1610_; 
lean_dec_ref(v_e_1586_);
v_val_1608_ = lean_ctor_get(v_e_x3f_1604_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v_e_x3f_1604_, 1);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_val_1608_);
v___x_1610_ = v___x_1596_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_val_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_e_1586_);
lean_dec_ref(v_post_1582_);
lean_dec_ref(v_pre_1581_);
v_a_1613_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1593_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1593_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1621_, lean_object* v_post_1622_, uint8_t v_usedLetOnly_1623_, uint8_t v_skipConstInApp_1624_, uint8_t v_skipInstances_1625_, lean_object* v_fvars_1626_, lean_object* v_e_1627_, lean_object* v_a_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
if (lean_obj_tag(v_e_1627_) == 6)
{
lean_object* v_binderName_1634_; lean_object* v_binderType_1635_; lean_object* v_body_1636_; uint8_t v_binderInfo_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_binderName_1634_ = lean_ctor_get(v_e_1627_, 0);
lean_inc(v_binderName_1634_);
v_binderType_1635_ = lean_ctor_get(v_e_1627_, 1);
lean_inc_ref(v_binderType_1635_);
v_body_1636_ = lean_ctor_get(v_e_1627_, 2);
lean_inc_ref(v_body_1636_);
v_binderInfo_1637_ = lean_ctor_get_uint8(v_e_1627_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1627_, 3);
v___x_1638_ = lean_expr_instantiate_rev(v_binderType_1635_, v_fvars_1626_);
lean_dec_ref(v_binderType_1635_);
lean_inc_ref(v_post_1622_);
lean_inc_ref(v_pre_1621_);
v___x_1639_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1621_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___x_1638_, v_a_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___f_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = lean_box(v_usedLetOnly_1623_);
v___x_1642_ = lean_box(v_skipConstInApp_1624_);
v___x_1643_ = lean_box(v_skipInstances_1625_);
v___f_1644_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1644_, 0, v_fvars_1626_);
lean_closure_set(v___f_1644_, 1, v_pre_1621_);
lean_closure_set(v___f_1644_, 2, v_post_1622_);
lean_closure_set(v___f_1644_, 3, v___x_1641_);
lean_closure_set(v___f_1644_, 4, v___x_1642_);
lean_closure_set(v___f_1644_, 5, v___x_1643_);
lean_closure_set(v___f_1644_, 6, v_body_1636_);
v___x_1645_ = 0;
v___x_1646_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1634_, v_binderInfo_1637_, v_a_1640_, v___f_1644_, v___x_1645_, v_a_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1646_;
}
else
{
lean_dec_ref(v_body_1636_);
lean_dec(v_binderName_1634_);
lean_dec_ref(v_fvars_1626_);
lean_dec_ref(v_post_1622_);
lean_dec_ref(v_pre_1621_);
return v___x_1639_;
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_expr_instantiate_rev(v_e_1627_, v_fvars_1626_);
lean_dec_ref(v_e_1627_);
lean_inc_ref(v_post_1622_);
lean_inc_ref(v_pre_1621_);
v___x_1648_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1621_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v___x_1647_, v_a_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; uint8_t v___x_1650_; uint8_t v___x_1651_; uint8_t v___x_1652_; lean_object* v___x_1653_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = 0;
v___x_1651_ = 1;
v___x_1652_ = 1;
v___x_1653_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1626_, v_a_1649_, v___x_1650_, v_usedLetOnly_1623_, v___x_1650_, v___x_1651_, v___x_1652_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec_ref(v_fvars_1626_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1655_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1621_, v_post_1622_, v_usedLetOnly_1623_, v_skipConstInApp_1624_, v_skipInstances_1625_, v_a_1654_, v_a_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1655_;
}
else
{
lean_dec_ref(v_post_1622_);
lean_dec_ref(v_pre_1621_);
return v___x_1653_;
}
}
else
{
lean_dec_ref(v_fvars_1626_);
lean_dec_ref(v_post_1622_);
lean_dec_ref(v_pre_1621_);
return v___x_1648_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1656_, lean_object* v_pre_1657_, lean_object* v_post_1658_, uint8_t v_usedLetOnly_1659_, uint8_t v_skipConstInApp_1660_, uint8_t v_skipInstances_1661_, lean_object* v_body_1662_, lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_array_push(v_fvars_1656_, v_x_1663_);
v___x_1671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1657_, v_post_1658_, v_usedLetOnly_1659_, v_skipConstInApp_1660_, v_skipInstances_1661_, v___x_1670_, v_body_1662_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1672_, lean_object* v_pre_1673_, lean_object* v_post_1674_, lean_object* v_usedLetOnly_1675_, lean_object* v_skipConstInApp_1676_, lean_object* v_skipInstances_1677_, lean_object* v_body_1678_, lean_object* v_x_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v_usedLetOnly_boxed_1686_; uint8_t v_skipConstInApp_boxed_1687_; uint8_t v_skipInstances_boxed_1688_; lean_object* v_res_1689_; 
v_usedLetOnly_boxed_1686_ = lean_unbox(v_usedLetOnly_1675_);
v_skipConstInApp_boxed_1687_ = lean_unbox(v_skipConstInApp_1676_);
v_skipInstances_boxed_1688_ = lean_unbox(v_skipInstances_1677_);
v_res_1689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1672_, v_pre_1673_, v_post_1674_, v_usedLetOnly_boxed_1686_, v_skipConstInApp_boxed_1687_, v_skipInstances_boxed_1688_, v_body_1678_, v_x_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1690_, lean_object* v_post_1691_, uint8_t v_usedLetOnly_1692_, uint8_t v_skipConstInApp_1693_, uint8_t v_skipInstances_1694_, lean_object* v_fvars_1695_, lean_object* v_e_1696_, lean_object* v_a_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
if (lean_obj_tag(v_e_1696_) == 8)
{
lean_object* v_declName_1703_; lean_object* v_type_1704_; lean_object* v_value_1705_; lean_object* v_body_1706_; uint8_t v_nondep_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_declName_1703_ = lean_ctor_get(v_e_1696_, 0);
lean_inc(v_declName_1703_);
v_type_1704_ = lean_ctor_get(v_e_1696_, 1);
lean_inc_ref(v_type_1704_);
v_value_1705_ = lean_ctor_get(v_e_1696_, 2);
lean_inc_ref(v_value_1705_);
v_body_1706_ = lean_ctor_get(v_e_1696_, 3);
lean_inc_ref(v_body_1706_);
v_nondep_1707_ = lean_ctor_get_uint8(v_e_1696_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1696_, 4);
v___x_1708_ = lean_expr_instantiate_rev(v_type_1704_, v_fvars_1695_);
lean_dec_ref(v_type_1704_);
lean_inc_ref(v_post_1691_);
lean_inc_ref(v_pre_1690_);
v___x_1709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1690_, v_post_1691_, v_usedLetOnly_1692_, v_skipConstInApp_1693_, v_skipInstances_1694_, v___x_1708_, v_a_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v___x_1711_ = lean_expr_instantiate_rev(v_value_1705_, v_fvars_1695_);
lean_dec_ref(v_value_1705_);
lean_inc_ref(v_post_1691_);
lean_inc_ref(v_pre_1690_);
v___x_1712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1690_, v_post_1691_, v_usedLetOnly_1692_, v_skipConstInApp_1693_, v_skipInstances_1694_, v___x_1711_, v_a_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___f_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = lean_box(v_usedLetOnly_1692_);
v___x_1715_ = lean_box(v_skipConstInApp_1693_);
v___x_1716_ = lean_box(v_skipInstances_1694_);
v___f_1717_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1717_, 0, v_fvars_1695_);
lean_closure_set(v___f_1717_, 1, v_pre_1690_);
lean_closure_set(v___f_1717_, 2, v_post_1691_);
lean_closure_set(v___f_1717_, 3, v___x_1714_);
lean_closure_set(v___f_1717_, 4, v___x_1715_);
lean_closure_set(v___f_1717_, 5, v___x_1716_);
lean_closure_set(v___f_1717_, 6, v_body_1706_);
v___x_1718_ = 0;
v___x_1719_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1703_, v_a_1710_, v_a_1713_, v___f_1717_, v_nondep_1707_, v___x_1718_, v_a_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1719_;
}
else
{
lean_dec(v_a_1710_);
lean_dec_ref(v_body_1706_);
lean_dec(v_declName_1703_);
lean_dec_ref(v_fvars_1695_);
lean_dec_ref(v_post_1691_);
lean_dec_ref(v_pre_1690_);
return v___x_1712_;
}
}
else
{
lean_dec_ref(v_body_1706_);
lean_dec_ref(v_value_1705_);
lean_dec(v_declName_1703_);
lean_dec_ref(v_fvars_1695_);
lean_dec_ref(v_post_1691_);
lean_dec_ref(v_pre_1690_);
return v___x_1709_;
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_expr_instantiate_rev(v_e_1696_, v_fvars_1695_);
lean_dec_ref(v_e_1696_);
lean_inc_ref(v_post_1691_);
lean_inc_ref(v_pre_1690_);
v___x_1721_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1690_, v_post_1691_, v_usedLetOnly_1692_, v_skipConstInApp_1693_, v_skipInstances_1694_, v___x_1720_, v_a_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; uint8_t v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = 0;
v___x_1724_ = 1;
v___x_1725_ = l_Lean_Meta_mkLetFVars(v_fvars_1695_, v_a_1722_, v_usedLetOnly_1692_, v___x_1723_, v___x_1724_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec_ref(v_fvars_1695_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1690_, v_post_1691_, v_usedLetOnly_1692_, v_skipConstInApp_1693_, v_skipInstances_1694_, v_a_1726_, v_a_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
return v___x_1727_;
}
else
{
lean_dec_ref(v_post_1691_);
lean_dec_ref(v_pre_1690_);
return v___x_1725_;
}
}
else
{
lean_dec_ref(v_fvars_1695_);
lean_dec_ref(v_post_1691_);
lean_dec_ref(v_pre_1690_);
return v___x_1721_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1728_; lean_object* v_dummy_1729_; 
v___x_1728_ = lean_box(0);
v_dummy_1729_ = l_Lean_Expr_sort___override(v___x_1728_);
return v_dummy_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1730_, lean_object* v_post_1731_, uint8_t v_usedLetOnly_1732_, uint8_t v_skipConstInApp_1733_, uint8_t v_skipInstances_1734_, size_t v_sz_1735_, size_t v_i_1736_, lean_object* v_bs_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_lt(v_i_1736_, v_sz_1735_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref(v_post_1731_);
lean_dec_ref(v_pre_1730_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_bs_1737_);
return v___x_1745_;
}
else
{
lean_object* v_v_1746_; lean_object* v___x_1747_; 
v_v_1746_ = lean_array_uget_borrowed(v_bs_1737_, v_i_1736_);
lean_inc(v_v_1746_);
lean_inc_ref(v_post_1731_);
lean_inc_ref(v_pre_1730_);
v___x_1747_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1730_, v_post_1731_, v_usedLetOnly_1732_, v_skipConstInApp_1733_, v_skipInstances_1734_, v_v_1746_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; lean_object* v_bs_x27_1750_; size_t v___x_1751_; size_t v___x_1752_; lean_object* v___x_1753_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = lean_unsigned_to_nat(0u);
v_bs_x27_1750_ = lean_array_uset(v_bs_1737_, v_i_1736_, v___x_1749_);
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1736_, v___x_1751_);
v___x_1753_ = lean_array_uset(v_bs_x27_1750_, v_i_1736_, v_a_1748_);
v_i_1736_ = v___x_1752_;
v_bs_1737_ = v___x_1753_;
goto _start;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v_bs_1737_);
lean_dec_ref(v_post_1731_);
lean_dec_ref(v_pre_1730_);
v_a_1755_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1747_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1747_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1763_, lean_object* v_post_1764_, uint8_t v_usedLetOnly_1765_, uint8_t v_skipConstInApp_1766_, uint8_t v_skipInstances_1767_, lean_object* v___x_1768_, lean_object* v___y_1769_, lean_object* v_b_1770_, lean_object* v_a_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1763_, v_post_1764_, v_usedLetOnly_1765_, v_skipConstInApp_1766_, v_skipInstances_1767_, v___x_1768_, v___y_1769_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1787_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_array_fset(v_b_1770_, v_a_1771_, v_a_1778_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1783_);
v___x_1785_ = v___x_1780_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_b_1770_);
v_a_1788_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1777_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1777_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1796_, lean_object* v_post_1797_, lean_object* v_usedLetOnly_1798_, lean_object* v_skipConstInApp_1799_, lean_object* v_skipInstances_1800_, lean_object* v___x_1801_, lean_object* v___y_1802_, lean_object* v_b_1803_, lean_object* v_a_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
uint8_t v_usedLetOnly_boxed_1810_; uint8_t v_skipConstInApp_boxed_1811_; uint8_t v_skipInstances_boxed_1812_; lean_object* v_res_1813_; 
v_usedLetOnly_boxed_1810_ = lean_unbox(v_usedLetOnly_1798_);
v_skipConstInApp_boxed_1811_ = lean_unbox(v_skipConstInApp_1799_);
v_skipInstances_boxed_1812_ = lean_unbox(v_skipInstances_1800_);
v_res_1813_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1796_, v_post_1797_, v_usedLetOnly_boxed_1810_, v_skipConstInApp_boxed_1811_, v_skipInstances_boxed_1812_, v___x_1801_, v___y_1802_, v_b_1803_, v_a_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v_a_1804_);
lean_dec(v___y_1802_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1814_, lean_object* v___x_1815_, lean_object* v_pre_1816_, lean_object* v_post_1817_, uint8_t v_usedLetOnly_1818_, uint8_t v_skipConstInApp_1819_, uint8_t v_skipInstances_1820_, lean_object* v_a_1821_, lean_object* v_b_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___y_1830_; uint8_t v___x_1853_; 
v___x_1853_ = lean_nat_dec_lt(v_a_1821_, v_upperBound_1814_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_dec(v_a_1821_);
lean_dec_ref(v_post_1817_);
lean_dec_ref(v_pre_1816_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_b_1822_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1855_ = lean_array_fget_borrowed(v_b_1822_, v_a_1821_);
v___x_1856_ = lean_array_get_size(v___x_1815_);
v___x_1857_ = lean_nat_dec_lt(v_a_1821_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___f_1861_; 
lean_inc(v___x_1855_);
v___x_1858_ = lean_box(v_usedLetOnly_1818_);
v___x_1859_ = lean_box(v_skipConstInApp_1819_);
v___x_1860_ = lean_box(v_skipInstances_1820_);
lean_inc(v_a_1821_);
lean_inc(v___y_1823_);
lean_inc_ref(v_post_1817_);
lean_inc_ref(v_pre_1816_);
v___f_1861_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1861_, 0, v_pre_1816_);
lean_closure_set(v___f_1861_, 1, v_post_1817_);
lean_closure_set(v___f_1861_, 2, v___x_1858_);
lean_closure_set(v___f_1861_, 3, v___x_1859_);
lean_closure_set(v___f_1861_, 4, v___x_1860_);
lean_closure_set(v___f_1861_, 5, v___x_1855_);
lean_closure_set(v___f_1861_, 6, v___y_1823_);
lean_closure_set(v___f_1861_, 7, v_b_1822_);
lean_closure_set(v___f_1861_, 8, v_a_1821_);
v___y_1830_ = v___f_1861_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1862_; uint8_t v_isInstance_1863_; 
v___x_1862_ = lean_array_fget_borrowed(v___x_1815_, v_a_1821_);
v_isInstance_1863_ = lean_ctor_get_uint8(v___x_1862_, sizeof(void*)*1 + 4);
if (v_isInstance_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___f_1867_; 
lean_inc(v___x_1855_);
v___x_1864_ = lean_box(v_usedLetOnly_1818_);
v___x_1865_ = lean_box(v_skipConstInApp_1819_);
v___x_1866_ = lean_box(v_skipInstances_1820_);
lean_inc(v_a_1821_);
lean_inc(v___y_1823_);
lean_inc_ref(v_post_1817_);
lean_inc_ref(v_pre_1816_);
v___f_1867_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1867_, 0, v_pre_1816_);
lean_closure_set(v___f_1867_, 1, v_post_1817_);
lean_closure_set(v___f_1867_, 2, v___x_1864_);
lean_closure_set(v___f_1867_, 3, v___x_1865_);
lean_closure_set(v___f_1867_, 4, v___x_1866_);
lean_closure_set(v___f_1867_, 5, v___x_1855_);
lean_closure_set(v___f_1867_, 6, v___y_1823_);
lean_closure_set(v___f_1867_, 7, v_b_1822_);
lean_closure_set(v___f_1867_, 8, v_a_1821_);
v___y_1830_ = v___f_1867_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1868_; lean_object* v___f_1869_; 
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_b_1822_);
v___f_1869_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1869_, 0, v___x_1868_);
v___y_1830_ = v___f_1869_;
goto v___jp_1829_;
}
}
}
v___jp_1829_:
{
lean_object* v___x_1831_; 
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
lean_inc(v___y_1825_);
lean_inc_ref(v___y_1824_);
v___x_1831_ = lean_apply_5(v___y_1830_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, lean_box(0));
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1844_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
if (lean_obj_tag(v_a_1832_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; 
lean_dec(v_a_1821_);
lean_dec_ref(v_post_1817_);
lean_dec_ref(v_pre_1816_);
v_a_1836_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v_a_1832_, 1);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v_a_1836_);
v___x_1838_ = v___x_1834_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1834_);
v_a_1840_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v_a_1832_, 1);
v___x_1841_ = lean_unsigned_to_nat(1u);
v___x_1842_ = lean_nat_add(v_a_1821_, v___x_1841_);
lean_dec(v_a_1821_);
v_a_1821_ = v___x_1842_;
v_b_1822_ = v_a_1840_;
goto _start;
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v_a_1821_);
lean_dec_ref(v_post_1817_);
lean_dec_ref(v_pre_1816_);
v_a_1845_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1831_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1831_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1870_, lean_object* v_pre_1871_, lean_object* v_post_1872_, uint8_t v_usedLetOnly_1873_, uint8_t v_skipConstInApp_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_f_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; 
if (lean_obj_tag(v_x_1875_) == 5)
{
lean_object* v_fn_1933_; lean_object* v_arg_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_fn_1933_ = lean_ctor_get(v_x_1875_, 0);
lean_inc_ref(v_fn_1933_);
v_arg_1934_ = lean_ctor_get(v_x_1875_, 1);
lean_inc_ref(v_arg_1934_);
lean_dec_ref_known(v_x_1875_, 2);
v___x_1935_ = lean_array_set(v_x_1876_, v_x_1877_, v_arg_1934_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = lean_nat_sub(v_x_1877_, v___x_1936_);
lean_dec(v_x_1877_);
v_x_1875_ = v_fn_1933_;
v_x_1876_ = v___x_1935_;
v_x_1877_ = v___x_1937_;
goto _start;
}
else
{
lean_dec(v_x_1877_);
if (v_skipConstInApp_1874_ == 0)
{
goto v___jp_1930_;
}
else
{
uint8_t v___x_1939_; 
v___x_1939_ = l_Lean_Expr_isConst(v_x_1875_);
if (v___x_1939_ == 0)
{
goto v___jp_1930_;
}
else
{
v_f_1885_ = v_x_1875_;
v___y_1886_ = v___y_1878_;
v___y_1887_ = v___y_1879_;
v___y_1888_ = v___y_1880_;
v___y_1889_ = v___y_1881_;
v___y_1890_ = v___y_1882_;
goto v___jp_1884_;
}
}
}
v___jp_1884_:
{
if (v_skipInstances_1870_ == 0)
{
size_t v_sz_1891_; size_t v___x_1892_; lean_object* v___x_1893_; 
v_sz_1891_ = lean_array_size(v_x_1876_);
v___x_1892_ = ((size_t)0ULL);
lean_inc_ref(v_post_1872_);
lean_inc_ref(v_pre_1871_);
v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1871_, v_post_1872_, v_usedLetOnly_1873_, v_skipConstInApp_1874_, v_skipInstances_1870_, v_sz_1891_, v___x_1892_, v_x_1876_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = l_Lean_mkAppN(v_f_1885_, v_a_1894_);
lean_dec(v_a_1894_);
v___x_1896_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1871_, v_post_1872_, v_usedLetOnly_1873_, v_skipConstInApp_1874_, v_skipInstances_1870_, v___x_1895_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1896_;
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v_f_1885_);
lean_dec_ref(v_post_1872_);
lean_dec_ref(v_pre_1871_);
v_a_1897_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1893_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1893_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_array_get_size(v_x_1876_);
lean_inc_ref(v_f_1885_);
v___x_1906_ = l_Lean_Meta_getFunInfoNArgs(v_f_1885_, v___x_1905_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v_paramInfo_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v_paramInfo_1908_ = lean_ctor_get(v_a_1907_, 0);
lean_inc_ref(v_paramInfo_1908_);
lean_dec(v_a_1907_);
v___x_1909_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1872_);
lean_inc_ref(v_pre_1871_);
v___x_1910_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1905_, v_paramInfo_1908_, v_pre_1871_, v_post_1872_, v_usedLetOnly_1873_, v_skipConstInApp_1874_, v_skipInstances_1870_, v___x_1909_, v_x_1876_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec_ref(v_paramInfo_1908_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = l_Lean_mkAppN(v_f_1885_, v_a_1911_);
lean_dec(v_a_1911_);
v___x_1913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1871_, v_post_1872_, v_usedLetOnly_1873_, v_skipConstInApp_1874_, v_skipInstances_1870_, v___x_1912_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
return v___x_1913_;
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v_f_1885_);
lean_dec_ref(v_post_1872_);
lean_dec_ref(v_pre_1871_);
v_a_1914_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1910_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1910_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v_f_1885_);
lean_dec_ref(v_x_1876_);
lean_dec_ref(v_post_1872_);
lean_dec_ref(v_pre_1871_);
v_a_1922_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1906_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1906_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
v___jp_1930_:
{
lean_object* v___x_1931_; 
lean_inc_ref(v_post_1872_);
lean_inc_ref(v_pre_1871_);
v___x_1931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1871_, v_post_1872_, v_usedLetOnly_1873_, v_skipConstInApp_1874_, v_skipInstances_1870_, v_x_1875_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v_f_1885_ = v_a_1932_;
v___y_1886_ = v___y_1878_;
v___y_1887_ = v___y_1879_;
v___y_1888_ = v___y_1880_;
v___y_1889_ = v___y_1881_;
v___y_1890_ = v___y_1882_;
goto v___jp_1884_;
}
else
{
lean_dec_ref(v_x_1876_);
lean_dec_ref(v_post_1872_);
lean_dec_ref(v_pre_1871_);
return v___x_1931_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1940_, lean_object* v_pre_1941_, lean_object* v_e_1942_, lean_object* v_post_1943_, uint8_t v_usedLetOnly_1944_, uint8_t v_skipConstInApp_1945_, uint8_t v_skipInstances_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_Core_checkSystem(v___x_1940_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v___x_1954_; 
lean_dec_ref_known(v___x_1953_, 1);
lean_inc_ref(v_pre_1941_);
lean_inc(v___y_1951_);
lean_inc_ref(v___y_1950_);
lean_inc(v___y_1949_);
lean_inc_ref(v___y_1948_);
lean_inc_ref(v_e_1942_);
v___x_1954_ = lean_apply_6(v_pre_1941_, v_e_1942_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, lean_box(0));
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2003_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_2003_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2003_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___y_1960_; 
switch(lean_obj_tag(v_a_1955_))
{
case 0:
{
lean_object* v_e_1995_; lean_object* v___x_1997_; 
lean_dec_ref(v_post_1943_);
lean_dec_ref(v_e_1942_);
lean_dec_ref(v_pre_1941_);
v_e_1995_ = lean_ctor_get(v_a_1955_, 0);
lean_inc_ref(v_e_1995_);
lean_dec_ref_known(v_a_1955_, 1);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v_e_1995_);
v___x_1997_ = v___x_1957_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_e_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
case 1:
{
lean_object* v_e_1999_; lean_object* v___x_2000_; 
lean_del_object(v___x_1957_);
lean_dec_ref(v_e_1942_);
v_e_1999_ = lean_ctor_get(v_a_1955_, 0);
lean_inc_ref(v_e_1999_);
lean_dec_ref_known(v_a_1955_, 1);
v___x_2000_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v_e_1999_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_2000_;
}
default: 
{
lean_object* v_e_x3f_2001_; 
lean_del_object(v___x_1957_);
v_e_x3f_2001_ = lean_ctor_get(v_a_1955_, 0);
lean_inc(v_e_x3f_2001_);
lean_dec_ref_known(v_a_1955_, 1);
if (lean_obj_tag(v_e_x3f_2001_) == 0)
{
v___y_1960_ = v_e_1942_;
goto v___jp_1959_;
}
else
{
lean_object* v_val_2002_; 
lean_dec_ref(v_e_1942_);
v_val_2002_ = lean_ctor_get(v_e_x3f_2001_, 0);
lean_inc(v_val_2002_);
lean_dec_ref_known(v_e_x3f_2001_, 1);
v___y_1960_ = v_val_2002_;
goto v___jp_1959_;
}
}
}
v___jp_1959_:
{
switch(lean_obj_tag(v___y_1960_))
{
case 7:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v___x_1961_, v___y_1960_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1962_;
}
case 6:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1964_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v___x_1963_, v___y_1960_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1964_;
}
case 8:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v___x_1965_, v___y_1960_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1966_;
}
case 5:
{
lean_object* v_dummy_1967_; lean_object* v_nargs_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_dummy_1967_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1968_ = l_Lean_Expr_getAppNumArgs(v___y_1960_);
lean_inc(v_nargs_1968_);
v___x_1969_ = lean_mk_array(v_nargs_1968_, v_dummy_1967_);
v___x_1970_ = lean_unsigned_to_nat(1u);
v___x_1971_ = lean_nat_sub(v_nargs_1968_, v___x_1970_);
lean_dec(v_nargs_1968_);
v___x_1972_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1946_, v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v___y_1960_, v___x_1969_, v___x_1971_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1972_;
}
case 10:
{
lean_object* v_data_1973_; lean_object* v_expr_1974_; lean_object* v___x_1975_; 
v_data_1973_ = lean_ctor_get(v___y_1960_, 0);
v_expr_1974_ = lean_ctor_get(v___y_1960_, 1);
lean_inc_ref(v_expr_1974_);
lean_inc_ref(v_post_1943_);
lean_inc_ref(v_pre_1941_);
v___x_1975_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v_expr_1974_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; size_t v___x_1977_; size_t v___x_1978_; uint8_t v___x_1979_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1975_, 1);
v___x_1977_ = lean_ptr_addr(v_expr_1974_);
v___x_1978_ = lean_ptr_addr(v_a_1976_);
v___x_1979_ = lean_usize_dec_eq(v___x_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_inc(v_data_1973_);
lean_dec_ref_known(v___y_1960_, 2);
v___x_1980_ = l_Lean_Expr_mdata___override(v_data_1973_, v_a_1976_);
v___x_1981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v___x_1980_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; 
lean_dec(v_a_1976_);
v___x_1982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v___y_1960_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1982_;
}
}
else
{
lean_dec_ref_known(v___y_1960_, 2);
lean_dec_ref(v_post_1943_);
lean_dec_ref(v_pre_1941_);
return v___x_1975_;
}
}
case 11:
{
lean_object* v_typeName_1983_; lean_object* v_idx_1984_; lean_object* v_struct_1985_; lean_object* v___x_1986_; 
v_typeName_1983_ = lean_ctor_get(v___y_1960_, 0);
v_idx_1984_ = lean_ctor_get(v___y_1960_, 1);
v_struct_1985_ = lean_ctor_get(v___y_1960_, 2);
lean_inc_ref(v_struct_1985_);
lean_inc_ref(v_post_1943_);
lean_inc_ref(v_pre_1941_);
v___x_1986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v_struct_1985_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; size_t v___x_1988_; size_t v___x_1989_; uint8_t v___x_1990_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = lean_ptr_addr(v_struct_1985_);
v___x_1989_ = lean_ptr_addr(v_a_1987_);
v___x_1990_ = lean_usize_dec_eq(v___x_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_inc(v_idx_1984_);
lean_inc(v_typeName_1983_);
lean_dec_ref_known(v___y_1960_, 3);
v___x_1991_ = l_Lean_Expr_proj___override(v_typeName_1983_, v_idx_1984_, v_a_1987_);
v___x_1992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v___x_1991_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; 
lean_dec(v_a_1987_);
v___x_1993_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v___y_1960_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1993_;
}
}
else
{
lean_dec_ref_known(v___y_1960_, 3);
lean_dec_ref(v_post_1943_);
lean_dec_ref(v_pre_1941_);
return v___x_1986_;
}
}
default: 
{
lean_object* v___x_1994_; 
v___x_1994_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1941_, v_post_1943_, v_usedLetOnly_1944_, v_skipConstInApp_1945_, v_skipInstances_1946_, v___y_1960_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1994_;
}
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_post_1943_);
lean_dec_ref(v_e_1942_);
lean_dec_ref(v_pre_1941_);
v_a_2004_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1954_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1954_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_post_1943_);
lean_dec_ref(v_e_1942_);
lean_dec_ref(v_pre_1941_);
v_a_2012_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1953_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1953_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2020_, lean_object* v_pre_2021_, lean_object* v_e_2022_, lean_object* v_post_2023_, lean_object* v_usedLetOnly_2024_, lean_object* v_skipConstInApp_2025_, lean_object* v_skipInstances_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
uint8_t v_usedLetOnly_boxed_2033_; uint8_t v_skipConstInApp_boxed_2034_; uint8_t v_skipInstances_boxed_2035_; lean_object* v_res_2036_; 
v_usedLetOnly_boxed_2033_ = lean_unbox(v_usedLetOnly_2024_);
v_skipConstInApp_boxed_2034_ = lean_unbox(v_skipConstInApp_2025_);
v_skipInstances_boxed_2035_ = lean_unbox(v_skipInstances_2026_);
v_res_2036_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2020_, v_pre_2021_, v_e_2022_, v_post_2023_, v_usedLetOnly_boxed_2033_, v_skipConstInApp_boxed_2034_, v_skipInstances_boxed_2035_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2037_, lean_object* v_post_2038_, uint8_t v_usedLetOnly_2039_, uint8_t v_skipConstInApp_2040_, uint8_t v_skipInstances_2041_, lean_object* v_e_2042_, lean_object* v_a_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_inc(v_a_2043_);
v___x_2049_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2049_, 0, lean_box(0));
lean_closure_set(v___x_2049_, 1, lean_box(0));
lean_closure_set(v___x_2049_, 2, v_a_2043_);
v___x_2050_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2049_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2085_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2085_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2085_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2051_, v_e_2042_);
lean_dec(v_a_2051_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; 
lean_del_object(v___x_2053_);
v___x_2056_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2057_ = lean_box(v_usedLetOnly_2039_);
v___x_2058_ = lean_box(v_skipConstInApp_2040_);
v___x_2059_ = lean_box(v_skipInstances_2041_);
lean_inc_ref(v_e_2042_);
v___f_2060_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2060_, 0, v___x_2056_);
lean_closure_set(v___f_2060_, 1, v_pre_2037_);
lean_closure_set(v___f_2060_, 2, v_e_2042_);
lean_closure_set(v___f_2060_, 3, v_post_2038_);
lean_closure_set(v___f_2060_, 4, v___x_2057_);
lean_closure_set(v___f_2060_, 5, v___x_2058_);
lean_closure_set(v___f_2060_, 6, v___x_2059_);
v___x_2061_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2060_, v_a_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___f_2063_; lean_object* v___x_2064_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_n(v_a_2062_, 2);
lean_dec_ref_known(v___x_2061_, 1);
lean_inc(v_a_2043_);
v___f_2063_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2063_, 0, v_a_2043_);
lean_closure_set(v___f_2063_, 1, v_e_2042_);
lean_closure_set(v___f_2063_, 2, v_a_2062_);
v___x_2064_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2063_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v___x_2064_, 0);
lean_dec(v_unused_2072_);
v___x_2066_ = v___x_2064_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v___x_2064_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v_a_2062_);
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2062_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_a_2062_);
v_a_2073_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2064_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2064_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_dec_ref(v_e_2042_);
return v___x_2061_;
}
}
else
{
lean_object* v_val_2081_; lean_object* v___x_2083_; 
lean_dec_ref(v_e_2042_);
lean_dec_ref(v_post_2038_);
lean_dec_ref(v_pre_2037_);
v_val_2081_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_val_2081_);
lean_dec_ref_known(v___x_2055_, 1);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v_val_2081_);
v___x_2083_ = v___x_2053_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_val_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v_e_2042_);
lean_dec_ref(v_post_2038_);
lean_dec_ref(v_pre_2037_);
v_a_2086_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2050_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2050_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2094_, lean_object* v_pre_2095_, lean_object* v_post_2096_, lean_object* v_usedLetOnly_2097_, lean_object* v_skipConstInApp_2098_, lean_object* v_skipInstances_2099_, lean_object* v_body_2100_, lean_object* v_x_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v_usedLetOnly_boxed_2108_; uint8_t v_skipConstInApp_boxed_2109_; uint8_t v_skipInstances_boxed_2110_; lean_object* v_res_2111_; 
v_usedLetOnly_boxed_2108_ = lean_unbox(v_usedLetOnly_2097_);
v_skipConstInApp_boxed_2109_ = lean_unbox(v_skipConstInApp_2098_);
v_skipInstances_boxed_2110_ = lean_unbox(v_skipInstances_2099_);
v_res_2111_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2094_, v_pre_2095_, v_post_2096_, v_usedLetOnly_boxed_2108_, v_skipConstInApp_boxed_2109_, v_skipInstances_boxed_2110_, v_body_2100_, v_x_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2112_, lean_object* v_post_2113_, uint8_t v_usedLetOnly_2114_, uint8_t v_skipConstInApp_2115_, uint8_t v_skipInstances_2116_, lean_object* v_fvars_2117_, lean_object* v_e_2118_, lean_object* v_a_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
if (lean_obj_tag(v_e_2118_) == 7)
{
lean_object* v_binderName_2125_; lean_object* v_binderType_2126_; lean_object* v_body_2127_; uint8_t v_binderInfo_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_binderName_2125_ = lean_ctor_get(v_e_2118_, 0);
lean_inc(v_binderName_2125_);
v_binderType_2126_ = lean_ctor_get(v_e_2118_, 1);
lean_inc_ref(v_binderType_2126_);
v_body_2127_ = lean_ctor_get(v_e_2118_, 2);
lean_inc_ref(v_body_2127_);
v_binderInfo_2128_ = lean_ctor_get_uint8(v_e_2118_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2118_, 3);
v___x_2129_ = lean_expr_instantiate_rev(v_binderType_2126_, v_fvars_2117_);
lean_dec_ref(v_binderType_2126_);
lean_inc_ref(v_post_2113_);
lean_inc_ref(v_pre_2112_);
v___x_2130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2112_, v_post_2113_, v_usedLetOnly_2114_, v_skipConstInApp_2115_, v_skipInstances_2116_, v___x_2129_, v_a_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_box(v_usedLetOnly_2114_);
v___x_2133_ = lean_box(v_skipConstInApp_2115_);
v___x_2134_ = lean_box(v_skipInstances_2116_);
v___f_2135_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2135_, 0, v_fvars_2117_);
lean_closure_set(v___f_2135_, 1, v_pre_2112_);
lean_closure_set(v___f_2135_, 2, v_post_2113_);
lean_closure_set(v___f_2135_, 3, v___x_2132_);
lean_closure_set(v___f_2135_, 4, v___x_2133_);
lean_closure_set(v___f_2135_, 5, v___x_2134_);
lean_closure_set(v___f_2135_, 6, v_body_2127_);
v___x_2136_ = 0;
v___x_2137_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2125_, v_binderInfo_2128_, v_a_2131_, v___f_2135_, v___x_2136_, v_a_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2137_;
}
else
{
lean_dec_ref(v_body_2127_);
lean_dec(v_binderName_2125_);
lean_dec_ref(v_fvars_2117_);
lean_dec_ref(v_post_2113_);
lean_dec_ref(v_pre_2112_);
return v___x_2130_;
}
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_expr_instantiate_rev(v_e_2118_, v_fvars_2117_);
lean_dec_ref(v_e_2118_);
lean_inc_ref(v_post_2113_);
lean_inc_ref(v_pre_2112_);
v___x_2139_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2112_, v_post_2113_, v_usedLetOnly_2114_, v_skipConstInApp_2115_, v_skipInstances_2116_, v___x_2138_, v_a_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; uint8_t v___x_2141_; uint8_t v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = 0;
v___x_2142_ = 1;
v___x_2143_ = 1;
v___x_2144_ = l_Lean_Meta_mkForallFVars(v_fvars_2117_, v_a_2140_, v___x_2141_, v_usedLetOnly_2114_, v___x_2142_, v___x_2143_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec_ref(v_fvars_2117_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2112_, v_post_2113_, v_usedLetOnly_2114_, v_skipConstInApp_2115_, v_skipInstances_2116_, v_a_2145_, v_a_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2146_;
}
else
{
lean_dec_ref(v_post_2113_);
lean_dec_ref(v_pre_2112_);
return v___x_2144_;
}
}
else
{
lean_dec_ref(v_fvars_2117_);
lean_dec_ref(v_post_2113_);
lean_dec_ref(v_pre_2112_);
return v___x_2139_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2147_, lean_object* v_pre_2148_, lean_object* v_post_2149_, uint8_t v_usedLetOnly_2150_, uint8_t v_skipConstInApp_2151_, uint8_t v_skipInstances_2152_, lean_object* v_body_2153_, lean_object* v_x_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_array_push(v_fvars_2147_, v_x_2154_);
v___x_2162_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2148_, v_post_2149_, v_usedLetOnly_2150_, v_skipConstInApp_2151_, v_skipInstances_2152_, v___x_2161_, v_body_2153_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2163_, lean_object* v_post_2164_, lean_object* v_usedLetOnly_2165_, lean_object* v_skipConstInApp_2166_, lean_object* v_skipInstances_2167_, lean_object* v_e_2168_, lean_object* v_a_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
uint8_t v_usedLetOnly_boxed_2175_; uint8_t v_skipConstInApp_boxed_2176_; uint8_t v_skipInstances_boxed_2177_; lean_object* v_res_2178_; 
v_usedLetOnly_boxed_2175_ = lean_unbox(v_usedLetOnly_2165_);
v_skipConstInApp_boxed_2176_ = lean_unbox(v_skipConstInApp_2166_);
v_skipInstances_boxed_2177_ = lean_unbox(v_skipInstances_2167_);
v_res_2178_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2163_, v_post_2164_, v_usedLetOnly_boxed_2175_, v_skipConstInApp_boxed_2176_, v_skipInstances_boxed_2177_, v_e_2168_, v_a_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v_a_2169_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2179_, lean_object* v_post_2180_, lean_object* v_usedLetOnly_2181_, lean_object* v_skipConstInApp_2182_, lean_object* v_skipInstances_2183_, lean_object* v_sz_2184_, lean_object* v_i_2185_, lean_object* v_bs_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
uint8_t v_usedLetOnly_boxed_2193_; uint8_t v_skipConstInApp_boxed_2194_; uint8_t v_skipInstances_boxed_2195_; size_t v_sz_boxed_2196_; size_t v_i_boxed_2197_; lean_object* v_res_2198_; 
v_usedLetOnly_boxed_2193_ = lean_unbox(v_usedLetOnly_2181_);
v_skipConstInApp_boxed_2194_ = lean_unbox(v_skipConstInApp_2182_);
v_skipInstances_boxed_2195_ = lean_unbox(v_skipInstances_2183_);
v_sz_boxed_2196_ = lean_unbox_usize(v_sz_2184_);
lean_dec(v_sz_2184_);
v_i_boxed_2197_ = lean_unbox_usize(v_i_2185_);
lean_dec(v_i_2185_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2179_, v_post_2180_, v_usedLetOnly_boxed_2193_, v_skipConstInApp_boxed_2194_, v_skipInstances_boxed_2195_, v_sz_boxed_2196_, v_i_boxed_2197_, v_bs_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2199_, lean_object* v_post_2200_, lean_object* v_usedLetOnly_2201_, lean_object* v_skipConstInApp_2202_, lean_object* v_skipInstances_2203_, lean_object* v_e_2204_, lean_object* v_a_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v_usedLetOnly_boxed_2211_; uint8_t v_skipConstInApp_boxed_2212_; uint8_t v_skipInstances_boxed_2213_; lean_object* v_res_2214_; 
v_usedLetOnly_boxed_2211_ = lean_unbox(v_usedLetOnly_2201_);
v_skipConstInApp_boxed_2212_ = lean_unbox(v_skipConstInApp_2202_);
v_skipInstances_boxed_2213_ = lean_unbox(v_skipInstances_2203_);
v_res_2214_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2199_, v_post_2200_, v_usedLetOnly_boxed_2211_, v_skipConstInApp_boxed_2212_, v_skipInstances_boxed_2213_, v_e_2204_, v_a_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v_a_2205_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2215_, lean_object* v_post_2216_, lean_object* v_usedLetOnly_2217_, lean_object* v_skipConstInApp_2218_, lean_object* v_skipInstances_2219_, lean_object* v_fvars_2220_, lean_object* v_e_2221_, lean_object* v_a_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v_usedLetOnly_boxed_2228_; uint8_t v_skipConstInApp_boxed_2229_; uint8_t v_skipInstances_boxed_2230_; lean_object* v_res_2231_; 
v_usedLetOnly_boxed_2228_ = lean_unbox(v_usedLetOnly_2217_);
v_skipConstInApp_boxed_2229_ = lean_unbox(v_skipConstInApp_2218_);
v_skipInstances_boxed_2230_ = lean_unbox(v_skipInstances_2219_);
v_res_2231_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2215_, v_post_2216_, v_usedLetOnly_boxed_2228_, v_skipConstInApp_boxed_2229_, v_skipInstances_boxed_2230_, v_fvars_2220_, v_e_2221_, v_a_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v_a_2222_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2232_, lean_object* v_post_2233_, lean_object* v_usedLetOnly_2234_, lean_object* v_skipConstInApp_2235_, lean_object* v_skipInstances_2236_, lean_object* v_fvars_2237_, lean_object* v_e_2238_, lean_object* v_a_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
uint8_t v_usedLetOnly_boxed_2245_; uint8_t v_skipConstInApp_boxed_2246_; uint8_t v_skipInstances_boxed_2247_; lean_object* v_res_2248_; 
v_usedLetOnly_boxed_2245_ = lean_unbox(v_usedLetOnly_2234_);
v_skipConstInApp_boxed_2246_ = lean_unbox(v_skipConstInApp_2235_);
v_skipInstances_boxed_2247_ = lean_unbox(v_skipInstances_2236_);
v_res_2248_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2232_, v_post_2233_, v_usedLetOnly_boxed_2245_, v_skipConstInApp_boxed_2246_, v_skipInstances_boxed_2247_, v_fvars_2237_, v_e_2238_, v_a_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v_a_2239_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2249_, lean_object* v_post_2250_, lean_object* v_usedLetOnly_2251_, lean_object* v_skipConstInApp_2252_, lean_object* v_skipInstances_2253_, lean_object* v_fvars_2254_, lean_object* v_e_2255_, lean_object* v_a_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
uint8_t v_usedLetOnly_boxed_2262_; uint8_t v_skipConstInApp_boxed_2263_; uint8_t v_skipInstances_boxed_2264_; lean_object* v_res_2265_; 
v_usedLetOnly_boxed_2262_ = lean_unbox(v_usedLetOnly_2251_);
v_skipConstInApp_boxed_2263_ = lean_unbox(v_skipConstInApp_2252_);
v_skipInstances_boxed_2264_ = lean_unbox(v_skipInstances_2253_);
v_res_2265_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2249_, v_post_2250_, v_usedLetOnly_boxed_2262_, v_skipConstInApp_boxed_2263_, v_skipInstances_boxed_2264_, v_fvars_2254_, v_e_2255_, v_a_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v_a_2256_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2266_, lean_object* v___x_2267_, lean_object* v_pre_2268_, lean_object* v_post_2269_, lean_object* v_usedLetOnly_2270_, lean_object* v_skipConstInApp_2271_, lean_object* v_skipInstances_2272_, lean_object* v_a_2273_, lean_object* v_b_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
uint8_t v_usedLetOnly_boxed_2281_; uint8_t v_skipConstInApp_boxed_2282_; uint8_t v_skipInstances_boxed_2283_; lean_object* v_res_2284_; 
v_usedLetOnly_boxed_2281_ = lean_unbox(v_usedLetOnly_2270_);
v_skipConstInApp_boxed_2282_ = lean_unbox(v_skipConstInApp_2271_);
v_skipInstances_boxed_2283_ = lean_unbox(v_skipInstances_2272_);
v_res_2284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2266_, v___x_2267_, v_pre_2268_, v_post_2269_, v_usedLetOnly_boxed_2281_, v_skipConstInApp_boxed_2282_, v_skipInstances_boxed_2283_, v_a_2273_, v_b_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___x_2267_);
lean_dec(v_upperBound_2266_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2285_, lean_object* v_pre_2286_, lean_object* v_post_2287_, lean_object* v_usedLetOnly_2288_, lean_object* v_skipConstInApp_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_skipInstances_boxed_2299_; uint8_t v_usedLetOnly_boxed_2300_; uint8_t v_skipConstInApp_boxed_2301_; lean_object* v_res_2302_; 
v_skipInstances_boxed_2299_ = lean_unbox(v_skipInstances_2285_);
v_usedLetOnly_boxed_2300_ = lean_unbox(v_usedLetOnly_2288_);
v_skipConstInApp_boxed_2301_ = lean_unbox(v_skipConstInApp_2289_);
v_res_2302_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2299_, v_pre_2286_, v_post_2287_, v_usedLetOnly_boxed_2300_, v_skipConstInApp_boxed_2301_, v_x_2290_, v_x_2291_, v_x_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
return v_res_2302_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2304_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2304_, 0, lean_box(0));
lean_closure_set(v___x_2304_, 1, lean_box(0));
lean_closure_set(v___x_2304_, 2, v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2305_, lean_object* v_pre_2306_, lean_object* v_post_2307_, uint8_t v_usedLetOnly_2308_, uint8_t v_skipConstInApp_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v_a_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; 
v___x_2315_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2316_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2315_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref(v___x_2316_);
v___x_2318_ = 0;
v___x_2319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v___x_2318_, v_input_2305_, v_a_2317_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2321_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2321_, 0, lean_box(0));
lean_closure_set(v___x_2321_, 1, lean_box(0));
lean_closure_set(v___x_2321_, 2, v_a_2317_);
v___x_2322_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2321_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2322_, 0);
lean_dec(v_unused_2330_);
v___x_2324_ = v___x_2322_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_dec(v___x_2322_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v_a_2320_);
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2320_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_dec(v_a_2317_);
return v___x_2319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2331_, lean_object* v_pre_2332_, lean_object* v_post_2333_, lean_object* v_usedLetOnly_2334_, lean_object* v_skipConstInApp_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
uint8_t v_usedLetOnly_boxed_2341_; uint8_t v_skipConstInApp_boxed_2342_; lean_object* v_res_2343_; 
v_usedLetOnly_boxed_2341_ = lean_unbox(v_usedLetOnly_2334_);
v_skipConstInApp_boxed_2342_ = lean_unbox(v_skipConstInApp_2335_);
v_res_2343_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2331_, v_pre_2332_, v_post_2333_, v_usedLetOnly_boxed_2341_, v_skipConstInApp_boxed_2342_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2344_, lean_object* v_as_2345_, lean_object* v_j_2346_){
_start:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = lean_array_get_size(v_as_2345_);
v___x_2348_ = lean_nat_dec_lt(v_j_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
lean_dec(v_j_2346_);
v___x_2349_ = lean_box(0);
return v___x_2349_;
}
else
{
lean_object* v___x_2350_; lean_object* v_declName_2351_; uint8_t v___x_2352_; 
v___x_2350_ = lean_array_fget_borrowed(v_as_2345_, v_j_2346_);
v_declName_2351_ = lean_ctor_get(v___x_2350_, 3);
v___x_2352_ = lean_name_eq(v_declName_2351_, v___x_2344_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_nat_add(v_j_2346_, v___x_2353_);
lean_dec(v_j_2346_);
v_j_2346_ = v___x_2354_;
goto _start;
}
else
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_j_2346_);
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2357_, lean_object* v_as_2358_, lean_object* v_j_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2357_, v_as_2358_, v_j_2359_);
lean_dec_ref(v_as_2358_);
lean_dec(v___x_2357_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = lean_st_ref_get(v_val_2361_);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v_val_2369_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2376_, lean_object* v_val_2377_, lean_object* v_a_2378_, lean_object* v___x_2379_, lean_object* v_____r_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2386_ = lean_st_ref_take(v_val_2376_);
v___x_2387_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2377_, v_a_2378_, v___x_2386_);
v___x_2388_ = lean_st_ref_set(v_val_2376_, v___x_2387_);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2379_);
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2391_, lean_object* v_val_2392_, lean_object* v_a_2393_, lean_object* v___x_2394_, lean_object* v_____r_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2391_, v_val_2392_, v_a_2393_, v___x_2394_, v_____r_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v_val_2392_);
lean_dec(v_val_2391_);
return v_res_2401_;
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0(void){
_start:
{
uint8_t v___x_2402_; uint64_t v___x_2403_; 
v___x_2402_ = 2;
v___x_2403_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_upperBound_2404_, lean_object* v_val_2405_, lean_object* v_next_2406_, lean_object* v_params_2407_, lean_object* v___x_2408_, lean_object* v_val_2409_, lean_object* v_next_2410_, uint8_t v___x_2411_, lean_object* v_a_2412_, uint8_t v_b_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
uint8_t v_a_2420_; uint8_t v___x_2424_; 
v___x_2424_ = lean_nat_dec_lt(v_a_2412_, v_upperBound_2404_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec(v_a_2412_);
lean_dec(v_next_2410_);
lean_dec_ref(v___x_2408_);
v___x_2425_ = lean_box(v_b_2413_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = lean_st_ref_get(v_val_2405_);
v___x_2428_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2406_, v_a_2412_, v___x_2427_);
lean_dec(v___x_2427_);
if (v___x_2428_ == 0)
{
v_a_2420_ = v_b_2413_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2429_; uint8_t v_foApprox_2430_; uint8_t v_ctxApprox_2431_; uint8_t v_quasiPatternApprox_2432_; uint8_t v_constApprox_2433_; uint8_t v_isDefEqStuckEx_2434_; uint8_t v_unificationHints_2435_; uint8_t v_assignSyntheticOpaque_2436_; uint8_t v_offsetCnstrs_2437_; uint8_t v_transparency_2438_; uint8_t v_etaStruct_2439_; uint8_t v_univApprox_2440_; uint8_t v_iota_2441_; uint8_t v_beta_2442_; uint8_t v_proj_2443_; uint8_t v_zeta_2444_; uint8_t v_zetaDelta_2445_; uint8_t v_zetaUnused_2446_; uint8_t v_zetaHave_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2510_; 
v___x_2429_ = l_Lean_Meta_Context_config(v___y_2414_);
v_foApprox_2430_ = lean_ctor_get_uint8(v___x_2429_, 0);
v_ctxApprox_2431_ = lean_ctor_get_uint8(v___x_2429_, 1);
v_quasiPatternApprox_2432_ = lean_ctor_get_uint8(v___x_2429_, 2);
v_constApprox_2433_ = lean_ctor_get_uint8(v___x_2429_, 3);
v_isDefEqStuckEx_2434_ = lean_ctor_get_uint8(v___x_2429_, 4);
v_unificationHints_2435_ = lean_ctor_get_uint8(v___x_2429_, 5);
v_assignSyntheticOpaque_2436_ = lean_ctor_get_uint8(v___x_2429_, 7);
v_offsetCnstrs_2437_ = lean_ctor_get_uint8(v___x_2429_, 8);
v_transparency_2438_ = lean_ctor_get_uint8(v___x_2429_, 9);
v_etaStruct_2439_ = lean_ctor_get_uint8(v___x_2429_, 10);
v_univApprox_2440_ = lean_ctor_get_uint8(v___x_2429_, 11);
v_iota_2441_ = lean_ctor_get_uint8(v___x_2429_, 12);
v_beta_2442_ = lean_ctor_get_uint8(v___x_2429_, 13);
v_proj_2443_ = lean_ctor_get_uint8(v___x_2429_, 14);
v_zeta_2444_ = lean_ctor_get_uint8(v___x_2429_, 15);
v_zetaDelta_2445_ = lean_ctor_get_uint8(v___x_2429_, 16);
v_zetaUnused_2446_ = lean_ctor_get_uint8(v___x_2429_, 17);
v_zetaHave_2447_ = lean_ctor_get_uint8(v___x_2429_, 18);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2449_ = v___x_2429_;
v_isShared_2450_ = v_isSharedCheck_2510_;
goto v_resetjp_2448_;
}
else
{
lean_dec(v___x_2429_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2510_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v_trackZetaDelta_2451_; lean_object* v_zetaDeltaSet_2452_; lean_object* v_lctx_2453_; lean_object* v_localInstances_2454_; lean_object* v_defEqCtx_x3f_2455_; lean_object* v_synthPendingDepth_2456_; lean_object* v_canUnfold_x3f_2457_; uint8_t v_univApprox_2458_; uint8_t v_inTypeClassResolution_2459_; uint8_t v_cacheInferType_2460_; uint8_t v___x_2461_; lean_object* v___x_2463_; 
v_trackZetaDelta_2451_ = lean_ctor_get_uint8(v___y_2414_, sizeof(void*)*7);
v_zetaDeltaSet_2452_ = lean_ctor_get(v___y_2414_, 1);
v_lctx_2453_ = lean_ctor_get(v___y_2414_, 2);
v_localInstances_2454_ = lean_ctor_get(v___y_2414_, 3);
v_defEqCtx_x3f_2455_ = lean_ctor_get(v___y_2414_, 4);
v_synthPendingDepth_2456_ = lean_ctor_get(v___y_2414_, 5);
v_canUnfold_x3f_2457_ = lean_ctor_get(v___y_2414_, 6);
v_univApprox_2458_ = lean_ctor_get_uint8(v___y_2414_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2459_ = lean_ctor_get_uint8(v___y_2414_, sizeof(void*)*7 + 2);
v_cacheInferType_2460_ = lean_ctor_get_uint8(v___y_2414_, sizeof(void*)*7 + 3);
v___x_2461_ = 0;
if (v_isShared_2450_ == 0)
{
v___x_2463_ = v___x_2449_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 0, v_foApprox_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 1, v_ctxApprox_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 2, v_quasiPatternApprox_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 3, v_constApprox_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 4, v_isDefEqStuckEx_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 5, v_unificationHints_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 7, v_assignSyntheticOpaque_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 8, v_offsetCnstrs_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 9, v_transparency_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 10, v_etaStruct_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 11, v_univApprox_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 12, v_iota_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 13, v_beta_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 14, v_proj_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 15, v_zeta_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 16, v_zetaDelta_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 17, v_zetaUnused_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, 18, v_zetaHave_2447_);
v___x_2463_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
uint64_t v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v_foApprox_2468_; uint8_t v_ctxApprox_2469_; uint8_t v_quasiPatternApprox_2470_; uint8_t v_constApprox_2471_; uint8_t v_isDefEqStuckEx_2472_; uint8_t v_unificationHints_2473_; uint8_t v_proofIrrelevance_2474_; uint8_t v_assignSyntheticOpaque_2475_; uint8_t v_offsetCnstrs_2476_; uint8_t v_etaStruct_2477_; uint8_t v_univApprox_2478_; uint8_t v_iota_2479_; uint8_t v_beta_2480_; uint8_t v_proj_2481_; uint8_t v_zeta_2482_; uint8_t v_zetaDelta_2483_; uint8_t v_zetaUnused_2484_; uint8_t v_zetaHave_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2508_; 
lean_ctor_set_uint8(v___x_2463_, 6, v___x_2461_);
v___x_2464_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2463_);
v___x_2465_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set_uint64(v___x_2465_, sizeof(void*)*1, v___x_2464_);
lean_inc(v_canUnfold_x3f_2457_);
lean_inc(v_synthPendingDepth_2456_);
lean_inc(v_defEqCtx_x3f_2455_);
lean_inc_ref(v_localInstances_2454_);
lean_inc_ref(v_lctx_2453_);
lean_inc(v_zetaDeltaSet_2452_);
v___x_2466_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v_zetaDeltaSet_2452_);
lean_ctor_set(v___x_2466_, 2, v_lctx_2453_);
lean_ctor_set(v___x_2466_, 3, v_localInstances_2454_);
lean_ctor_set(v___x_2466_, 4, v_defEqCtx_x3f_2455_);
lean_ctor_set(v___x_2466_, 5, v_synthPendingDepth_2456_);
lean_ctor_set(v___x_2466_, 6, v_canUnfold_x3f_2457_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*7, v_trackZetaDelta_2451_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*7 + 1, v_univApprox_2458_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2459_);
lean_ctor_set_uint8(v___x_2466_, sizeof(void*)*7 + 3, v_cacheInferType_2460_);
v___x_2467_ = l_Lean_Meta_Context_config(v___x_2466_);
v_foApprox_2468_ = lean_ctor_get_uint8(v___x_2467_, 0);
v_ctxApprox_2469_ = lean_ctor_get_uint8(v___x_2467_, 1);
v_quasiPatternApprox_2470_ = lean_ctor_get_uint8(v___x_2467_, 2);
v_constApprox_2471_ = lean_ctor_get_uint8(v___x_2467_, 3);
v_isDefEqStuckEx_2472_ = lean_ctor_get_uint8(v___x_2467_, 4);
v_unificationHints_2473_ = lean_ctor_get_uint8(v___x_2467_, 5);
v_proofIrrelevance_2474_ = lean_ctor_get_uint8(v___x_2467_, 6);
v_assignSyntheticOpaque_2475_ = lean_ctor_get_uint8(v___x_2467_, 7);
v_offsetCnstrs_2476_ = lean_ctor_get_uint8(v___x_2467_, 8);
v_etaStruct_2477_ = lean_ctor_get_uint8(v___x_2467_, 10);
v_univApprox_2478_ = lean_ctor_get_uint8(v___x_2467_, 11);
v_iota_2479_ = lean_ctor_get_uint8(v___x_2467_, 12);
v_beta_2480_ = lean_ctor_get_uint8(v___x_2467_, 13);
v_proj_2481_ = lean_ctor_get_uint8(v___x_2467_, 14);
v_zeta_2482_ = lean_ctor_get_uint8(v___x_2467_, 15);
v_zetaDelta_2483_ = lean_ctor_get_uint8(v___x_2467_, 16);
v_zetaUnused_2484_ = lean_ctor_get_uint8(v___x_2467_, 17);
v_zetaHave_2485_ = lean_ctor_get_uint8(v___x_2467_, 18);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2487_ = v___x_2467_;
v_isShared_2488_ = v_isSharedCheck_2508_;
goto v_resetjp_2486_;
}
else
{
lean_dec(v___x_2467_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2508_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v_config_2492_; 
v___x_2489_ = lean_array_fget_borrowed(v_params_2407_, v_a_2412_);
v___x_2490_ = 2;
if (v_isShared_2488_ == 0)
{
v_config_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 0, v_foApprox_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 1, v_ctxApprox_2469_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 2, v_quasiPatternApprox_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 3, v_constApprox_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 4, v_isDefEqStuckEx_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 5, v_unificationHints_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 6, v_proofIrrelevance_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 7, v_assignSyntheticOpaque_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 8, v_offsetCnstrs_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 10, v_etaStruct_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 11, v_univApprox_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 12, v_iota_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 13, v_beta_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 14, v_proj_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 15, v_zeta_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 16, v_zetaDelta_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 17, v_zetaUnused_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2507_, 18, v_zetaHave_2485_);
v_config_2492_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
uint64_t v___x_2493_; uint64_t v___x_2494_; uint64_t v___x_2495_; uint64_t v___x_2496_; uint64_t v___x_2497_; uint64_t v_key_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_ctor_set_uint8(v_config_2492_, 9, v___x_2490_);
v___x_2493_ = l_Lean_Meta_Context_configKey(v___x_2466_);
lean_dec_ref_known(v___x_2466_, 7);
v___x_2494_ = 3ULL;
v___x_2495_ = lean_uint64_shift_right(v___x_2493_, v___x_2494_);
v___x_2496_ = lean_uint64_shift_left(v___x_2495_, v___x_2494_);
v___x_2497_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2498_ = lean_uint64_lor(v___x_2496_, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2499_, 0, v_config_2492_);
lean_ctor_set_uint64(v___x_2499_, sizeof(void*)*1, v_key_2498_);
lean_inc(v_canUnfold_x3f_2457_);
lean_inc(v_synthPendingDepth_2456_);
lean_inc(v_defEqCtx_x3f_2455_);
lean_inc_ref(v_localInstances_2454_);
lean_inc_ref(v_lctx_2453_);
lean_inc(v_zetaDeltaSet_2452_);
v___x_2500_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v_zetaDeltaSet_2452_);
lean_ctor_set(v___x_2500_, 2, v_lctx_2453_);
lean_ctor_set(v___x_2500_, 3, v_localInstances_2454_);
lean_ctor_set(v___x_2500_, 4, v_defEqCtx_x3f_2455_);
lean_ctor_set(v___x_2500_, 5, v_synthPendingDepth_2456_);
lean_ctor_set(v___x_2500_, 6, v_canUnfold_x3f_2457_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*7, v_trackZetaDelta_2451_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*7 + 1, v_univApprox_2458_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2459_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*7 + 3, v_cacheInferType_2460_);
lean_inc_ref(v___x_2408_);
lean_inc(v___x_2489_);
v___x_2501_ = l_Lean_Meta_isExprDefEq(v___x_2489_, v___x_2408_, v___x_2500_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec_ref_known(v___x_2500_, 7);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; uint8_t v___x_2503_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2503_ = lean_unbox(v_a_2502_);
lean_dec(v_a_2502_);
if (v___x_2503_ == 0)
{
v_a_2420_ = v_b_2413_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = lean_st_ref_take(v_val_2405_);
lean_inc(v_a_2412_);
lean_inc(v_next_2410_);
v___x_2505_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2409_, v_next_2410_, v_next_2406_, v_a_2412_, v___x_2504_);
v___x_2506_ = lean_st_ref_set(v_val_2405_, v___x_2505_);
v_a_2420_ = v___x_2411_;
goto v___jp_2419_;
}
}
else
{
lean_dec(v_a_2412_);
lean_dec(v_next_2410_);
lean_dec_ref(v___x_2408_);
return v___x_2501_;
}
}
}
}
}
}
}
v___jp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_unsigned_to_nat(1u);
v___x_2422_ = lean_nat_add(v_a_2412_, v___x_2421_);
lean_dec(v_a_2412_);
v_a_2412_ = v___x_2422_;
v_b_2413_ = v_a_2420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_upperBound_2511_, lean_object* v_val_2512_, lean_object* v_next_2513_, lean_object* v_params_2514_, lean_object* v___x_2515_, lean_object* v_val_2516_, lean_object* v_next_2517_, lean_object* v___x_2518_, lean_object* v_a_2519_, lean_object* v_b_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v___x_44689__boxed_2526_; uint8_t v_b_boxed_2527_; lean_object* v_res_2528_; 
v___x_44689__boxed_2526_ = lean_unbox(v___x_2518_);
v_b_boxed_2527_ = lean_unbox(v_b_2520_);
v_res_2528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_2511_, v_val_2512_, v_next_2513_, v_params_2514_, v___x_2515_, v_val_2516_, v_next_2517_, v___x_44689__boxed_2526_, v_a_2519_, v_b_boxed_2527_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v_val_2516_);
lean_dec_ref(v_params_2514_);
lean_dec(v_next_2513_);
lean_dec(v_val_2512_);
lean_dec(v_upperBound_2511_);
return v_res_2528_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2540_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2541_ = l_Lean_Name_append(v___x_2540_, v___x_2539_);
return v___x_2541_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2544_ = l_Lean_stringToMessageData(v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2546_ = l_Lean_stringToMessageData(v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2558_ = l_Lean_stringToMessageData(v___x_2557_);
return v___x_2558_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
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
lean_dec_ref_known(v___x_2605_, 1);
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
lean_object* v_options_2611_; lean_object* v_inheritedTraceOptions_2612_; uint8_t v_hasTrace_2613_; 
v_options_2611_ = lean_ctor_get(v___y_2575_, 2);
v_inheritedTraceOptions_2612_ = lean_ctor_get(v___y_2575_, 13);
v_hasTrace_2613_ = lean_ctor_get_uint8(v_options_2611_, sizeof(void*)*1);
if (v_hasTrace_2613_ == 0)
{
goto v___jp_2614_;
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2616_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2617_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2618_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2612_, v_options_2611_, v___x_2617_);
if (v___x_2618_ == 0)
{
goto v___jp_2614_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2619_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2563_);
v___x_2620_ = l_Nat_reprFast(v_val_2563_);
v___x_2621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
v___x_2622_ = l_Lean_MessageData_ofFormat(v___x_2621_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2619_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
lean_inc(v_a_2571_);
v___x_2626_ = l_Nat_reprFast(v_a_2571_);
v___x_2627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
v___x_2628_ = l_Lean_MessageData_ofFormat(v___x_2627_);
lean_inc_ref(v___x_2628_);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2625_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
lean_inc_ref(v_e_2566_);
v___x_2632_ = l_Lean_MessageData_ofExpr(v_e_2566_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2635_);
lean_ctor_set(v___x_2636_, 1, v___x_2628_);
v___x_2637_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2616_, v___x_2636_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2639_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
lean_inc(v_a_2571_);
v___x_2639_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v_a_2638_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2639_;
goto v___jp_2583_;
}
else
{
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
return v___x_2637_;
}
}
}
v___jp_2614_:
{
lean_object* v___x_2615_; 
lean_inc(v_a_2571_);
v___x_2615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v___x_2607_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2615_;
goto v___jp_2583_;
}
}
else
{
lean_object* v___x_2640_; 
v___x_2640_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2562_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = lean_array_fget_borrowed(v_args_2565_, v_a_2571_);
v___x_2643_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2563_, v_a_2571_, v_next_2567_, v_a_2641_);
lean_dec(v_a_2641_);
if (lean_obj_tag(v___x_2643_) == 1)
{
lean_object* v_val_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2772_; 
v_val_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2772_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_val_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2772_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; uint8_t v_foApprox_2649_; uint8_t v_ctxApprox_2650_; uint8_t v_quasiPatternApprox_2651_; uint8_t v_constApprox_2652_; uint8_t v_isDefEqStuckEx_2653_; uint8_t v_unificationHints_2654_; uint8_t v_assignSyntheticOpaque_2655_; uint8_t v_offsetCnstrs_2656_; uint8_t v_transparency_2657_; uint8_t v_etaStruct_2658_; uint8_t v_univApprox_2659_; uint8_t v_iota_2660_; uint8_t v_beta_2661_; uint8_t v_proj_2662_; uint8_t v_zeta_2663_; uint8_t v_zetaDelta_2664_; uint8_t v_zetaUnused_2665_; uint8_t v_zetaHave_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2771_; 
v___x_2648_ = l_Lean_Meta_Context_config(v___y_2573_);
v_foApprox_2649_ = lean_ctor_get_uint8(v___x_2648_, 0);
v_ctxApprox_2650_ = lean_ctor_get_uint8(v___x_2648_, 1);
v_quasiPatternApprox_2651_ = lean_ctor_get_uint8(v___x_2648_, 2);
v_constApprox_2652_ = lean_ctor_get_uint8(v___x_2648_, 3);
v_isDefEqStuckEx_2653_ = lean_ctor_get_uint8(v___x_2648_, 4);
v_unificationHints_2654_ = lean_ctor_get_uint8(v___x_2648_, 5);
v_assignSyntheticOpaque_2655_ = lean_ctor_get_uint8(v___x_2648_, 7);
v_offsetCnstrs_2656_ = lean_ctor_get_uint8(v___x_2648_, 8);
v_transparency_2657_ = lean_ctor_get_uint8(v___x_2648_, 9);
v_etaStruct_2658_ = lean_ctor_get_uint8(v___x_2648_, 10);
v_univApprox_2659_ = lean_ctor_get_uint8(v___x_2648_, 11);
v_iota_2660_ = lean_ctor_get_uint8(v___x_2648_, 12);
v_beta_2661_ = lean_ctor_get_uint8(v___x_2648_, 13);
v_proj_2662_ = lean_ctor_get_uint8(v___x_2648_, 14);
v_zeta_2663_ = lean_ctor_get_uint8(v___x_2648_, 15);
v_zetaDelta_2664_ = lean_ctor_get_uint8(v___x_2648_, 16);
v_zetaUnused_2665_ = lean_ctor_get_uint8(v___x_2648_, 17);
v_zetaHave_2666_ = lean_ctor_get_uint8(v___x_2648_, 18);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2668_ = v___x_2648_;
v_isShared_2669_ = v_isSharedCheck_2771_;
goto v_resetjp_2667_;
}
else
{
lean_dec(v___x_2648_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2771_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
uint8_t v_trackZetaDelta_2670_; lean_object* v_zetaDeltaSet_2671_; lean_object* v_lctx_2672_; lean_object* v_localInstances_2673_; lean_object* v_defEqCtx_x3f_2674_; lean_object* v_synthPendingDepth_2675_; lean_object* v_canUnfold_x3f_2676_; uint8_t v_univApprox_2677_; uint8_t v_inTypeClassResolution_2678_; uint8_t v_cacheInferType_2679_; uint8_t v___x_2680_; lean_object* v___x_2682_; 
v_trackZetaDelta_2670_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*7);
v_zetaDeltaSet_2671_ = lean_ctor_get(v___y_2573_, 1);
v_lctx_2672_ = lean_ctor_get(v___y_2573_, 2);
v_localInstances_2673_ = lean_ctor_get(v___y_2573_, 3);
v_defEqCtx_x3f_2674_ = lean_ctor_get(v___y_2573_, 4);
v_synthPendingDepth_2675_ = lean_ctor_get(v___y_2573_, 5);
v_canUnfold_x3f_2676_ = lean_ctor_get(v___y_2573_, 6);
v_univApprox_2677_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2678_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*7 + 2);
v_cacheInferType_2679_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*7 + 3);
v___x_2680_ = 0;
if (v_isShared_2669_ == 0)
{
v___x_2682_ = v___x_2668_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 0, v_foApprox_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 1, v_ctxApprox_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 2, v_quasiPatternApprox_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 3, v_constApprox_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 4, v_isDefEqStuckEx_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 5, v_unificationHints_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 7, v_assignSyntheticOpaque_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 8, v_offsetCnstrs_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 9, v_transparency_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 10, v_etaStruct_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 11, v_univApprox_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 12, v_iota_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 13, v_beta_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 14, v_proj_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 15, v_zeta_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 16, v_zetaDelta_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 17, v_zetaUnused_2665_);
lean_ctor_set_uint8(v_reuseFailAlloc_2770_, 18, v_zetaHave_2666_);
v___x_2682_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
uint64_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v_foApprox_2687_; uint8_t v_ctxApprox_2688_; uint8_t v_quasiPatternApprox_2689_; uint8_t v_constApprox_2690_; uint8_t v_isDefEqStuckEx_2691_; uint8_t v_unificationHints_2692_; uint8_t v_proofIrrelevance_2693_; uint8_t v_assignSyntheticOpaque_2694_; uint8_t v_offsetCnstrs_2695_; uint8_t v_etaStruct_2696_; uint8_t v_univApprox_2697_; uint8_t v_iota_2698_; uint8_t v_beta_2699_; uint8_t v_proj_2700_; uint8_t v_zeta_2701_; uint8_t v_zetaDelta_2702_; uint8_t v_zetaUnused_2703_; uint8_t v_zetaHave_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2769_; 
lean_ctor_set_uint8(v___x_2682_, 6, v___x_2680_);
v___x_2683_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2682_);
v___x_2684_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set_uint64(v___x_2684_, sizeof(void*)*1, v___x_2683_);
lean_inc(v_canUnfold_x3f_2676_);
lean_inc(v_synthPendingDepth_2675_);
lean_inc(v_defEqCtx_x3f_2674_);
lean_inc_ref(v_localInstances_2673_);
lean_inc_ref(v_lctx_2672_);
lean_inc(v_zetaDeltaSet_2671_);
v___x_2685_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_ctor_set(v___x_2685_, 1, v_zetaDeltaSet_2671_);
lean_ctor_set(v___x_2685_, 2, v_lctx_2672_);
lean_ctor_set(v___x_2685_, 3, v_localInstances_2673_);
lean_ctor_set(v___x_2685_, 4, v_defEqCtx_x3f_2674_);
lean_ctor_set(v___x_2685_, 5, v_synthPendingDepth_2675_);
lean_ctor_set(v___x_2685_, 6, v_canUnfold_x3f_2676_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*7, v_trackZetaDelta_2670_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*7 + 1, v_univApprox_2677_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2678_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*7 + 3, v_cacheInferType_2679_);
v___x_2686_ = l_Lean_Meta_Context_config(v___x_2685_);
v_foApprox_2687_ = lean_ctor_get_uint8(v___x_2686_, 0);
v_ctxApprox_2688_ = lean_ctor_get_uint8(v___x_2686_, 1);
v_quasiPatternApprox_2689_ = lean_ctor_get_uint8(v___x_2686_, 2);
v_constApprox_2690_ = lean_ctor_get_uint8(v___x_2686_, 3);
v_isDefEqStuckEx_2691_ = lean_ctor_get_uint8(v___x_2686_, 4);
v_unificationHints_2692_ = lean_ctor_get_uint8(v___x_2686_, 5);
v_proofIrrelevance_2693_ = lean_ctor_get_uint8(v___x_2686_, 6);
v_assignSyntheticOpaque_2694_ = lean_ctor_get_uint8(v___x_2686_, 7);
v_offsetCnstrs_2695_ = lean_ctor_get_uint8(v___x_2686_, 8);
v_etaStruct_2696_ = lean_ctor_get_uint8(v___x_2686_, 10);
v_univApprox_2697_ = lean_ctor_get_uint8(v___x_2686_, 11);
v_iota_2698_ = lean_ctor_get_uint8(v___x_2686_, 12);
v_beta_2699_ = lean_ctor_get_uint8(v___x_2686_, 13);
v_proj_2700_ = lean_ctor_get_uint8(v___x_2686_, 14);
v_zeta_2701_ = lean_ctor_get_uint8(v___x_2686_, 15);
v_zetaDelta_2702_ = lean_ctor_get_uint8(v___x_2686_, 16);
v_zetaUnused_2703_ = lean_ctor_get_uint8(v___x_2686_, 17);
v_zetaHave_2704_ = lean_ctor_get_uint8(v___x_2686_, 18);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2706_ = v___x_2686_;
v_isShared_2707_ = v_isSharedCheck_2769_;
goto v_resetjp_2705_;
}
else
{
lean_dec(v___x_2686_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2769_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v_config_2712_; 
v___x_2708_ = l_Lean_instInhabitedExpr;
v___x_2709_ = lean_array_get_borrowed(v___x_2708_, v_params_2568_, v_val_2644_);
lean_dec(v_val_2644_);
v___x_2710_ = 2;
if (v_isShared_2707_ == 0)
{
v_config_2712_ = v___x_2706_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 0, v_foApprox_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 1, v_ctxApprox_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 2, v_quasiPatternApprox_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 3, v_constApprox_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 4, v_isDefEqStuckEx_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 5, v_unificationHints_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 6, v_proofIrrelevance_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 7, v_assignSyntheticOpaque_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 8, v_offsetCnstrs_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 10, v_etaStruct_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 11, v_univApprox_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 12, v_iota_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 13, v_beta_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 14, v_proj_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 15, v_zeta_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 16, v_zetaDelta_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 17, v_zetaUnused_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2768_, 18, v_zetaHave_2704_);
v_config_2712_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
uint64_t v___x_2713_; uint64_t v___x_2714_; uint64_t v___x_2715_; uint64_t v___x_2716_; uint64_t v___x_2717_; uint64_t v_key_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
lean_ctor_set_uint8(v_config_2712_, 9, v___x_2710_);
v___x_2713_ = l_Lean_Meta_Context_configKey(v___x_2685_);
lean_dec_ref_known(v___x_2685_, 7);
v___x_2714_ = 3ULL;
v___x_2715_ = lean_uint64_shift_right(v___x_2713_, v___x_2714_);
v___x_2716_ = lean_uint64_shift_left(v___x_2715_, v___x_2714_);
v___x_2717_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2718_ = lean_uint64_lor(v___x_2716_, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2719_, 0, v_config_2712_);
lean_ctor_set_uint64(v___x_2719_, sizeof(void*)*1, v_key_2718_);
lean_inc(v_canUnfold_x3f_2676_);
lean_inc(v_synthPendingDepth_2675_);
lean_inc(v_defEqCtx_x3f_2674_);
lean_inc_ref(v_localInstances_2673_);
lean_inc_ref(v_lctx_2672_);
lean_inc(v_zetaDeltaSet_2671_);
v___x_2720_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v_zetaDeltaSet_2671_);
lean_ctor_set(v___x_2720_, 2, v_lctx_2672_);
lean_ctor_set(v___x_2720_, 3, v_localInstances_2673_);
lean_ctor_set(v___x_2720_, 4, v_defEqCtx_x3f_2674_);
lean_ctor_set(v___x_2720_, 5, v_synthPendingDepth_2675_);
lean_ctor_set(v___x_2720_, 6, v_canUnfold_x3f_2676_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7, v_trackZetaDelta_2670_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 1, v_univApprox_2677_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2678_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 3, v_cacheInferType_2679_);
lean_inc(v___x_2642_);
lean_inc(v___x_2709_);
v___x_2721_ = l_Lean_Meta_isExprDefEq(v___x_2709_, v___x_2642_, v___x_2720_, v___y_2574_, v___y_2575_, v___y_2576_);
lean_dec_ref_known(v___x_2720_, 7);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; uint8_t v___x_2723_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2723_ = lean_unbox(v_a_2722_);
lean_dec(v_a_2722_);
if (v___x_2723_ == 0)
{
lean_object* v_options_2724_; lean_object* v_inheritedTraceOptions_2725_; uint8_t v_hasTrace_2726_; 
v_options_2724_ = lean_ctor_get(v___y_2575_, 2);
v_inheritedTraceOptions_2725_ = lean_ctor_get(v___y_2575_, 13);
v_hasTrace_2726_ = lean_ctor_get_uint8(v_options_2724_, sizeof(void*)*1);
if (v_hasTrace_2726_ == 0)
{
lean_del_object(v___x_2646_);
goto v___jp_2727_;
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2730_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2725_, v_options_2724_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_del_object(v___x_2646_);
goto v___jp_2727_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2732_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2563_);
v___x_2733_ = l_Nat_reprFast(v_val_2563_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 3);
lean_ctor_set(v___x_2646_, 0, v___x_2733_);
v___x_2735_ = v___x_2646_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2736_ = l_Lean_MessageData_ofFormat(v___x_2735_);
v___x_2737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2732_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
lean_inc(v_a_2571_);
v___x_2740_ = l_Nat_reprFast(v_a_2571_);
v___x_2741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
v___x_2742_ = l_Lean_MessageData_ofFormat(v___x_2741_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2739_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
lean_inc_ref(v_e_2566_);
v___x_2746_ = l_Lean_MessageData_ofExpr(v_e_2566_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
lean_inc(v___x_2709_);
v___x_2750_ = l_Lean_MessageData_ofExpr(v___x_2709_);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
lean_inc(v___x_2642_);
v___x_2754_ = l_Lean_MessageData_ofExpr(v___x_2642_);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2729_, v___x_2755_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
lean_inc(v_a_2571_);
v___x_2758_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v_a_2757_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2758_;
goto v___jp_2583_;
}
else
{
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
return v___x_2756_;
}
}
}
}
v___jp_2727_:
{
lean_object* v___x_2728_; 
lean_inc(v_a_2571_);
v___x_2728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v___x_2607_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2728_;
goto v___jp_2583_;
}
}
else
{
lean_del_object(v___x_2646_);
v_a_2579_ = v___x_2607_;
goto v___jp_2578_;
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_del_object(v___x_2646_);
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2760_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2721_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2721_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
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
lean_object* v___x_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v___x_2643_);
v___x_2773_ = lean_unsigned_to_nat(0u);
v___x_2774_ = 0;
lean_inc(v_a_2571_);
lean_inc(v___x_2642_);
v___x_2775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v___x_2569_, v_val_2562_, v_next_2567_, v_params_2568_, v___x_2642_, v_val_2563_, v_a_2571_, v___x_2570_, v___x_2773_, v___x_2774_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; uint8_t v___x_2777_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = lean_unbox(v_a_2776_);
lean_dec(v_a_2776_);
if (v___x_2777_ == 0)
{
lean_object* v_options_2778_; lean_object* v_inheritedTraceOptions_2779_; uint8_t v_hasTrace_2780_; 
v_options_2778_ = lean_ctor_get(v___y_2575_, 2);
v_inheritedTraceOptions_2779_ = lean_ctor_get(v___y_2575_, 13);
v_hasTrace_2780_ = lean_ctor_get_uint8(v_options_2778_, sizeof(void*)*1);
if (v_hasTrace_2780_ == 0)
{
goto v___jp_2781_;
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v___x_2783_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2784_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2785_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2779_, v_options_2778_, v___x_2784_);
if (v___x_2785_ == 0)
{
goto v___jp_2781_;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2786_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2563_);
v___x_2787_ = l_Nat_reprFast(v_val_2563_);
v___x_2788_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
v___x_2789_ = l_Lean_MessageData_ofFormat(v___x_2788_);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2786_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
lean_inc(v_a_2571_);
v___x_2793_ = l_Nat_reprFast(v_a_2571_);
v___x_2794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
v___x_2795_ = l_Lean_MessageData_ofFormat(v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2792_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
lean_inc_ref(v_e_2566_);
v___x_2799_ = l_Lean_MessageData_ofExpr(v_e_2566_);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
lean_inc(v___x_2642_);
v___x_2803_ = l_Lean_MessageData_ofExpr(v___x_2642_);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2783_, v___x_2806_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
lean_inc(v_a_2571_);
v___x_2809_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v_a_2808_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2809_;
goto v___jp_2583_;
}
else
{
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
return v___x_2807_;
}
}
}
v___jp_2781_:
{
lean_object* v___x_2782_; 
lean_inc(v_a_2571_);
v___x_2782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2562_, v_val_2563_, v_a_2571_, v___x_2607_, v___x_2607_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
v___y_2584_ = v___x_2782_;
goto v___jp_2583_;
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
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2810_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2775_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2775_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2818_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2640_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2640_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2826_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2605_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2605_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
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
lean_dec(v_a_2571_);
lean_dec_ref(v_e_2566_);
lean_dec(v_val_2563_);
v_a_2589_ = lean_ctor_get(v_a_2585_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v_a_2585_, 1);
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
lean_dec_ref_known(v_a_2585_, 1);
v_a_2579_ = v_a_2593_;
goto v___jp_2578_;
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2834_, lean_object* v_val_2835_, lean_object* v_upperBound_2836_, lean_object* v_args_2837_, lean_object* v_e_2838_, lean_object* v_next_2839_, lean_object* v_params_2840_, lean_object* v___x_2841_, lean_object* v___x_2842_, lean_object* v_a_2843_, lean_object* v_b_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v___x_44926__boxed_2850_; lean_object* v_res_2851_; 
v___x_44926__boxed_2850_ = lean_unbox(v___x_2842_);
v_res_2851_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2834_, v_val_2835_, v_upperBound_2836_, v_args_2837_, v_e_2838_, v_next_2839_, v_params_2840_, v___x_2841_, v___x_44926__boxed_2850_, v_a_2843_, v_b_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___x_2841_);
lean_dec_ref(v_params_2840_);
lean_dec(v_next_2839_);
lean_dec_ref(v_args_2837_);
lean_dec(v_upperBound_2836_);
lean_dec(v_val_2834_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2854_, lean_object* v___x_2855_, lean_object* v_val_2856_, lean_object* v_e_2857_, lean_object* v_next_2858_, lean_object* v_params_2859_, lean_object* v___x_2860_, lean_object* v_x_2861_, lean_object* v_x_2862_, lean_object* v_x_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 5)
{
lean_object* v_fn_2869_; lean_object* v_arg_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_fn_2869_ = lean_ctor_get(v_x_2861_, 0);
lean_inc_ref(v_fn_2869_);
v_arg_2870_ = lean_ctor_get(v_x_2861_, 1);
lean_inc_ref(v_arg_2870_);
lean_dec_ref_known(v_x_2861_, 2);
v___x_2871_ = lean_array_set(v_x_2862_, v_x_2863_, v_arg_2870_);
v___x_2872_ = lean_unsigned_to_nat(1u);
v___x_2873_ = lean_nat_sub(v_x_2863_, v___x_2872_);
lean_dec(v_x_2863_);
v_x_2861_ = v_fn_2869_;
v_x_2862_ = v___x_2871_;
v_x_2863_ = v___x_2873_;
goto _start;
}
else
{
uint8_t v___x_2875_; 
lean_dec(v_x_2863_);
v___x_2875_ = l_Lean_Expr_isConst(v_x_2861_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec_ref(v_x_2862_);
lean_dec_ref(v_x_2861_);
lean_dec_ref(v_e_2857_);
v___x_2876_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = l_Lean_Expr_constName_x21(v_x_2861_);
lean_dec_ref(v_x_2861_);
v___x_2879_ = lean_unsigned_to_nat(0u);
v___x_2880_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2878_, v_preDefs_2854_, v___x_2879_);
lean_dec(v___x_2878_);
if (lean_obj_tag(v___x_2880_) == 1)
{
lean_object* v_val_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v_val_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_array_get_borrowed(v___x_2879_, v___x_2855_, v_val_2881_);
v___x_2884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2856_, v_val_2881_, v___x_2883_, v_x_2862_, v_e_2857_, v_next_2858_, v_params_2859_, v___x_2860_, v___x_2875_, v___x_2879_, v___x_2882_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec_ref(v_x_2862_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2892_; 
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2892_ == 0)
{
lean_object* v_unused_2893_; 
v_unused_2893_ = lean_ctor_get(v___x_2884_, 0);
lean_dec(v_unused_2893_);
v___x_2886_ = v___x_2884_;
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
else
{
lean_dec(v___x_2884_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2892_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2888_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2888_);
v___x_2890_ = v___x_2886_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_a_2894_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2884_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2884_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
lean_dec(v___x_2880_);
lean_dec_ref(v_x_2862_);
lean_dec_ref(v_e_2857_);
v___x_2902_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
return v___x_2903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2904_, lean_object* v___x_2905_, lean_object* v_val_2906_, lean_object* v_e_2907_, lean_object* v_next_2908_, lean_object* v_params_2909_, lean_object* v___x_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2904_, v___x_2905_, v_val_2906_, v_e_2907_, v_next_2908_, v_params_2909_, v___x_2910_, v_x_2911_, v_x_2912_, v_x_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___x_2910_);
lean_dec_ref(v_params_2909_);
lean_dec(v_next_2908_);
lean_dec(v_val_2906_);
lean_dec_ref(v___x_2905_);
lean_dec_ref(v_preDefs_2904_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2920_, lean_object* v___x_2921_, lean_object* v_val_2922_, lean_object* v_a_2923_, lean_object* v_params_2924_, lean_object* v___x_2925_, lean_object* v_e_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_dummy_2932_; lean_object* v_nargs_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_dummy_2932_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2933_ = l_Lean_Expr_getAppNumArgs(v_e_2926_);
lean_inc(v_nargs_2933_);
v___x_2934_ = lean_mk_array(v_nargs_2933_, v_dummy_2932_);
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = lean_nat_sub(v_nargs_2933_, v___x_2935_);
lean_dec(v_nargs_2933_);
lean_inc_ref(v_e_2926_);
v___x_2937_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2920_, v___x_2921_, v_val_2922_, v_e_2926_, v_a_2923_, v_params_2924_, v___x_2925_, v_e_2926_, v___x_2934_, v___x_2936_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2938_, lean_object* v___x_2939_, lean_object* v_val_2940_, lean_object* v_a_2941_, lean_object* v_params_2942_, lean_object* v___x_2943_, lean_object* v_e_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2938_, v___x_2939_, v_val_2940_, v_a_2941_, v_params_2942_, v___x_2943_, v_e_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___x_2943_);
lean_dec_ref(v_params_2942_);
lean_dec(v_a_2941_);
lean_dec(v_val_2940_);
lean_dec_ref(v___x_2939_);
lean_dec_ref(v_preDefs_2938_);
return v_res_2950_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2954_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2955_ = lean_unsigned_to_nat(6u);
v___x_2956_ = lean_unsigned_to_nat(201u);
v___x_2957_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2959_ = l_mkPanicMessageWithDecl(v___x_2958_, v___x_2957_, v___x_2956_, v___x_2955_, v___x_2954_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2960_, lean_object* v___x_2961_, lean_object* v_a_2962_, lean_object* v_preDefs_2963_, lean_object* v_val_2964_, lean_object* v___f_2965_, lean_object* v___x_2966_, lean_object* v_params_2967_, lean_object* v_body_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v___x_2974_ = lean_array_get_size(v_params_2967_);
v___x_2975_ = lean_array_get_borrowed(v___x_2960_, v___x_2961_, v_a_2962_);
v___x_2976_ = lean_nat_dec_eq(v___x_2974_, v___x_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref(v_body_2968_);
lean_dec_ref(v_params_2967_);
lean_dec_ref(v___f_2965_);
lean_dec(v_val_2964_);
lean_dec_ref(v_preDefs_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v___x_2961_);
v___x_2977_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2978_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2977_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
return v___x_2978_;
}
else
{
lean_object* v___f_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; 
v___f_2979_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_2979_, 0, v_preDefs_2963_);
lean_closure_set(v___f_2979_, 1, v___x_2961_);
lean_closure_set(v___f_2979_, 2, v_val_2964_);
lean_closure_set(v___f_2979_, 3, v_a_2962_);
lean_closure_set(v___f_2979_, 4, v_params_2967_);
lean_closure_set(v___f_2979_, 5, v___x_2974_);
v___x_2980_ = 0;
v___x_2981_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2968_, v___f_2979_, v___f_2965_, v___x_2980_, v___x_2976_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2981_, 0);
lean_dec(v_unused_2989_);
v___x_2983_ = v___x_2981_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v___x_2981_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2966_);
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2966_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
v_a_2990_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2981_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2981_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2998_, lean_object* v___x_2999_, lean_object* v_a_3000_, lean_object* v_preDefs_3001_, lean_object* v_val_3002_, lean_object* v___f_3003_, lean_object* v___x_3004_, lean_object* v_params_3005_, lean_object* v_body_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2998_, v___x_2999_, v_a_3000_, v_preDefs_3001_, v_val_3002_, v___f_3003_, v___x_3004_, v_params_3005_, v_body_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___x_2998_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_e_3013_);
v___x_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v_preDefs_3029_, lean_object* v___x_3030_, lean_object* v_val_3031_, lean_object* v_upperBound_3032_, lean_object* v_a_3033_, lean_object* v_b_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
uint8_t v___x_3040_; 
v___x_3040_ = lean_nat_dec_lt(v_a_3033_, v_upperBound_3032_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
lean_dec(v_a_3033_);
lean_dec(v_val_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_preDefs_3029_);
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v_b_3034_);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; lean_object* v_value_3043_; lean_object* v___f_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___f_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3042_ = lean_array_fget_borrowed(v_preDefs_3029_, v_a_3033_);
v_value_3043_ = lean_ctor_get(v___x_3042_, 7);
v___f_3044_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = lean_box(0);
lean_inc(v_val_3031_);
lean_inc_ref(v_preDefs_3029_);
lean_inc(v_a_3033_);
lean_inc_ref(v___x_3030_);
v___f_3047_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3047_, 0, v___x_3045_);
lean_closure_set(v___f_3047_, 1, v___x_3030_);
lean_closure_set(v___f_3047_, 2, v_a_3033_);
lean_closure_set(v___f_3047_, 3, v_preDefs_3029_);
lean_closure_set(v___f_3047_, 4, v_val_3031_);
lean_closure_set(v___f_3047_, 5, v___f_3044_);
lean_closure_set(v___f_3047_, 6, v___x_3046_);
v___x_3048_ = 0;
lean_inc_ref(v_value_3043_);
v___x_3049_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3043_, v___f_3047_, v___x_3048_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec_ref_known(v___x_3049_, 1);
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_nat_add(v_a_3033_, v___x_3050_);
lean_dec(v_a_3033_);
v_a_3033_ = v___x_3051_;
v_b_3034_ = v___x_3046_;
goto _start;
}
else
{
lean_dec(v_a_3033_);
lean_dec(v_val_3031_);
lean_dec_ref(v___x_3030_);
lean_dec_ref(v_preDefs_3029_);
return v___x_3049_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v_preDefs_3053_, lean_object* v___x_3054_, lean_object* v_val_3055_, lean_object* v_upperBound_3056_, lean_object* v_a_3057_, lean_object* v_b_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3053_, v___x_3054_, v_val_3055_, v_upperBound_3056_, v_a_3057_, v_b_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v_upperBound_3056_);
return v_res_3064_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
size_t v_sz_3074_; size_t v___x_3075_; lean_object* v___x_3076_; 
v_sz_3074_ = lean_array_size(v_preDefs_3068_);
v___x_3075_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3068_);
v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3074_, v___x_3075_, v_preDefs_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; size_t v_sz_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc_n(v_a_3077_, 2);
lean_dec_ref_known(v___x_3076_, 1);
v_sz_3078_ = lean_array_size(v_a_3077_);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3078_, v___x_3075_, v_a_3077_);
v___x_3080_ = l_Lean_Elab_FixedParams_Info_init(v_a_3077_);
v___x_3081_ = lean_st_mk_ref(v___x_3080_);
v___x_3082_ = lean_st_ref_take(v___x_3081_);
v___x_3083_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3082_);
v___x_3084_ = lean_st_ref_set(v___x_3081_, v___x_3083_);
v___x_3085_ = lean_array_get_size(v_preDefs_3068_);
v___x_3086_ = lean_unsigned_to_nat(0u);
v___x_3087_ = lean_box(0);
lean_inc(v___x_3081_);
v___x_3088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3068_, v___x_3079_, v___x_3081_, v___x_3085_, v___x_3086_, v___x_3087_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3127_; 
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3088_, 0);
lean_dec(v_unused_3128_);
v___x_3090_ = v___x_3088_;
v_isShared_3091_ = v_isSharedCheck_3127_;
goto v_resetjp_3089_;
}
else
{
lean_dec(v___x_3088_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3127_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3092_; lean_object* v_options_3093_; uint8_t v_hasTrace_3094_; 
v___x_3092_ = lean_st_ref_get(v___x_3081_);
lean_dec(v___x_3081_);
v_options_3093_ = lean_ctor_get(v_a_3071_, 2);
v_hasTrace_3094_ = lean_ctor_get_uint8(v_options_3093_, sizeof(void*)*1);
if (v_hasTrace_3094_ == 0)
{
lean_object* v___x_3096_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3092_);
v___x_3096_ = v___x_3090_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3092_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_inheritedTraceOptions_3098_ = lean_ctor_get(v_a_3071_, 13);
v___x_3099_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3100_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3101_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3098_, v_options_3093_, v___x_3100_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3103_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3092_);
v___x_3103_ = v___x_3090_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3092_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_del_object(v___x_3090_);
v___x_3105_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3092_);
v___x_3106_ = l_Lean_Elab_FixedParams_Info_format(v___x_3092_);
v___x_3107_ = l_Std_Format_indentD(v___x_3106_);
v___x_3108_ = l_Lean_MessageData_ofFormat(v___x_3107_);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3105_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3099_, v___x_3109_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3110_, 0);
lean_dec(v_unused_3118_);
v___x_3112_ = v___x_3110_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_dec(v___x_3110_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3092_);
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3092_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v___x_3092_);
v_a_3119_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3110_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3110_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v___x_3081_);
v_a_3129_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3088_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3088_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec_ref(v_preDefs_3068_);
v_a_3137_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3076_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3076_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_upperBound_3152_, lean_object* v_val_3153_, lean_object* v_next_3154_, lean_object* v_params_3155_, lean_object* v___x_3156_, lean_object* v_val_3157_, lean_object* v_next_3158_, uint8_t v___x_3159_, lean_object* v_inst_3160_, lean_object* v_R_3161_, lean_object* v_a_3162_, uint8_t v_b_3163_, lean_object* v_c_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_3152_, v_val_3153_, v_next_3154_, v_params_3155_, v___x_3156_, v_val_3157_, v_next_3158_, v___x_3159_, v_a_3162_, v_b_3163_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3171_ = _args[0];
lean_object* v_val_3172_ = _args[1];
lean_object* v_next_3173_ = _args[2];
lean_object* v_params_3174_ = _args[3];
lean_object* v___x_3175_ = _args[4];
lean_object* v_val_3176_ = _args[5];
lean_object* v_next_3177_ = _args[6];
lean_object* v___x_3178_ = _args[7];
lean_object* v_inst_3179_ = _args[8];
lean_object* v_R_3180_ = _args[9];
lean_object* v_a_3181_ = _args[10];
lean_object* v_b_3182_ = _args[11];
lean_object* v_c_3183_ = _args[12];
lean_object* v___y_3184_ = _args[13];
lean_object* v___y_3185_ = _args[14];
lean_object* v___y_3186_ = _args[15];
lean_object* v___y_3187_ = _args[16];
lean_object* v___y_3188_ = _args[17];
_start:
{
uint8_t v___x_45875__boxed_3189_; uint8_t v_b_boxed_3190_; lean_object* v_res_3191_; 
v___x_45875__boxed_3189_ = lean_unbox(v___x_3178_);
v_b_boxed_3190_ = lean_unbox(v_b_3182_);
v_res_3191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_upperBound_3171_, v_val_3172_, v_next_3173_, v_params_3174_, v___x_3175_, v_val_3176_, v_next_3177_, v___x_45875__boxed_3189_, v_inst_3179_, v_R_3180_, v_a_3181_, v_b_boxed_3190_, v_c_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v_val_3176_);
lean_dec_ref(v_params_3174_);
lean_dec(v_next_3173_);
lean_dec(v_val_3172_);
lean_dec(v_upperBound_3171_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3192_, lean_object* v_val_3193_, lean_object* v_upperBound_3194_, lean_object* v_args_3195_, lean_object* v_e_3196_, lean_object* v_next_3197_, lean_object* v_params_3198_, lean_object* v___x_3199_, uint8_t v___x_3200_, lean_object* v_inst_3201_, lean_object* v_R_3202_, lean_object* v_a_3203_, lean_object* v_b_3204_, lean_object* v_c_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3192_, v_val_3193_, v_upperBound_3194_, v_args_3195_, v_e_3196_, v_next_3197_, v_params_3198_, v___x_3199_, v___x_3200_, v_a_3203_, v_b_3204_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3212_ = _args[0];
lean_object* v_val_3213_ = _args[1];
lean_object* v_upperBound_3214_ = _args[2];
lean_object* v_args_3215_ = _args[3];
lean_object* v_e_3216_ = _args[4];
lean_object* v_next_3217_ = _args[5];
lean_object* v_params_3218_ = _args[6];
lean_object* v___x_3219_ = _args[7];
lean_object* v___x_3220_ = _args[8];
lean_object* v_inst_3221_ = _args[9];
lean_object* v_R_3222_ = _args[10];
lean_object* v_a_3223_ = _args[11];
lean_object* v_b_3224_ = _args[12];
lean_object* v_c_3225_ = _args[13];
lean_object* v___y_3226_ = _args[14];
lean_object* v___y_3227_ = _args[15];
lean_object* v___y_3228_ = _args[16];
lean_object* v___y_3229_ = _args[17];
lean_object* v___y_3230_ = _args[18];
_start:
{
uint8_t v___x_45910__boxed_3231_; lean_object* v_res_3232_; 
v___x_45910__boxed_3231_ = lean_unbox(v___x_3220_);
v_res_3232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3212_, v_val_3213_, v_upperBound_3214_, v_args_3215_, v_e_3216_, v_next_3217_, v_params_3218_, v___x_3219_, v___x_45910__boxed_3231_, v_inst_3221_, v_R_3222_, v_a_3223_, v_b_3224_, v_c_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___x_3219_);
lean_dec_ref(v_params_3218_);
lean_dec(v_next_3217_);
lean_dec_ref(v_args_3215_);
lean_dec(v_upperBound_3214_);
lean_dec(v_val_3212_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v_preDefs_3233_, lean_object* v___x_3234_, lean_object* v_val_3235_, lean_object* v_upperBound_3236_, lean_object* v_inst_3237_, lean_object* v_R_3238_, lean_object* v_a_3239_, lean_object* v_b_3240_, lean_object* v_c_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3233_, v___x_3234_, v_val_3235_, v_upperBound_3236_, v_a_3239_, v_b_3240_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v_preDefs_3248_, lean_object* v___x_3249_, lean_object* v_val_3250_, lean_object* v_upperBound_3251_, lean_object* v_inst_3252_, lean_object* v_R_3253_, lean_object* v_a_3254_, lean_object* v_b_3255_, lean_object* v_c_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v_preDefs_3248_, v___x_3249_, v_val_3250_, v_upperBound_3251_, v_inst_3252_, v_R_3253_, v_a_3254_, v_b_3255_, v_c_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v_upperBound_3251_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3263_, lean_object* v___x_3264_, lean_object* v_pre_3265_, lean_object* v_post_3266_, uint8_t v_usedLetOnly_3267_, uint8_t v_skipConstInApp_3268_, uint8_t v_skipInstances_3269_, lean_object* v___x_3270_, lean_object* v_inst_3271_, lean_object* v_R_3272_, lean_object* v_a_3273_, lean_object* v_b_3274_, lean_object* v_c_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3263_, v___x_3264_, v_pre_3265_, v_post_3266_, v_usedLetOnly_3267_, v_skipConstInApp_3268_, v_skipInstances_3269_, v_a_3273_, v_b_3274_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3283_ = _args[0];
lean_object* v___x_3284_ = _args[1];
lean_object* v_pre_3285_ = _args[2];
lean_object* v_post_3286_ = _args[3];
lean_object* v_usedLetOnly_3287_ = _args[4];
lean_object* v_skipConstInApp_3288_ = _args[5];
lean_object* v_skipInstances_3289_ = _args[6];
lean_object* v___x_3290_ = _args[7];
lean_object* v_inst_3291_ = _args[8];
lean_object* v_R_3292_ = _args[9];
lean_object* v_a_3293_ = _args[10];
lean_object* v_b_3294_ = _args[11];
lean_object* v_c_3295_ = _args[12];
lean_object* v___y_3296_ = _args[13];
lean_object* v___y_3297_ = _args[14];
lean_object* v___y_3298_ = _args[15];
lean_object* v___y_3299_ = _args[16];
lean_object* v___y_3300_ = _args[17];
lean_object* v___y_3301_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3302_; uint8_t v_skipConstInApp_boxed_3303_; uint8_t v_skipInstances_boxed_3304_; lean_object* v_res_3305_; 
v_usedLetOnly_boxed_3302_ = lean_unbox(v_usedLetOnly_3287_);
v_skipConstInApp_boxed_3303_ = lean_unbox(v_skipConstInApp_3288_);
v_skipInstances_boxed_3304_ = lean_unbox(v_skipInstances_3289_);
v_res_3305_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3283_, v___x_3284_, v_pre_3285_, v_post_3286_, v_usedLetOnly_boxed_3302_, v_skipConstInApp_boxed_3303_, v_skipInstances_boxed_3304_, v___x_3290_, v_inst_3291_, v_R_3292_, v_a_3293_, v_b_3294_, v_c_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___x_3290_);
lean_dec_ref(v___x_3284_);
lean_dec(v_upperBound_3283_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3306_, lean_object* v_m_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3307_, v_a_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3310_, lean_object* v_m_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3310_, v_m_3311_, v_a_3312_);
lean_dec_ref(v_a_3312_);
lean_dec_ref(v_m_3311_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3314_, lean_object* v_name_3315_, uint8_t v_bi_3316_, lean_object* v_type_3317_, lean_object* v_k_3318_, uint8_t v_kind_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3315_, v_bi_3316_, v_type_3317_, v_k_3318_, v_kind_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3327_, lean_object* v_name_3328_, lean_object* v_bi_3329_, lean_object* v_type_3330_, lean_object* v_k_3331_, lean_object* v_kind_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
uint8_t v_bi_boxed_3339_; uint8_t v_kind_boxed_3340_; lean_object* v_res_3341_; 
v_bi_boxed_3339_ = lean_unbox(v_bi_3329_);
v_kind_boxed_3340_ = lean_unbox(v_kind_3332_);
v_res_3341_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3327_, v_name_3328_, v_bi_boxed_3339_, v_type_3330_, v_k_3331_, v_kind_boxed_3340_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3342_, lean_object* v_name_3343_, lean_object* v_type_3344_, lean_object* v_val_3345_, lean_object* v_k_3346_, uint8_t v_nondep_3347_, uint8_t v_kind_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3343_, v_type_3344_, v_val_3345_, v_k_3346_, v_nondep_3347_, v_kind_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3356_, lean_object* v_name_3357_, lean_object* v_type_3358_, lean_object* v_val_3359_, lean_object* v_k_3360_, lean_object* v_nondep_3361_, lean_object* v_kind_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
uint8_t v_nondep_boxed_3369_; uint8_t v_kind_boxed_3370_; lean_object* v_res_3371_; 
v_nondep_boxed_3369_ = lean_unbox(v_nondep_3361_);
v_kind_boxed_3370_ = lean_unbox(v_kind_3362_);
v_res_3371_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3356_, v_name_3357_, v_type_3358_, v_val_3359_, v_k_3360_, v_nondep_boxed_3369_, v_kind_boxed_3370_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3372_, lean_object* v_ref_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3373_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_ref_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3380_, v_ref_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3388_, lean_object* v_x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3397_, lean_object* v_x_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3397_, v_x_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3406_, lean_object* v_m_3407_, lean_object* v_a_3408_, lean_object* v_b_3409_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3407_, v_a_3408_, v_b_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3411_, lean_object* v_a_3412_, lean_object* v_x_3413_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3412_, v_x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3415_, lean_object* v_a_3416_, lean_object* v_x_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3415_, v_a_3416_, v_x_3417_);
lean_dec(v_x_3417_);
lean_dec_ref(v_a_3416_);
return v_res_3418_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3419_, lean_object* v_a_3420_, lean_object* v_x_3421_){
_start:
{
uint8_t v___x_3422_; 
v___x_3422_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3420_, v_x_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3423_, lean_object* v_a_3424_, lean_object* v_x_3425_){
_start:
{
uint8_t v_res_3426_; lean_object* v_r_3427_; 
v_res_3426_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3423_, v_a_3424_, v_x_3425_);
lean_dec(v_x_3425_);
lean_dec_ref(v_a_3424_);
v_r_3427_ = lean_box(v_res_3426_);
return v_r_3427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3428_, lean_object* v_data_3429_){
_start:
{
lean_object* v___x_3430_; 
v___x_3430_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3431_, lean_object* v_a_3432_, lean_object* v_b_3433_, lean_object* v_x_3434_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3432_, v_b_3433_, v_x_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3436_, lean_object* v_i_3437_, lean_object* v_source_3438_, lean_object* v_target_3439_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3437_, v_source_3438_, v_target_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3441_, lean_object* v_x_3442_, lean_object* v_x_3443_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3442_, v_x_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3458_, lean_object* v_x_3459_){
_start:
{
if (lean_obj_tag(v_x_3458_) == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3460_;
}
else
{
lean_object* v_val_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3472_; 
v_val_3461_ = lean_ctor_get(v_x_3458_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_x_3458_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3463_ = v_x_3458_;
v_isShared_3464_ = v_isSharedCheck_3472_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_val_3461_);
lean_dec(v_x_3458_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3472_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3465_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3466_ = l_Nat_reprFast(v_val_3461_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set_tag(v___x_3463_, 3);
lean_ctor_set(v___x_3463_, 0, v___x_3466_);
v___x_3468_ = v___x_3463_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3466_);
v___x_3468_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3465_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = l_Repr_addAppParen(v___x_3469_, v_x_3459_);
return v___x_3470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3473_, lean_object* v_x_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3473_, v_x_3474_);
lean_dec(v_x_3474_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3476_, lean_object* v_x_3477_, lean_object* v_x_3478_){
_start:
{
if (lean_obj_tag(v_x_3478_) == 0)
{
lean_dec(v_x_3476_);
return v_x_3477_;
}
else
{
lean_object* v_head_3479_; lean_object* v_tail_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3491_; 
v_head_3479_ = lean_ctor_get(v_x_3478_, 0);
v_tail_3480_ = lean_ctor_get(v_x_3478_, 1);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_x_3478_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3482_ = v_x_3478_;
v_isShared_3483_ = v_isSharedCheck_3491_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_tail_3480_);
lean_inc(v_head_3479_);
lean_dec(v_x_3478_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3491_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
lean_inc(v_x_3476_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set_tag(v___x_3482_, 5);
lean_ctor_set(v___x_3482_, 1, v_x_3476_);
lean_ctor_set(v___x_3482_, 0, v_x_3477_);
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_x_3477_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_x_3476_);
v___x_3485_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = lean_unsigned_to_nat(0u);
v___x_3487_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3479_, v___x_3486_);
v___x_3488_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3485_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v_x_3477_ = v___x_3488_;
v_x_3478_ = v_tail_3480_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3492_, lean_object* v_x_3493_, lean_object* v_x_3494_){
_start:
{
if (lean_obj_tag(v_x_3494_) == 0)
{
lean_dec(v_x_3492_);
return v_x_3493_;
}
else
{
lean_object* v_head_3495_; lean_object* v_tail_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3507_; 
v_head_3495_ = lean_ctor_get(v_x_3494_, 0);
v_tail_3496_ = lean_ctor_get(v_x_3494_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_x_3494_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3498_ = v_x_3494_;
v_isShared_3499_ = v_isSharedCheck_3507_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_tail_3496_);
lean_inc(v_head_3495_);
lean_dec(v_x_3494_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3507_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
lean_inc(v_x_3492_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set_tag(v___x_3498_, 5);
lean_ctor_set(v___x_3498_, 1, v_x_3492_);
lean_ctor_set(v___x_3498_, 0, v_x_3493_);
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_x_3493_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_x_3492_);
v___x_3501_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3502_ = lean_unsigned_to_nat(0u);
v___x_3503_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3495_, v___x_3502_);
v___x_3504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3501_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3492_, v___x_3504_, v_tail_3496_);
return v___x_3505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = lean_unsigned_to_nat(0u);
v___x_3510_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3508_, v___x_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3511_, lean_object* v_x_3512_){
_start:
{
if (lean_obj_tag(v_x_3511_) == 0)
{
lean_object* v___x_3513_; 
lean_dec(v_x_3512_);
v___x_3513_ = lean_box(0);
return v___x_3513_;
}
else
{
lean_object* v_tail_3514_; 
v_tail_3514_ = lean_ctor_get(v_x_3511_, 1);
if (lean_obj_tag(v_tail_3514_) == 0)
{
lean_object* v_head_3515_; lean_object* v___x_3516_; 
lean_dec(v_x_3512_);
v_head_3515_ = lean_ctor_get(v_x_3511_, 0);
lean_inc(v_head_3515_);
lean_dec_ref_known(v_x_3511_, 2);
v___x_3516_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3515_);
return v___x_3516_;
}
else
{
lean_object* v_head_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_inc(v_tail_3514_);
v_head_3517_ = lean_ctor_get(v_x_3511_, 0);
lean_inc(v_head_3517_);
lean_dec_ref_known(v_x_3511_, 2);
v___x_3518_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3517_);
v___x_3519_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3512_, v___x_3518_, v_tail_3514_);
return v___x_3519_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3528_ = lean_string_length(v___x_3527_);
return v___x_3528_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3530_ = lean_nat_to_int(v___x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3536_){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3537_ = lean_array_get_size(v_xs_3536_);
v___x_3538_ = lean_unsigned_to_nat(0u);
v___x_3539_ = lean_nat_dec_eq(v___x_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3540_ = lean_array_to_list(v_xs_3536_);
v___x_3541_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3542_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3540_, v___x_3541_);
v___x_3543_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3544_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v___x_3542_);
v___x_3546_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3543_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = l_Std_Format_fill(v___x_3548_);
return v___x_3549_;
}
else
{
lean_object* v___x_3550_; 
lean_dec_ref(v_xs_3536_);
v___x_3550_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3550_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3551_, lean_object* v_x_3552_, lean_object* v_x_3553_){
_start:
{
if (lean_obj_tag(v_x_3553_) == 0)
{
lean_dec(v_x_3551_);
return v_x_3552_;
}
else
{
lean_object* v_head_3554_; lean_object* v_tail_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3565_; 
v_head_3554_ = lean_ctor_get(v_x_3553_, 0);
v_tail_3555_ = lean_ctor_get(v_x_3553_, 1);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_x_3553_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3557_ = v_x_3553_;
v_isShared_3558_ = v_isSharedCheck_3565_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_tail_3555_);
lean_inc(v_head_3554_);
lean_dec(v_x_3553_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3565_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
lean_inc(v_x_3551_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 5);
lean_ctor_set(v___x_3557_, 1, v_x_3551_);
lean_ctor_set(v___x_3557_, 0, v_x_3552_);
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_x_3552_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_x_3551_);
v___x_3560_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3554_);
v___x_3562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v_x_3552_ = v___x_3562_;
v_x_3553_ = v_tail_3555_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3566_, lean_object* v_x_3567_){
_start:
{
if (lean_obj_tag(v_x_3566_) == 0)
{
lean_object* v___x_3568_; 
lean_dec(v_x_3567_);
v___x_3568_ = lean_box(0);
return v___x_3568_;
}
else
{
lean_object* v_tail_3569_; 
v_tail_3569_ = lean_ctor_get(v_x_3566_, 1);
if (lean_obj_tag(v_tail_3569_) == 0)
{
lean_object* v_head_3570_; lean_object* v___x_3571_; 
lean_dec(v_x_3567_);
v_head_3570_ = lean_ctor_get(v_x_3566_, 0);
lean_inc(v_head_3570_);
lean_dec_ref_known(v_x_3566_, 2);
v___x_3571_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3570_);
return v___x_3571_;
}
else
{
lean_object* v_head_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
lean_inc(v_tail_3569_);
v_head_3572_ = lean_ctor_get(v_x_3566_, 0);
lean_inc(v_head_3572_);
lean_dec_ref_known(v_x_3566_, 2);
v___x_3573_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3572_);
v___x_3574_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3567_, v___x_3573_, v_tail_3569_);
return v___x_3574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3575_){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3576_ = lean_array_get_size(v_xs_3575_);
v___x_3577_ = lean_unsigned_to_nat(0u);
v___x_3578_ = lean_nat_dec_eq(v___x_3576_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3579_ = lean_array_to_list(v_xs_3575_);
v___x_3580_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3581_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3579_, v___x_3580_);
v___x_3582_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3583_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
lean_ctor_set(v___x_3584_, 1, v___x_3581_);
v___x_3585_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3586_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3584_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3582_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = l_Std_Format_fill(v___x_3587_);
return v___x_3588_;
}
else
{
lean_object* v___x_3589_; 
lean_dec_ref(v_xs_3575_);
v___x_3589_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3589_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_){
_start:
{
if (lean_obj_tag(v_x_3592_) == 0)
{
lean_dec(v_x_3590_);
return v_x_3591_;
}
else
{
lean_object* v_head_3593_; lean_object* v_tail_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3605_; 
v_head_3593_ = lean_ctor_get(v_x_3592_, 0);
v_tail_3594_ = lean_ctor_get(v_x_3592_, 1);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_x_3592_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3596_ = v_x_3592_;
v_isShared_3597_ = v_isSharedCheck_3605_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_tail_3594_);
lean_inc(v_head_3593_);
lean_dec(v_x_3592_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3605_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
lean_inc(v_x_3590_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set_tag(v___x_3596_, 5);
lean_ctor_set(v___x_3596_, 1, v_x_3590_);
lean_ctor_set(v___x_3596_, 0, v_x_3591_);
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_x_3591_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_x_3590_);
v___x_3599_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = l_Nat_reprFast(v_head_3593_);
v___x_3601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
v___x_3602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3599_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v_x_3591_ = v___x_3602_;
v_x_3592_ = v_tail_3594_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3606_, lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
if (lean_obj_tag(v_x_3608_) == 0)
{
lean_dec(v_x_3606_);
return v_x_3607_;
}
else
{
lean_object* v_head_3609_; lean_object* v_tail_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3621_; 
v_head_3609_ = lean_ctor_get(v_x_3608_, 0);
v_tail_3610_ = lean_ctor_get(v_x_3608_, 1);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_x_3608_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3612_ = v_x_3608_;
v_isShared_3613_ = v_isSharedCheck_3621_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_tail_3610_);
lean_inc(v_head_3609_);
lean_dec(v_x_3608_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3621_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
lean_inc(v_x_3606_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 5);
lean_ctor_set(v___x_3612_, 1, v_x_3606_);
lean_ctor_set(v___x_3612_, 0, v_x_3607_);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_x_3607_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_x_3606_);
v___x_3615_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3616_ = l_Nat_reprFast(v_head_3609_);
v___x_3617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
v___x_3618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3615_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3606_, v___x_3618_, v_tail_3610_);
return v___x_3619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3623_ = l_Nat_reprFast(v___y_3622_);
v___x_3624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3625_, lean_object* v_x_3626_){
_start:
{
if (lean_obj_tag(v_x_3625_) == 0)
{
lean_object* v___x_3627_; 
lean_dec(v_x_3626_);
v___x_3627_ = lean_box(0);
return v___x_3627_;
}
else
{
lean_object* v_tail_3628_; 
v_tail_3628_ = lean_ctor_get(v_x_3625_, 1);
if (lean_obj_tag(v_tail_3628_) == 0)
{
lean_object* v_head_3629_; lean_object* v___x_3630_; 
lean_dec(v_x_3626_);
v_head_3629_ = lean_ctor_get(v_x_3625_, 0);
lean_inc(v_head_3629_);
lean_dec_ref_known(v_x_3625_, 2);
v___x_3630_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3629_);
return v___x_3630_;
}
else
{
lean_object* v_head_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_inc(v_tail_3628_);
v_head_3631_ = lean_ctor_get(v_x_3625_, 0);
lean_inc(v_head_3631_);
lean_dec_ref_known(v_x_3625_, 2);
v___x_3632_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3631_);
v___x_3633_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3626_, v___x_3632_, v_tail_3628_);
return v___x_3633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3634_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3635_ = lean_array_get_size(v_xs_3634_);
v___x_3636_ = lean_unsigned_to_nat(0u);
v___x_3637_ = lean_nat_dec_eq(v___x_3635_, v___x_3636_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3638_ = lean_array_to_list(v_xs_3634_);
v___x_3639_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3640_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3638_, v___x_3639_);
v___x_3641_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3642_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
lean_ctor_set(v___x_3643_, 1, v___x_3640_);
v___x_3644_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3645_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3643_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3641_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = l_Std_Format_fill(v___x_3646_);
return v___x_3647_;
}
else
{
lean_object* v___x_3648_; 
lean_dec_ref(v_xs_3634_);
v___x_3648_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3648_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_){
_start:
{
if (lean_obj_tag(v_x_3651_) == 0)
{
lean_dec(v_x_3649_);
return v_x_3650_;
}
else
{
lean_object* v_head_3652_; lean_object* v_tail_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3663_; 
v_head_3652_ = lean_ctor_get(v_x_3651_, 0);
v_tail_3653_ = lean_ctor_get(v_x_3651_, 1);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_x_3651_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3655_ = v_x_3651_;
v_isShared_3656_ = v_isSharedCheck_3663_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_tail_3653_);
lean_inc(v_head_3652_);
lean_dec(v_x_3651_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3663_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
lean_inc(v_x_3649_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 5);
lean_ctor_set(v___x_3655_, 1, v_x_3649_);
lean_ctor_set(v___x_3655_, 0, v_x_3650_);
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_x_3650_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_x_3649_);
v___x_3658_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3652_);
v___x_3660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3658_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v_x_3650_ = v___x_3660_;
v_x_3651_ = v_tail_3653_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3664_, lean_object* v_x_3665_){
_start:
{
if (lean_obj_tag(v_x_3664_) == 0)
{
lean_object* v___x_3666_; 
lean_dec(v_x_3665_);
v___x_3666_ = lean_box(0);
return v___x_3666_;
}
else
{
lean_object* v_tail_3667_; 
v_tail_3667_ = lean_ctor_get(v_x_3664_, 1);
if (lean_obj_tag(v_tail_3667_) == 0)
{
lean_object* v_head_3668_; lean_object* v___x_3669_; 
lean_dec(v_x_3665_);
v_head_3668_ = lean_ctor_get(v_x_3664_, 0);
lean_inc(v_head_3668_);
lean_dec_ref_known(v_x_3664_, 2);
v___x_3669_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3668_);
return v___x_3669_;
}
else
{
lean_object* v_head_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_inc(v_tail_3667_);
v_head_3670_ = lean_ctor_get(v_x_3664_, 0);
lean_inc(v_head_3670_);
lean_dec_ref_known(v_x_3664_, 2);
v___x_3671_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3670_);
v___x_3672_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3665_, v___x_3671_, v_tail_3667_);
return v___x_3672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3673_){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v___x_3674_ = lean_array_get_size(v_xs_3673_);
v___x_3675_ = lean_unsigned_to_nat(0u);
v___x_3676_ = lean_nat_dec_eq(v___x_3674_, v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3677_ = lean_array_to_list(v_xs_3673_);
v___x_3678_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3679_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3677_, v___x_3678_);
v___x_3680_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3681_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v___x_3679_);
v___x_3683_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3680_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = l_Std_Format_fill(v___x_3685_);
return v___x_3686_;
}
else
{
lean_object* v___x_3687_; 
lean_dec_ref(v_xs_3673_);
v___x_3687_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3687_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3688_, lean_object* v_x_3689_, lean_object* v_x_3690_){
_start:
{
if (lean_obj_tag(v_x_3690_) == 0)
{
lean_dec(v_x_3688_);
return v_x_3689_;
}
else
{
lean_object* v_head_3691_; lean_object* v_tail_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3702_; 
v_head_3691_ = lean_ctor_get(v_x_3690_, 0);
v_tail_3692_ = lean_ctor_get(v_x_3690_, 1);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_x_3690_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3694_ = v_x_3690_;
v_isShared_3695_ = v_isSharedCheck_3702_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_tail_3692_);
lean_inc(v_head_3691_);
lean_dec(v_x_3690_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3702_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
lean_inc(v_x_3688_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set_tag(v___x_3694_, 5);
lean_ctor_set(v___x_3694_, 1, v_x_3688_);
lean_ctor_set(v___x_3694_, 0, v_x_3689_);
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_x_3689_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_x_3688_);
v___x_3697_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3691_);
v___x_3699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3697_);
lean_ctor_set(v___x_3699_, 1, v___x_3698_);
v_x_3689_ = v___x_3699_;
v_x_3690_ = v_tail_3692_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3703_, lean_object* v_x_3704_){
_start:
{
if (lean_obj_tag(v_x_3703_) == 0)
{
lean_object* v___x_3705_; 
lean_dec(v_x_3704_);
v___x_3705_ = lean_box(0);
return v___x_3705_;
}
else
{
lean_object* v_tail_3706_; 
v_tail_3706_ = lean_ctor_get(v_x_3703_, 1);
if (lean_obj_tag(v_tail_3706_) == 0)
{
lean_object* v_head_3707_; lean_object* v___x_3708_; 
lean_dec(v_x_3704_);
v_head_3707_ = lean_ctor_get(v_x_3703_, 0);
lean_inc(v_head_3707_);
lean_dec_ref_known(v_x_3703_, 2);
v___x_3708_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3707_);
return v___x_3708_;
}
else
{
lean_object* v_head_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
lean_inc(v_tail_3706_);
v_head_3709_ = lean_ctor_get(v_x_3703_, 0);
lean_inc(v_head_3709_);
lean_dec_ref_known(v_x_3703_, 2);
v___x_3710_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3709_);
v___x_3711_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3704_, v___x_3710_, v_tail_3706_);
return v___x_3711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3712_){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3713_ = lean_array_get_size(v_xs_3712_);
v___x_3714_ = lean_unsigned_to_nat(0u);
v___x_3715_ = lean_nat_dec_eq(v___x_3713_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3716_ = lean_array_to_list(v_xs_3712_);
v___x_3717_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3718_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3716_, v___x_3717_);
v___x_3719_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3720_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
lean_ctor_set(v___x_3721_, 1, v___x_3718_);
v___x_3722_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3719_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = l_Std_Format_fill(v___x_3724_);
return v___x_3725_;
}
else
{
lean_object* v___x_3726_; 
lean_dec_ref(v_xs_3712_);
v___x_3726_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3726_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = lean_unsigned_to_nat(12u);
v___x_3741_ = lean_nat_to_int(v___x_3740_);
return v___x_3741_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = lean_unsigned_to_nat(9u);
v___x_3746_ = lean_nat_to_int(v___x_3745_);
return v___x_3746_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = lean_unsigned_to_nat(11u);
v___x_3751_ = lean_nat_to_int(v___x_3750_);
return v___x_3751_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3754_ = lean_string_length(v___x_3753_);
return v___x_3754_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3756_ = lean_nat_to_int(v___x_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3761_){
_start:
{
lean_object* v_numFixed_3762_; lean_object* v_perms_3763_; lean_object* v_revDeps_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v_numFixed_3762_ = lean_ctor_get(v_x_3761_, 0);
lean_inc(v_numFixed_3762_);
v_perms_3763_ = lean_ctor_get(v_x_3761_, 1);
lean_inc_ref(v_perms_3763_);
v_revDeps_3764_ = lean_ctor_get(v_x_3761_, 2);
lean_inc_ref(v_revDeps_3764_);
lean_dec_ref(v_x_3761_);
v___x_3765_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3766_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3767_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3768_ = l_Nat_reprFast(v_numFixed_3762_);
v___x_3769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3767_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = 0;
v___x_3772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
lean_ctor_set_uint8(v___x_3772_, sizeof(void*)*1, v___x_3771_);
v___x_3773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3766_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3773_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = lean_box(1);
v___x_3777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3775_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
lean_ctor_set(v___x_3780_, 1, v___x_3765_);
v___x_3781_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3782_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3763_);
v___x_3783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*1, v___x_3771_);
v___x_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3780_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
lean_ctor_set(v___x_3786_, 1, v___x_3774_);
v___x_3787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
lean_ctor_set(v___x_3787_, 1, v___x_3776_);
v___x_3788_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
lean_ctor_set(v___x_3790_, 1, v___x_3765_);
v___x_3791_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3792_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3764_);
v___x_3793_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set_uint8(v___x_3794_, sizeof(void*)*1, v___x_3771_);
v___x_3795_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3790_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3797_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v___x_3795_);
v___x_3799_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3800_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3796_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set_uint8(v___x_3802_, sizeof(void*)*1, v___x_3771_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3803_, lean_object* v_prec_3804_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3803_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3806_, lean_object* v_prec_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3806_, v_prec_3807_);
lean_dec(v_prec_3807_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___f_3817_; lean_object* v___x_5797__overap_3818_; lean_object* v___x_3819_; 
v___f_3817_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5797__overap_3818_ = lean_panic_fn_borrowed(v___f_3817_, v_msg_3811_);
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3814_);
lean_inc(v___y_3813_);
lean_inc_ref(v___y_3812_);
v___x_3819_ = lean_apply_5(v___x_5797__overap_3818_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, lean_box(0));
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___f_3833_; lean_object* v___x_5807__overap_3834_; lean_object* v___x_3835_; 
v___f_3833_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5807__overap_3834_ = lean_panic_fn_borrowed(v___f_3833_, v_msg_3827_);
lean_inc(v___y_3831_);
lean_inc_ref(v___y_3830_);
lean_inc(v___y_3829_);
lean_inc_ref(v___y_3828_);
v___x_3835_ = lean_apply_5(v___x_5807__overap_3834_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, lean_box(0));
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___f_3849_; lean_object* v___x_5817__overap_3850_; lean_object* v___x_3851_; 
v___f_3849_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5817__overap_3850_ = lean_panic_fn_borrowed(v___f_3849_, v_msg_3843_);
lean_inc(v___y_3847_);
lean_inc_ref(v___y_3846_);
lean_inc(v___y_3845_);
lean_inc_ref(v___y_3844_);
v___x_3851_ = lean_apply_5(v___x_5817__overap_3850_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, lean_box(0));
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
return v_res_3858_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3862_ = lean_unsigned_to_nat(12u);
v___x_3863_ = lean_unsigned_to_nat(294u);
v___x_3864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3865_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3866_ = l_mkPanicMessageWithDecl(v___x_3865_, v___x_3864_, v___x_3863_, v___x_3862_, v___x_3861_);
return v___x_3866_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3869_ = lean_unsigned_to_nat(12u);
v___x_3870_ = lean_unsigned_to_nat(297u);
v___x_3871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3872_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3873_ = l_mkPanicMessageWithDecl(v___x_3872_, v___x_3871_, v___x_3870_, v___x_3869_, v___x_3868_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3874_, lean_object* v_as_3875_, size_t v_sz_3876_, size_t v_i_3877_, lean_object* v_b_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_a_3885_; uint8_t v___x_3889_; 
v___x_3889_ = lean_usize_dec_lt(v_i_3877_, v_sz_3876_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3890_, 0, v_b_3878_);
return v___x_3890_;
}
else
{
lean_object* v_a_3891_; 
v_a_3891_ = lean_array_uget_borrowed(v_as_3875_, v_i_3877_);
if (lean_obj_tag(v_a_3891_) == 1)
{
lean_object* v_val_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_val_3892_ = lean_ctor_get(v_a_3891_, 0);
v___x_3893_ = lean_unsigned_to_nat(0u);
v___x_3894_ = lean_box(0);
v___x_3895_ = lean_array_get_borrowed(v___x_3894_, v_val_3892_, v___x_3893_);
if (lean_obj_tag(v___x_3895_) == 1)
{
lean_object* v_val_3896_; lean_object* v___x_3897_; 
v_val_3896_ = lean_ctor_get(v___x_3895_, 0);
v___x_3897_ = lean_array_get_borrowed(v___x_3894_, v___x_3874_, v_val_3896_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec_ref(v_b_3878_);
v___x_3898_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3899_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3898_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3909_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3909_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3909_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
if (lean_obj_tag(v_a_3900_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; 
v_a_3904_ = lean_ctor_get(v_a_3900_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v_a_3900_, 1);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v_a_3904_);
v___x_3906_ = v___x_3902_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
else
{
lean_object* v_a_3908_; 
lean_del_object(v___x_3902_);
v_a_3908_ = lean_ctor_get(v_a_3900_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v_a_3900_, 1);
v_a_3885_ = v_a_3908_;
goto v___jp_3884_;
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
v_a_3910_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3899_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3899_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_object* v___x_3918_; 
lean_inc_ref(v___x_3897_);
v___x_3918_ = lean_array_push(v_b_3878_, v___x_3897_);
v_a_3885_ = v___x_3918_;
goto v___jp_3884_;
}
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3920_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3919_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_dec_ref_known(v___x_3920_, 1);
v_a_3885_ = v_b_3878_;
goto v___jp_3884_;
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref(v_b_3878_);
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
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
}
else
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = lean_box(0);
v___x_3930_ = lean_array_push(v_b_3878_, v___x_3929_);
v_a_3885_ = v___x_3930_;
goto v___jp_3884_;
}
}
v___jp_3884_:
{
size_t v___x_3886_; size_t v___x_3887_; 
v___x_3886_ = ((size_t)1ULL);
v___x_3887_ = lean_usize_add(v_i_3877_, v___x_3886_);
v_i_3877_ = v___x_3887_;
v_b_3878_ = v_a_3885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3931_, lean_object* v_as_3932_, lean_object* v_sz_3933_, lean_object* v_i_3934_, lean_object* v_b_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
size_t v_sz_boxed_3941_; size_t v_i_boxed_3942_; lean_object* v_res_3943_; 
v_sz_boxed_3941_ = lean_unbox_usize(v_sz_3933_);
lean_dec(v_sz_3933_);
v_i_boxed_3942_ = lean_unbox_usize(v_i_3934_);
lean_dec(v_i_3934_);
v_res_3943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3931_, v_as_3932_, v_sz_boxed_3941_, v_i_boxed_3942_, v_b_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_as_3932_);
lean_dec_ref(v___x_3931_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3946_, lean_object* v___x_3947_, lean_object* v___x_3948_, lean_object* v_a_3949_, lean_object* v_b_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
uint8_t v___x_3956_; 
v___x_3956_ = lean_nat_dec_lt(v_a_3949_, v_upperBound_3946_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; 
lean_dec(v_a_3949_);
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v_b_3950_);
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3959_; size_t v_sz_3960_; size_t v___x_3961_; lean_object* v___x_3962_; 
v___x_3958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3959_ = lean_array_fget_borrowed(v___x_3947_, v_a_3949_);
v_sz_3960_ = lean_array_size(v___x_3959_);
v___x_3961_ = ((size_t)0ULL);
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3948_, v___x_3959_, v_sz_3960_, v___x_3961_, v___x_3958_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___x_3964_ = lean_array_push(v_b_3950_, v_a_3963_);
v___x_3965_ = lean_unsigned_to_nat(1u);
v___x_3966_ = lean_nat_add(v_a_3949_, v___x_3965_);
lean_dec(v_a_3949_);
v_a_3949_ = v___x_3966_;
v_b_3950_ = v___x_3964_;
goto _start;
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec_ref(v_b_3950_);
lean_dec(v_a_3949_);
v_a_3968_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3962_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3962_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3976_, lean_object* v___x_3977_, lean_object* v___x_3978_, lean_object* v_a_3979_, lean_object* v_b_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3976_, v___x_3977_, v___x_3978_, v_a_3979_, v_b_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec_ref(v___x_3978_);
lean_dec_ref(v___x_3977_);
lean_dec(v_upperBound_3976_);
return v_res_3986_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3988_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3989_ = lean_unsigned_to_nat(8u);
v___x_3990_ = lean_unsigned_to_nat(281u);
v___x_3991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3992_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3993_ = l_mkPanicMessageWithDecl(v___x_3992_, v___x_3991_, v___x_3990_, v___x_3989_, v___x_3988_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3994_, lean_object* v_a_3995_, lean_object* v_b_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_a_4003_; uint8_t v___x_4007_; 
v___x_4007_ = lean_nat_dec_lt(v_a_3995_, v_upperBound_3994_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; 
lean_dec(v_a_3995_);
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v_b_3996_);
return v___x_4008_;
}
else
{
lean_object* v_snd_4009_; lean_object* v_snd_4010_; lean_object* v_snd_4011_; lean_object* v_fst_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4136_; 
v_snd_4009_ = lean_ctor_get(v_b_3996_, 1);
lean_inc(v_snd_4009_);
v_snd_4010_ = lean_ctor_get(v_snd_4009_, 1);
lean_inc(v_snd_4010_);
v_snd_4011_ = lean_ctor_get(v_snd_4010_, 1);
lean_inc(v_snd_4011_);
v_fst_4012_ = lean_ctor_get(v_b_3996_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_b_3996_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; 
v_unused_4137_ = lean_ctor_get(v_b_3996_, 1);
lean_dec(v_unused_4137_);
v___x_4014_ = v_b_3996_;
v_isShared_4015_ = v_isSharedCheck_4136_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_fst_4012_);
lean_dec(v_b_3996_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4136_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v_fst_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4134_; 
v_fst_4016_ = lean_ctor_get(v_snd_4009_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_snd_4009_);
if (v_isSharedCheck_4134_ == 0)
{
lean_object* v_unused_4135_; 
v_unused_4135_ = lean_ctor_get(v_snd_4009_, 1);
lean_dec(v_unused_4135_);
v___x_4018_ = v_snd_4009_;
v_isShared_4019_ = v_isSharedCheck_4134_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_fst_4016_);
lean_dec(v_snd_4009_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4134_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v_fst_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4132_; 
v_fst_4020_ = lean_ctor_get(v_snd_4010_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_snd_4010_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; 
v_unused_4133_ = lean_ctor_get(v_snd_4010_, 1);
lean_dec(v_unused_4133_);
v___x_4022_ = v_snd_4010_;
v_isShared_4023_ = v_isSharedCheck_4132_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_fst_4020_);
lean_dec(v_snd_4010_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4132_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v_array_4024_; lean_object* v_start_4025_; lean_object* v_stop_4026_; uint8_t v___x_4027_; 
v_array_4024_ = lean_ctor_get(v_snd_4011_, 0);
v_start_4025_ = lean_ctor_get(v_snd_4011_, 1);
v_stop_4026_ = lean_ctor_get(v_snd_4011_, 2);
v___x_4027_ = lean_nat_dec_lt(v_start_4025_, v_stop_4026_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4029_; 
lean_dec(v_a_3995_);
if (v_isShared_4023_ == 0)
{
v___x_4029_ = v___x_4022_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_fst_4020_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v_snd_4011_);
v___x_4029_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4031_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4029_);
v___x_4031_ = v___x_4018_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_fst_4016_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v___x_4029_);
v___x_4031_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4033_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v___x_4031_);
v___x_4033_ = v___x_4014_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_fst_4012_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
return v___x_4034_;
}
}
}
}
else
{
lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4128_; 
lean_inc(v_stop_4026_);
lean_inc(v_start_4025_);
lean_inc_ref(v_array_4024_);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_snd_4011_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; lean_object* v_unused_4130_; lean_object* v_unused_4131_; 
v_unused_4129_ = lean_ctor_get(v_snd_4011_, 2);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_snd_4011_, 1);
lean_dec(v_unused_4130_);
v_unused_4131_ = lean_ctor_get(v_snd_4011_, 0);
lean_dec(v_unused_4131_);
v___x_4039_ = v_snd_4011_;
v_isShared_4040_ = v_isSharedCheck_4128_;
goto v_resetjp_4038_;
}
else
{
lean_dec(v_snd_4011_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4128_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v_array_4041_; lean_object* v_start_4042_; lean_object* v_stop_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
v_array_4041_ = lean_ctor_get(v_fst_4020_, 0);
v_start_4042_ = lean_ctor_get(v_fst_4020_, 1);
v_stop_4043_ = lean_ctor_get(v_fst_4020_, 2);
v___x_4044_ = lean_array_fget(v_array_4024_, v_start_4025_);
v___x_4045_ = lean_unsigned_to_nat(1u);
v___x_4046_ = lean_nat_add(v_start_4025_, v___x_4045_);
lean_dec(v_start_4025_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 1, v___x_4046_);
v___x_4048_ = v___x_4039_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_array_4024_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4127_, 2, v_stop_4026_);
v___x_4048_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
uint8_t v___x_4049_; 
v___x_4049_ = lean_nat_dec_lt(v_start_4042_, v_stop_4043_);
if (v___x_4049_ == 0)
{
lean_object* v___x_4051_; 
lean_dec(v___x_4044_);
lean_dec(v_a_3995_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4048_);
v___x_4051_ = v___x_4022_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_fst_4020_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v___x_4048_);
v___x_4051_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4053_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4051_);
v___x_4053_ = v___x_4018_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_fst_4016_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v___x_4051_);
v___x_4053_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
lean_object* v___x_4055_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v___x_4053_);
v___x_4055_ = v___x_4014_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_fst_4012_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; 
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
}
}
}
else
{
lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4123_; 
lean_inc(v_stop_4043_);
lean_inc(v_start_4042_);
lean_inc_ref(v_array_4041_);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_fst_4020_);
if (v_isSharedCheck_4123_ == 0)
{
lean_object* v_unused_4124_; lean_object* v_unused_4125_; lean_object* v_unused_4126_; 
v_unused_4124_ = lean_ctor_get(v_fst_4020_, 2);
lean_dec(v_unused_4124_);
v_unused_4125_ = lean_ctor_get(v_fst_4020_, 1);
lean_dec(v_unused_4125_);
v_unused_4126_ = lean_ctor_get(v_fst_4020_, 0);
lean_dec(v_unused_4126_);
v___x_4061_ = v_fst_4020_;
v_isShared_4062_ = v_isSharedCheck_4123_;
goto v_resetjp_4060_;
}
else
{
lean_dec(v_fst_4020_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4123_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4063_; lean_object* v___x_4065_; 
v___x_4063_ = lean_nat_add(v_start_4042_, v___x_4045_);
lean_dec(v_start_4042_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 1, v___x_4063_);
v___x_4065_ = v___x_4061_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_array_4041_);
lean_ctor_set(v_reuseFailAlloc_4122_, 1, v___x_4063_);
lean_ctor_set(v_reuseFailAlloc_4122_, 2, v_stop_4043_);
v___x_4065_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
if (lean_obj_tag(v___x_4044_) == 1)
{
lean_object* v_val_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4110_; 
v_val_4066_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4068_ = v___x_4044_;
v_isShared_4069_ = v_isSharedCheck_4110_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_val_4066_);
lean_dec(v___x_4044_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4110_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4075_; 
v___x_4070_ = lean_unsigned_to_nat(0u);
v___x_4071_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4072_ = lean_box(0);
v___x_4073_ = lean_array_get(v___x_4072_, v_val_4066_, v___x_4070_);
lean_dec(v_val_4066_);
lean_inc(v_a_3995_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 0, v_a_3995_);
v___x_4075_ = v___x_4068_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_3995_);
v___x_4075_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
uint8_t v___x_4076_; 
v___x_4076_ = l_Option_instDecidableEq___redArg(v___x_4071_, v___x_4073_, v___x_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
lean_dec_ref(v___x_4065_);
lean_dec_ref(v___x_4048_);
lean_del_object(v___x_4022_);
lean_del_object(v___x_4018_);
lean_dec(v_fst_4016_);
lean_del_object(v___x_4014_);
lean_dec(v_fst_4012_);
v___x_4077_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4078_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4077_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4088_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4088_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4088_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
if (lean_obj_tag(v_a_4079_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4085_; 
lean_dec(v_a_3995_);
v_a_4083_ = lean_ctor_get(v_a_4079_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v_a_4079_, 1);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v_a_4083_);
v___x_4085_ = v___x_4081_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4083_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
else
{
lean_object* v_a_4087_; 
lean_del_object(v___x_4081_);
v_a_4087_ = lean_ctor_get(v_a_4079_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v_a_4079_, 1);
v_a_4003_ = v_a_4087_;
goto v___jp_4002_;
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v_a_3995_);
v_a_4089_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4078_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4078_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4101_; 
lean_inc(v_fst_4016_);
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_fst_4016_);
v___x_4098_ = lean_array_push(v_fst_4012_, v___x_4097_);
v___x_4099_ = lean_nat_add(v_fst_4016_, v___x_4045_);
lean_dec(v_fst_4016_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4048_);
lean_ctor_set(v___x_4022_, 0, v___x_4065_);
v___x_4101_ = v___x_4022_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v___x_4048_);
v___x_4101_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
lean_object* v___x_4103_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4101_);
lean_ctor_set(v___x_4018_, 0, v___x_4099_);
v___x_4103_ = v___x_4018_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4099_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
lean_object* v___x_4105_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v___x_4103_);
lean_ctor_set(v___x_4014_, 0, v___x_4098_);
v___x_4105_ = v___x_4014_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4098_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
v_a_4003_ = v___x_4105_;
goto v___jp_4002_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
lean_dec(v___x_4044_);
v___x_4111_ = lean_box(0);
v___x_4112_ = lean_array_push(v_fst_4012_, v___x_4111_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4048_);
lean_ctor_set(v___x_4022_, 0, v___x_4065_);
v___x_4114_ = v___x_4022_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v___x_4048_);
v___x_4114_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4116_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4114_);
v___x_4116_ = v___x_4018_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_fst_4016_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4114_);
v___x_4116_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
lean_object* v___x_4118_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 1, v___x_4116_);
lean_ctor_set(v___x_4014_, 0, v___x_4112_);
v___x_4118_ = v___x_4014_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4116_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
v_a_4003_ = v___x_4118_;
goto v___jp_4002_;
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
v___jp_4002_:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = lean_unsigned_to_nat(1u);
v___x_4005_ = lean_nat_add(v_a_3995_, v___x_4004_);
lean_dec(v_a_3995_);
v_a_3995_ = v___x_4005_;
v_b_3996_ = v_a_4003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4138_, lean_object* v_a_4139_, lean_object* v_b_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4138_, v_a_4139_, v_b_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v_upperBound_4138_);
return v_res_4146_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4148_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4149_ = lean_unsigned_to_nat(4u);
v___x_4150_ = lean_unsigned_to_nat(275u);
v___x_4151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4152_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4153_ = l_mkPanicMessageWithDecl(v___x_4152_, v___x_4151_, v___x_4150_, v___x_4149_, v___x_4148_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4154_, lean_object* v___x_4155_, lean_object* v___x_4156_, lean_object* v_xs_4157_, lean_object* v_x_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_graph_4164_; lean_object* v_revDeps_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4218_; 
v_graph_4164_ = lean_ctor_get(v_a_4154_, 0);
v_revDeps_4165_ = lean_ctor_get(v_a_4154_, 1);
v_isSharedCheck_4218_ = !lean_is_exclusive(v_a_4154_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4167_ = v_a_4154_;
v_isShared_4168_ = v_isSharedCheck_4218_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_revDeps_4165_);
lean_inc(v_graph_4164_);
lean_dec(v_a_4154_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4218_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
v___x_4169_ = lean_array_get_borrowed(v___x_4155_, v_graph_4164_, v___x_4156_);
v___x_4170_ = lean_array_get_size(v_xs_4157_);
v___x_4171_ = lean_array_get_size(v___x_4169_);
v___x_4172_ = lean_nat_dec_eq(v___x_4170_, v___x_4171_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_del_object(v___x_4167_);
lean_dec_ref(v_revDeps_4165_);
lean_dec_ref(v_graph_4164_);
lean_dec_ref(v_xs_4157_);
lean_dec(v___x_4156_);
v___x_4173_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4174_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4173_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
return v___x_4174_;
}
else
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4175_ = lean_mk_empty_array_with_capacity(v___x_4156_);
lean_inc_n(v___x_4156_, 2);
v___x_4176_ = l_Array_toSubarray___redArg(v_xs_4157_, v___x_4156_, v___x_4170_);
lean_inc(v___x_4169_);
v___x_4177_ = l_Array_toSubarray___redArg(v___x_4169_, v___x_4156_, v___x_4171_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 1, v___x_4177_);
lean_ctor_set(v___x_4167_, 0, v___x_4176_);
v___x_4179_ = v___x_4167_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4176_);
lean_ctor_set(v_reuseFailAlloc_4217_, 1, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_inc(v___x_4156_);
v___x_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4156_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4175_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4170_, v___x_4156_, v___x_4181_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v_snd_4184_; lean_object* v_fst_4185_; lean_object* v_fst_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4182_, 1);
v_snd_4184_ = lean_ctor_get(v_a_4183_, 1);
lean_inc(v_snd_4184_);
v_fst_4185_ = lean_ctor_get(v_a_4183_, 0);
lean_inc_n(v_fst_4185_, 2);
lean_dec(v_a_4183_);
v_fst_4186_ = lean_ctor_get(v_snd_4184_, 0);
lean_inc(v_fst_4186_);
lean_dec(v_snd_4184_);
v___x_4187_ = lean_unsigned_to_nat(1u);
v___x_4188_ = lean_array_get_size(v_graph_4164_);
v___x_4189_ = lean_mk_empty_array_with_capacity(v___x_4187_);
v___x_4190_ = lean_array_push(v___x_4189_, v_fst_4185_);
v___x_4191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4188_, v_graph_4164_, v_fst_4185_, v___x_4187_, v___x_4190_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v_fst_4185_);
lean_dec_ref(v_graph_4164_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4200_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4194_ = v___x_4191_;
v_isShared_4195_ = v_isSharedCheck_4200_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4200_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4196_; lean_object* v___x_4198_; 
v___x_4196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4196_, 0, v_fst_4186_);
lean_ctor_set(v___x_4196_, 1, v_a_4192_);
lean_ctor_set(v___x_4196_, 2, v_revDeps_4165_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v___x_4196_);
v___x_4198_ = v___x_4194_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_dec(v_fst_4186_);
lean_dec_ref(v_revDeps_4165_);
v_a_4201_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4191_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4191_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_dec_ref(v_revDeps_4165_);
lean_dec_ref(v_graph_4164_);
v_a_4209_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4182_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4182_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4219_, lean_object* v___x_4220_, lean_object* v___x_4221_, lean_object* v_xs_4222_, lean_object* v_x_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4219_, v___x_4220_, v___x_4221_, v_xs_4222_, v_x_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec_ref(v_x_4223_);
lean_dec_ref(v___x_4220_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4236_; 
lean_inc_ref(v_preDefs_4230_);
v___x_4236_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v_value_4241_; lean_object* v___x_4242_; lean_object* v___f_4243_; uint8_t v___x_4244_; lean_object* v___x_4245_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4238_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4239_ = lean_unsigned_to_nat(0u);
v___x_4240_ = lean_array_get(v___x_4238_, v_preDefs_4230_, v___x_4239_);
lean_dec_ref(v_preDefs_4230_);
v_value_4241_ = lean_ctor_get(v___x_4240_, 7);
lean_inc_ref(v_value_4241_);
lean_dec(v___x_4240_);
v___x_4242_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4243_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4243_, 0, v_a_4237_);
lean_closure_set(v___f_4243_, 1, v___x_4242_);
lean_closure_set(v___f_4243_, 2, v___x_4239_);
v___x_4244_ = 0;
v___x_4245_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4241_, v___f_4243_, v___x_4244_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_);
return v___x_4245_;
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v_preDefs_4230_);
v_a_4246_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4236_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4236_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_);
lean_dec(v_a_4258_);
lean_dec_ref(v_a_4257_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4261_, lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v_inst_4264_, lean_object* v_R_4265_, lean_object* v_a_4266_, lean_object* v_b_4267_, lean_object* v_c_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4261_, v___x_4262_, v___x_4263_, v_a_4266_, v_b_4267_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4275_, lean_object* v___x_4276_, lean_object* v___x_4277_, lean_object* v_inst_4278_, lean_object* v_R_4279_, lean_object* v_a_4280_, lean_object* v_b_4281_, lean_object* v_c_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4275_, v___x_4276_, v___x_4277_, v_inst_4278_, v_R_4279_, v_a_4280_, v_b_4281_, v_c_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec_ref(v___x_4277_);
lean_dec_ref(v___x_4276_);
lean_dec(v_upperBound_4275_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4289_, lean_object* v_inst_4290_, lean_object* v_R_4291_, lean_object* v_a_4292_, lean_object* v_b_4293_, lean_object* v_c_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4289_, v_a_4292_, v_b_4293_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4301_, lean_object* v_inst_4302_, lean_object* v_R_4303_, lean_object* v_a_4304_, lean_object* v_b_4305_, lean_object* v_c_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4301_, v_inst_4302_, v_R_4303_, v_a_4304_, v_b_4305_, v_c_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v_upperBound_4301_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4313_, size_t v_i_4314_, size_t v_stop_4315_, lean_object* v_b_4316_){
_start:
{
uint8_t v___x_4317_; 
v___x_4317_ = lean_usize_dec_eq(v_i_4314_, v_stop_4315_);
if (v___x_4317_ == 0)
{
size_t v___x_4318_; size_t v___x_4319_; lean_object* v___x_4320_; 
v___x_4318_ = ((size_t)1ULL);
v___x_4319_ = lean_usize_sub(v_i_4314_, v___x_4318_);
v___x_4320_ = lean_array_uget_borrowed(v_as_4313_, v___x_4319_);
if (lean_obj_tag(v___x_4320_) == 0)
{
v_i_4314_ = v___x_4319_;
goto _start;
}
else
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4322_ = lean_unsigned_to_nat(1u);
v___x_4323_ = lean_nat_add(v_b_4316_, v___x_4322_);
lean_dec(v_b_4316_);
v_i_4314_ = v___x_4319_;
v_b_4316_ = v___x_4323_;
goto _start;
}
}
else
{
return v_b_4316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4325_, lean_object* v_i_4326_, lean_object* v_stop_4327_, lean_object* v_b_4328_){
_start:
{
size_t v_i_boxed_4329_; size_t v_stop_boxed_4330_; lean_object* v_res_4331_; 
v_i_boxed_4329_ = lean_unbox_usize(v_i_4326_);
lean_dec(v_i_4326_);
v_stop_boxed_4330_ = lean_unbox_usize(v_stop_4327_);
lean_dec(v_stop_4327_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4325_, v_i_boxed_4329_, v_stop_boxed_4330_, v_b_4328_);
lean_dec_ref(v_as_4325_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4332_){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_4333_ = lean_unsigned_to_nat(0u);
v___x_4334_ = lean_array_get_size(v_perm_4332_);
v___x_4335_ = lean_nat_dec_lt(v___x_4333_, v___x_4334_);
if (v___x_4335_ == 0)
{
return v___x_4333_;
}
else
{
size_t v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = lean_usize_of_nat(v___x_4334_);
v___x_4337_ = ((size_t)0ULL);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4332_, v___x_4336_, v___x_4337_, v___x_4333_);
return v___x_4338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4339_);
lean_dec_ref(v_perm_4339_);
return v_res_4340_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4341_, lean_object* v_i_4342_){
_start:
{
lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4343_ = lean_array_get_size(v_perm_4341_);
v___x_4344_ = lean_nat_dec_lt(v_i_4342_, v___x_4343_);
if (v___x_4344_ == 0)
{
return v___x_4344_;
}
else
{
lean_object* v___x_4345_; 
v___x_4345_ = lean_array_fget_borrowed(v_perm_4341_, v_i_4342_);
if (lean_obj_tag(v___x_4345_) == 0)
{
uint8_t v___x_4346_; 
v___x_4346_ = 0;
return v___x_4346_;
}
else
{
return v___x_4344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4347_, lean_object* v_i_4348_){
_start:
{
uint8_t v_res_4349_; lean_object* v_r_4350_; 
v_res_4349_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4347_, v_i_4348_);
lean_dec(v_i_4348_);
lean_dec_ref(v_perm_4347_);
v_r_4350_ = lean_box(v_res_4349_);
return v_r_4350_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___f_4357_; lean_object* v___x_1072__overap_4358_; lean_object* v___x_4359_; 
v___f_4357_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_1072__overap_4358_ = lean_panic_fn_borrowed(v___f_4357_, v_msg_4351_);
lean_inc(v___y_4355_);
lean_inc_ref(v___y_4354_);
lean_inc(v___y_4353_);
lean_inc_ref(v___y_4352_);
v___x_4359_ = lean_apply_5(v___x_1072__overap_4358_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, lean_box(0));
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4367_, lean_object* v_msg_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4375_, lean_object* v_msg_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4375_, v_msg_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4383_, lean_object* v_maxFVars_x3f_4384_, lean_object* v_k_4385_, uint8_t v_cleanupAnnotations_4386_, uint8_t v_whnfType_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___f_4393_; lean_object* v___x_4394_; 
v___f_4393_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4393_, 0, v_k_4385_);
v___x_4394_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4383_, v_maxFVars_x3f_4384_, v___f_4393_, v_cleanupAnnotations_4386_, v_whnfType_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
v_a_4403_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4394_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4394_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4411_, lean_object* v_maxFVars_x3f_4412_, lean_object* v_k_4413_, lean_object* v_cleanupAnnotations_4414_, lean_object* v_whnfType_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4421_; uint8_t v_whnfType_boxed_4422_; lean_object* v_res_4423_; 
v_cleanupAnnotations_boxed_4421_ = lean_unbox(v_cleanupAnnotations_4414_);
v_whnfType_boxed_4422_ = lean_unbox(v_whnfType_4415_);
v_res_4423_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4411_, v_maxFVars_x3f_4412_, v_k_4413_, v_cleanupAnnotations_boxed_4421_, v_whnfType_boxed_4422_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4424_, lean_object* v_type_4425_, lean_object* v_maxFVars_x3f_4426_, lean_object* v_k_4427_, uint8_t v_cleanupAnnotations_4428_, uint8_t v_whnfType_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4425_, v_maxFVars_x3f_4426_, v_k_4427_, v_cleanupAnnotations_4428_, v_whnfType_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4436_, lean_object* v_type_4437_, lean_object* v_maxFVars_x3f_4438_, lean_object* v_k_4439_, lean_object* v_cleanupAnnotations_4440_, lean_object* v_whnfType_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4447_; uint8_t v_whnfType_boxed_4448_; lean_object* v_res_4449_; 
v_cleanupAnnotations_boxed_4447_ = lean_unbox(v_cleanupAnnotations_4440_);
v_whnfType_boxed_4448_ = lean_unbox(v_whnfType_4441_);
v_res_4449_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4436_, v_type_4437_, v_maxFVars_x3f_4438_, v_k_4439_, v_cleanupAnnotations_boxed_4447_, v_whnfType_boxed_4448_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4449_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4452_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4453_ = lean_unsigned_to_nat(6u);
v___x_4454_ = lean_unsigned_to_nat(329u);
v___x_4455_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4456_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4457_ = l_mkPanicMessageWithDecl(v___x_4456_, v___x_4455_, v___x_4454_, v___x_4453_, v___x_4452_);
return v___x_4457_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4461_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4462_ = lean_unsigned_to_nat(8u);
v___x_4463_ = lean_unsigned_to_nat(322u);
v___x_4464_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4465_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4466_ = l_mkPanicMessageWithDecl(v___x_4465_, v___x_4464_, v___x_4463_, v___x_4462_, v___x_4461_);
return v___x_4466_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4468_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4469_ = lean_unsigned_to_nat(8u);
v___x_4470_ = lean_unsigned_to_nat(325u);
v___x_4471_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4472_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4473_ = l_mkPanicMessageWithDecl(v___x_4472_, v___x_4471_, v___x_4470_, v___x_4469_, v___x_4468_);
return v___x_4473_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4476_ = lean_unsigned_to_nat(8u);
v___x_4477_ = lean_unsigned_to_nat(324u);
v___x_4478_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4479_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4480_ = l_mkPanicMessageWithDecl(v___x_4479_, v___x_4478_, v___x_4477_, v___x_4476_, v___x_4475_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4481_, lean_object* v_xs_4482_, lean_object* v_val_4483_, lean_object* v_i_4484_, lean_object* v_perm_4485_, lean_object* v_k_4486_, lean_object* v_xs_x27_4487_, lean_object* v_type_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v___x_4494_; uint8_t v___x_4495_; 
v___x_4494_ = lean_array_get_size(v_xs_x27_4487_);
v___x_4495_ = lean_nat_dec_eq(v___x_4494_, v___x_4481_);
if (v___x_4495_ == 0)
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
lean_dec_ref(v_type_4488_);
lean_dec_ref(v_k_4486_);
lean_dec_ref(v_perm_4485_);
lean_dec_ref(v_xs_4482_);
v___x_4496_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4497_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4496_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4497_;
}
else
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v_x_4500_; lean_object* v___x_4501_; 
v___x_4498_ = l_Lean_instInhabitedExpr;
v___x_4499_ = lean_unsigned_to_nat(0u);
v_x_4500_ = lean_array_get_borrowed(v___x_4498_, v_xs_x27_4487_, v___x_4499_);
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc(v___y_4490_);
lean_inc_ref(v___y_4489_);
lean_inc(v_x_4500_);
v___x_4501_ = lean_infer_type(v_x_4500_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; uint8_t v___x_4503_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v___x_4503_ = l_Lean_Expr_hasLooseBVars(v_a_4502_);
lean_dec(v_a_4502_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = lean_array_get_size(v_xs_4482_);
v___x_4505_ = lean_nat_dec_lt(v_val_4483_, v___x_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
lean_dec_ref(v_type_4488_);
lean_dec_ref(v_k_4486_);
lean_dec_ref(v_perm_4485_);
lean_dec_ref(v_xs_4482_);
v___x_4506_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4507_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4506_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4507_;
}
else
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4508_ = lean_nat_add(v_i_4484_, v___x_4481_);
lean_inc(v_x_4500_);
v___x_4509_ = lean_array_set(v_xs_4482_, v_val_4483_, v_x_4500_);
v___x_4510_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4485_, v_k_4486_, v___x_4508_, v_type_4488_, v___x_4509_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4510_;
}
}
else
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_dec_ref(v_type_4488_);
lean_dec_ref(v_k_4486_);
lean_dec_ref(v_perm_4485_);
lean_dec_ref(v_xs_4482_);
v___x_4511_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4512_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4511_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4512_;
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec_ref(v_type_4488_);
lean_dec_ref(v_k_4486_);
lean_dec_ref(v_perm_4485_);
lean_dec_ref(v_xs_4482_);
v_a_4513_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4501_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4501_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4521_, lean_object* v_xs_4522_, lean_object* v_val_4523_, lean_object* v_i_4524_, lean_object* v_perm_4525_, lean_object* v_k_4526_, lean_object* v_xs_x27_4527_, lean_object* v_type_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4521_, v_xs_4522_, v_val_4523_, v_i_4524_, v_perm_4525_, v_k_4526_, v_xs_x27_4527_, v_type_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec_ref(v_xs_x27_4527_);
lean_dec(v_i_4524_);
lean_dec(v_val_4523_);
lean_dec(v___x_4521_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4535_, lean_object* v_k_4536_, lean_object* v_i_4537_, lean_object* v_type_4538_, lean_object* v_xs_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v___x_4545_; uint8_t v___x_4546_; 
v___x_4545_ = lean_array_get_size(v_perm_4535_);
v___x_4546_ = lean_nat_dec_lt(v_i_4537_, v___x_4545_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; 
lean_dec_ref(v_type_4538_);
lean_dec(v_i_4537_);
lean_dec_ref(v_perm_4535_);
lean_inc(v_a_4543_);
lean_inc_ref(v_a_4542_);
lean_inc(v_a_4541_);
lean_inc_ref(v_a_4540_);
v___x_4547_ = lean_apply_6(v_k_4536_, v_xs_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, lean_box(0));
return v___x_4547_;
}
else
{
lean_object* v___x_4548_; 
v___x_4548_ = lean_array_fget_borrowed(v_perm_4535_, v_i_4537_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v___x_4549_; 
lean_inc(v_a_4543_);
lean_inc_ref(v_a_4542_);
lean_inc(v_a_4541_);
lean_inc_ref(v_a_4540_);
v___x_4549_ = lean_whnf(v_type_4538_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; uint8_t v___x_4551_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v___x_4551_ = l_Lean_Expr_isForall(v_a_4550_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec(v_a_4550_);
lean_dec_ref(v_xs_4539_);
lean_dec(v_i_4537_);
lean_dec_ref(v_k_4536_);
lean_dec_ref(v_perm_4535_);
v___x_4552_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4553_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4552_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
return v___x_4553_;
}
else
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4554_ = lean_unsigned_to_nat(1u);
v___x_4555_ = lean_nat_add(v_i_4537_, v___x_4554_);
lean_dec(v_i_4537_);
v___x_4556_ = l_Lean_Expr_bindingBody_x21(v_a_4550_);
lean_dec(v_a_4550_);
v_i_4537_ = v___x_4555_;
v_type_4538_ = v___x_4556_;
goto _start;
}
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
lean_dec_ref(v_xs_4539_);
lean_dec(v_i_4537_);
lean_dec_ref(v_k_4536_);
lean_dec_ref(v_perm_4535_);
v_a_4558_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___x_4549_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4549_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
else
{
lean_object* v_val_4566_; lean_object* v___x_4567_; lean_object* v___f_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; lean_object* v___x_4571_; 
v_val_4566_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_val_4566_);
v___x_4567_ = lean_unsigned_to_nat(1u);
v___f_4568_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4568_, 0, v___x_4567_);
lean_closure_set(v___f_4568_, 1, v_xs_4539_);
lean_closure_set(v___f_4568_, 2, v_val_4566_);
lean_closure_set(v___f_4568_, 3, v_i_4537_);
lean_closure_set(v___f_4568_, 4, v_perm_4535_);
lean_closure_set(v___f_4568_, 5, v_k_4536_);
v___x_4569_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4570_ = 0;
v___x_4571_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4538_, v___x_4569_, v___f_4568_, v___x_4546_, v___x_4570_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
return v___x_4571_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4572_, lean_object* v_k_4573_, lean_object* v_i_4574_, lean_object* v_type_4575_, lean_object* v_xs_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4572_, v_k_4573_, v_i_4574_, v_type_4575_, v_xs_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4583_, lean_object* v_perm_4584_, lean_object* v_k_4585_, lean_object* v_i_4586_, lean_object* v_type_4587_, lean_object* v_xs_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4584_, v_k_4585_, v_i_4586_, v_type_4587_, v_xs_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4595_, lean_object* v_perm_4596_, lean_object* v_k_4597_, lean_object* v_i_4598_, lean_object* v_type_4599_, lean_object* v_xs_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4595_, v_perm_4596_, v_k_4597_, v_i_4598_, v_type_4599_, v_xs_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
lean_dec(v_a_4604_);
lean_dec_ref(v_a_4603_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
return v_res_4606_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4607_ = lean_unsigned_to_nat(0u);
v___x_4608_ = l_Lean_Level_ofNat(v___x_4607_);
return v___x_4608_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4610_ = l_Lean_mkSort(v___x_4609_);
return v___x_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4611_, lean_object* v_type_4612_, lean_object* v_k_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4619_ = lean_unsigned_to_nat(0u);
v___x_4620_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4611_);
v___x_4621_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4622_ = lean_mk_array(v___x_4620_, v___x_4621_);
v___x_4623_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4611_, v_k_4613_, v___x_4619_, v_type_4612_, v___x_4622_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4624_, lean_object* v_type_4625_, lean_object* v_k_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4624_, v_type_4625_, v_k_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4633_, lean_object* v_perm_4634_, lean_object* v_type_4635_, lean_object* v_k_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4634_, v_type_4635_, v_k_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4643_, lean_object* v_perm_4644_, lean_object* v_type_4645_, lean_object* v_k_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4643_, v_perm_4644_, v_type_4645_, v_k_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_);
lean_dec(v_a_4650_);
lean_dec_ref(v_a_4649_);
lean_dec(v_a_4648_);
lean_dec_ref(v_a_4647_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4653_, lean_object* v_runInBase_4654_, lean_object* v_b_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = lean_apply_1(v_k_4653_, v_b_4655_);
lean_inc(v___y_4659_);
lean_inc_ref(v___y_4658_);
lean_inc(v___y_4657_);
lean_inc_ref(v___y_4656_);
v___x_4662_ = lean_apply_7(v_runInBase_4654_, lean_box(0), v___x_4661_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, lean_box(0));
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4663_, lean_object* v_runInBase_4664_, lean_object* v_b_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4663_, v_runInBase_4664_, v_b_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4672_, lean_object* v_perm_4673_, lean_object* v_type_4674_, lean_object* v_runInBase_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v___f_4681_; lean_object* v___x_4682_; 
v___f_4681_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4681_, 0, v_k_4672_);
lean_closure_set(v___f_4681_, 1, v_runInBase_4675_);
v___x_4682_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4673_, v_type_4674_, v___f_4681_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4683_, lean_object* v_perm_4684_, lean_object* v_type_4685_, lean_object* v_runInBase_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4683_, v_perm_4684_, v_type_4685_, v_runInBase_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4693_, lean_object* v_inst_4694_, lean_object* v_perm_4695_, lean_object* v_type_4696_, lean_object* v_k_4697_){
_start:
{
lean_object* v_toBind_4698_; lean_object* v_liftWith_4699_; lean_object* v_restoreM_4700_; lean_object* v___f_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v_toBind_4698_ = lean_ctor_get(v_inst_4694_, 1);
lean_inc(v_toBind_4698_);
lean_dec_ref(v_inst_4694_);
v_liftWith_4699_ = lean_ctor_get(v_inst_4693_, 0);
lean_inc(v_liftWith_4699_);
v_restoreM_4700_ = lean_ctor_get(v_inst_4693_, 1);
lean_inc(v_restoreM_4700_);
lean_dec_ref(v_inst_4693_);
v___f_4701_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4701_, 0, v_k_4697_);
lean_closure_set(v___f_4701_, 1, v_perm_4695_);
lean_closure_set(v___f_4701_, 2, v_type_4696_);
v___x_4702_ = lean_apply_2(v_liftWith_4699_, lean_box(0), v___f_4701_);
v___x_4703_ = lean_apply_1(v_restoreM_4700_, lean_box(0));
v___x_4704_ = lean_apply_4(v_toBind_4698_, lean_box(0), lean_box(0), v___x_4702_, v___x_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4705_, lean_object* v_00_u03b1_4706_, lean_object* v_inst_4707_, lean_object* v_inst_4708_, lean_object* v_perm_4709_, lean_object* v_type_4710_, lean_object* v_k_4711_){
_start:
{
lean_object* v___x_4712_; 
v___x_4712_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4707_, v_inst_4708_, v_perm_4709_, v_type_4710_, v_k_4711_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v___f_4719_; lean_object* v___x_603__overap_4720_; lean_object* v___x_4721_; 
v___f_4719_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_603__overap_4720_ = lean_panic_fn_borrowed(v___f_4719_, v_msg_4713_);
lean_inc(v___y_4717_);
lean_inc_ref(v___y_4716_);
lean_inc(v___y_4715_);
lean_inc_ref(v___y_4714_);
v___x_4721_ = lean_apply_5(v___x_603__overap_4720_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, lean_box(0));
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
return v_res_4728_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4731_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4732_ = lean_unsigned_to_nat(10u);
v___x_4733_ = lean_unsigned_to_nat(353u);
v___x_4734_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4736_ = l_mkPanicMessageWithDecl(v___x_4735_, v___x_4734_, v___x_4733_, v___x_4732_, v___x_4731_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4737_, lean_object* v_xs_4738_, lean_object* v_tail_4739_, lean_object* v_ys_4740_, lean_object* v_type_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4737_, v_xs_4738_, v_tail_4739_, v_ys_4740_, v_type_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec_ref(v_ys_4740_);
lean_dec(v___x_4737_);
return v_res_4747_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4748_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4749_ = lean_unsigned_to_nat(8u);
v___x_4750_ = lean_unsigned_to_nat(349u);
v___x_4751_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4752_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4753_ = l_mkPanicMessageWithDecl(v___x_4752_, v___x_4751_, v___x_4750_, v___x_4749_, v___x_4748_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4754_, lean_object* v_x_4755_, lean_object* v_x_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
if (lean_obj_tag(v_x_4755_) == 0)
{
lean_object* v___x_4762_; 
lean_dec_ref(v_xs_4754_);
v___x_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4762_, 0, v_x_4756_);
return v___x_4762_;
}
else
{
lean_object* v_head_4763_; 
v_head_4763_ = lean_ctor_get(v_x_4755_, 0);
if (lean_obj_tag(v_head_4763_) == 0)
{
lean_object* v_tail_4764_; lean_object* v___x_4765_; lean_object* v___f_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; lean_object* v___x_4769_; 
v_tail_4764_ = lean_ctor_get(v_x_4755_, 1);
lean_inc(v_tail_4764_);
lean_dec_ref_known(v_x_4755_, 2);
v___x_4765_ = lean_unsigned_to_nat(1u);
v___f_4766_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4766_, 0, v___x_4765_);
lean_closure_set(v___f_4766_, 1, v_xs_4754_);
lean_closure_set(v___f_4766_, 2, v_tail_4764_);
v___x_4767_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4768_ = 0;
v___x_4769_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4756_, v___x_4767_, v___f_4766_, v___x_4768_, v___x_4768_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
return v___x_4769_;
}
else
{
lean_object* v_tail_4770_; lean_object* v_val_4771_; lean_object* v___x_4772_; uint8_t v___x_4773_; 
lean_inc_ref(v_head_4763_);
v_tail_4770_ = lean_ctor_get(v_x_4755_, 1);
lean_inc(v_tail_4770_);
lean_dec_ref_known(v_x_4755_, 2);
v_val_4771_ = lean_ctor_get(v_head_4763_, 0);
lean_inc(v_val_4771_);
lean_dec_ref_known(v_head_4763_, 1);
v___x_4772_ = lean_array_get_size(v_xs_4754_);
v___x_4773_ = lean_nat_dec_lt(v_val_4771_, v___x_4772_);
if (v___x_4773_ == 0)
{
lean_object* v___x_4774_; lean_object* v___x_4775_; 
lean_dec(v_val_4771_);
lean_dec(v_tail_4770_);
lean_dec_ref(v_x_4756_);
lean_dec_ref(v_xs_4754_);
v___x_4774_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4775_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4774_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
return v___x_4775_;
}
else
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4776_ = l_Lean_instInhabitedExpr;
v___x_4777_ = lean_array_get_borrowed(v___x_4776_, v_xs_4754_, v_val_4771_);
lean_dec(v_val_4771_);
v___x_4778_ = lean_unsigned_to_nat(1u);
v___x_4779_ = lean_mk_empty_array_with_capacity(v___x_4778_);
lean_inc(v___x_4777_);
v___x_4780_ = lean_array_push(v___x_4779_, v___x_4777_);
v___x_4781_ = l_Lean_Meta_instantiateForall(v_x_4756_, v___x_4780_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec_ref(v___x_4780_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_a_4782_);
lean_dec_ref_known(v___x_4781_, 1);
v_x_4755_ = v_tail_4770_;
v_x_4756_ = v_a_4782_;
goto _start;
}
else
{
lean_dec(v_tail_4770_);
lean_dec_ref(v_xs_4754_);
return v___x_4781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4784_, lean_object* v_xs_4785_, lean_object* v_tail_4786_, lean_object* v_ys_4787_, lean_object* v_type_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___x_4794_; uint8_t v___x_4795_; 
v___x_4794_ = lean_array_get_size(v_ys_4787_);
v___x_4795_ = lean_nat_dec_eq(v___x_4794_, v___x_4784_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
lean_dec_ref(v_type_4788_);
lean_dec(v_tail_4786_);
lean_dec_ref(v_xs_4785_);
v___x_4796_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4797_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4796_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
return v___x_4797_;
}
else
{
lean_object* v___x_4798_; 
v___x_4798_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4785_, v_tail_4786_, v_type_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; uint8_t v___x_4800_; uint8_t v___x_4801_; lean_object* v___x_4802_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___x_4798_, 1);
v___x_4800_ = 0;
v___x_4801_ = 1;
v___x_4802_ = l_Lean_Meta_mkForallFVars(v_ys_4787_, v_a_4799_, v___x_4800_, v___x_4795_, v___x_4795_, v___x_4801_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
return v___x_4802_;
}
else
{
return v___x_4798_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4803_, lean_object* v_x_4804_, lean_object* v_x_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4803_, v_x_4804_, v_x_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
return v_res_4811_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4814_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4815_ = lean_unsigned_to_nat(2u);
v___x_4816_ = lean_unsigned_to_nat(343u);
v___x_4817_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4818_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4819_ = l_mkPanicMessageWithDecl(v___x_4818_, v___x_4817_, v___x_4816_, v___x_4815_, v___x_4814_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4820_, lean_object* v_type_u2080_4821_, lean_object* v_xs_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4828_ = lean_array_get_size(v_xs_4822_);
v___x_4829_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4820_);
v___x_4830_ = lean_nat_dec_eq(v___x_4828_, v___x_4829_);
lean_dec(v___x_4829_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
lean_dec_ref(v_xs_4822_);
lean_dec_ref(v_type_u2080_4821_);
lean_dec_ref(v_perm_4820_);
v___x_4831_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4832_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4831_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_);
return v___x_4832_;
}
else
{
lean_object* v_mask_4833_; lean_object* v___x_4834_; 
v_mask_4833_ = lean_array_to_list(v_perm_4820_);
v___x_4834_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4822_, v_mask_4833_, v_type_u2080_4821_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_);
return v___x_4834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4835_, lean_object* v_type_u2080_4836_, lean_object* v_xs_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4835_, v_type_u2080_4836_, v_xs_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4844_, lean_object* v_maxFVars_4845_, lean_object* v_k_4846_, uint8_t v_cleanupAnnotations_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v___f_4853_; uint8_t v___x_4854_; uint8_t v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___f_4853_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4853_, 0, v_k_4846_);
v___x_4854_ = 1;
v___x_4855_ = 0;
v___x_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4856_, 0, v_maxFVars_4845_);
v___x_4857_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4844_, v___x_4854_, v___x_4855_, v___x_4854_, v___x_4855_, v___x_4856_, v___f_4853_, v_cleanupAnnotations_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
lean_dec_ref_known(v___x_4856_, 1);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4865_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4860_ = v___x_4857_;
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4857_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4863_; 
if (v_isShared_4861_ == 0)
{
v___x_4863_ = v___x_4860_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
else
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4873_; 
v_a_4866_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4868_ = v___x_4857_;
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4857_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4871_; 
if (v_isShared_4869_ == 0)
{
v___x_4871_ = v___x_4868_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4874_, lean_object* v_maxFVars_4875_, lean_object* v_k_4876_, lean_object* v_cleanupAnnotations_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4883_; lean_object* v_res_4884_; 
v_cleanupAnnotations_boxed_4883_ = lean_unbox(v_cleanupAnnotations_4877_);
v_res_4884_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4874_, v_maxFVars_4875_, v_k_4876_, v_cleanupAnnotations_boxed_4883_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
lean_dec(v___y_4879_);
lean_dec_ref(v___y_4878_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4885_, lean_object* v_e_4886_, lean_object* v_maxFVars_4887_, lean_object* v_k_4888_, uint8_t v_cleanupAnnotations_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4886_, v_maxFVars_4887_, v_k_4888_, v_cleanupAnnotations_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4896_, lean_object* v_e_4897_, lean_object* v_maxFVars_4898_, lean_object* v_k_4899_, lean_object* v_cleanupAnnotations_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4906_; lean_object* v_res_4907_; 
v_cleanupAnnotations_boxed_4906_ = lean_unbox(v_cleanupAnnotations_4900_);
v_res_4907_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4896_, v_e_4897_, v_maxFVars_4898_, v_k_4899_, v_cleanupAnnotations_boxed_4906_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_);
lean_dec(v___y_4904_);
lean_dec_ref(v___y_4903_);
lean_dec(v___y_4902_);
lean_dec_ref(v___y_4901_);
return v_res_4907_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4908_){
_start:
{
if (lean_obj_tag(v_x_4908_) == 0)
{
uint8_t v___x_4909_; 
v___x_4909_ = 1;
return v___x_4909_;
}
else
{
lean_object* v_head_4910_; 
v_head_4910_ = lean_ctor_get(v_x_4908_, 0);
if (lean_obj_tag(v_head_4910_) == 0)
{
lean_object* v_tail_4911_; 
v_tail_4911_ = lean_ctor_get(v_x_4908_, 1);
v_x_4908_ = v_tail_4911_;
goto _start;
}
else
{
uint8_t v___x_4913_; 
v___x_4913_ = 0;
return v___x_4913_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4914_){
_start:
{
uint8_t v_res_4915_; lean_object* v_r_4916_; 
v_res_4915_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4914_);
lean_dec(v_x_4914_);
v_r_4916_ = lean_box(v_res_4915_);
return v_r_4916_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
v___x_4919_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4920_ = lean_unsigned_to_nat(12u);
v___x_4921_ = lean_unsigned_to_nat(376u);
v___x_4922_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4923_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4924_ = l_mkPanicMessageWithDecl(v___x_4923_, v___x_4922_, v___x_4921_, v___x_4920_, v___x_4919_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4925_, lean_object* v_xs_4926_, lean_object* v_tail_4927_, lean_object* v___x_4928_, lean_object* v___x_4929_, lean_object* v_ys_4930_, lean_object* v_value_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
uint8_t v___x_1310__boxed_4937_; uint8_t v___x_1311__boxed_4938_; lean_object* v_res_4939_; 
v___x_1310__boxed_4937_ = lean_unbox(v___x_4928_);
v___x_1311__boxed_4938_ = lean_unbox(v___x_4929_);
v_res_4939_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4925_, v_xs_4926_, v_tail_4927_, v___x_1310__boxed_4937_, v___x_1311__boxed_4938_, v_ys_4930_, v_value_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec_ref(v_ys_4930_);
lean_dec(v___x_4925_);
return v_res_4939_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4940_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4941_ = lean_unsigned_to_nat(8u);
v___x_4942_ = lean_unsigned_to_nat(368u);
v___x_4943_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4944_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4945_ = l_mkPanicMessageWithDecl(v___x_4944_, v___x_4943_, v___x_4942_, v___x_4941_, v___x_4940_);
return v___x_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4946_, lean_object* v_x_4947_, lean_object* v_x_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_){
_start:
{
if (lean_obj_tag(v_x_4947_) == 0)
{
lean_object* v___x_4954_; 
lean_dec_ref(v_xs_4946_);
v___x_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4954_, 0, v_x_4948_);
return v___x_4954_;
}
else
{
lean_object* v_head_4955_; 
v_head_4955_ = lean_ctor_get(v_x_4947_, 0);
if (lean_obj_tag(v_head_4955_) == 0)
{
lean_object* v_tail_4956_; uint8_t v___x_4957_; 
v_tail_4956_ = lean_ctor_get(v_x_4947_, 1);
lean_inc(v_tail_4956_);
lean_dec_ref_known(v_x_4947_, 2);
v___x_4957_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4956_);
if (v___x_4957_ == 0)
{
uint8_t v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___f_4962_; lean_object* v___x_4963_; 
v___x_4958_ = 1;
v___x_4959_ = lean_unsigned_to_nat(1u);
v___x_4960_ = lean_box(v___x_4957_);
v___x_4961_ = lean_box(v___x_4958_);
v___f_4962_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4962_, 0, v___x_4959_);
lean_closure_set(v___f_4962_, 1, v_xs_4946_);
lean_closure_set(v___f_4962_, 2, v_tail_4956_);
lean_closure_set(v___f_4962_, 3, v___x_4960_);
lean_closure_set(v___f_4962_, 4, v___x_4961_);
v___x_4963_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4948_, v___x_4959_, v___f_4962_, v___x_4957_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
return v___x_4963_;
}
else
{
lean_object* v___x_4964_; 
lean_dec(v_tail_4956_);
lean_dec_ref(v_xs_4946_);
v___x_4964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4964_, 0, v_x_4948_);
return v___x_4964_;
}
}
else
{
lean_object* v_tail_4965_; lean_object* v_val_4966_; lean_object* v___x_4967_; uint8_t v___x_4968_; 
lean_inc_ref(v_head_4955_);
v_tail_4965_ = lean_ctor_get(v_x_4947_, 1);
lean_inc(v_tail_4965_);
lean_dec_ref_known(v_x_4947_, 2);
v_val_4966_ = lean_ctor_get(v_head_4955_, 0);
lean_inc(v_val_4966_);
lean_dec_ref_known(v_head_4955_, 1);
v___x_4967_ = lean_array_get_size(v_xs_4946_);
v___x_4968_ = lean_nat_dec_lt(v_val_4966_, v___x_4967_);
if (v___x_4968_ == 0)
{
lean_object* v___x_4969_; lean_object* v___x_4970_; 
lean_dec(v_val_4966_);
lean_dec(v_tail_4965_);
lean_dec_ref(v_x_4948_);
lean_dec_ref(v_xs_4946_);
v___x_4969_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4970_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4969_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
return v___x_4970_;
}
else
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4971_ = l_Lean_instInhabitedExpr;
v___x_4972_ = lean_array_get_borrowed(v___x_4971_, v_xs_4946_, v_val_4966_);
lean_dec(v_val_4966_);
v___x_4973_ = lean_unsigned_to_nat(1u);
v___x_4974_ = lean_mk_empty_array_with_capacity(v___x_4973_);
lean_inc(v___x_4972_);
v___x_4975_ = lean_array_push(v___x_4974_, v___x_4972_);
v___x_4976_ = l_Lean_Meta_instantiateLambda(v_x_4948_, v___x_4975_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
lean_dec_ref(v___x_4975_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4977_; 
v_a_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4976_, 1);
v_x_4947_ = v_tail_4965_;
v_x_4948_ = v_a_4977_;
goto _start;
}
else
{
lean_dec(v_tail_4965_);
lean_dec_ref(v_xs_4946_);
return v___x_4976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4979_, lean_object* v_xs_4980_, lean_object* v_tail_4981_, uint8_t v___x_4982_, uint8_t v___x_4983_, lean_object* v_ys_4984_, lean_object* v_value_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v___x_4991_; uint8_t v___x_4992_; 
v___x_4991_ = lean_array_get_size(v_ys_4984_);
v___x_4992_ = lean_nat_dec_eq(v___x_4991_, v___x_4979_);
if (v___x_4992_ == 0)
{
lean_object* v___x_4993_; lean_object* v___x_4994_; 
lean_dec_ref(v_value_4985_);
lean_dec(v_tail_4981_);
lean_dec_ref(v_xs_4980_);
v___x_4993_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4994_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4993_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
return v___x_4994_;
}
else
{
lean_object* v___x_4995_; 
v___x_4995_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4980_, v_tail_4981_, v_value_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; uint8_t v___x_4997_; lean_object* v___x_4998_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref_known(v___x_4995_, 1);
v___x_4997_ = 1;
v___x_4998_ = l_Lean_Meta_mkLambdaFVars(v_ys_4984_, v_a_4996_, v___x_4982_, v___x_4983_, v___x_4982_, v___x_4983_, v___x_4997_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
return v___x_4998_;
}
else
{
return v___x_4995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4999_, lean_object* v_x_5000_, lean_object* v_x_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4999_, v_x_5000_, v_x_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
lean_dec(v_a_5003_);
lean_dec_ref(v_a_5002_);
return v_res_5007_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5009_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5010_ = lean_unsigned_to_nat(2u);
v___x_5011_ = lean_unsigned_to_nat(362u);
v___x_5012_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5013_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5014_ = l_mkPanicMessageWithDecl(v___x_5013_, v___x_5012_, v___x_5011_, v___x_5010_, v___x_5009_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5015_, lean_object* v_value_u2080_5016_, lean_object* v_xs_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; uint8_t v___x_5025_; 
v___x_5023_ = lean_array_get_size(v_xs_5017_);
v___x_5024_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5015_);
v___x_5025_ = lean_nat_dec_eq(v___x_5023_, v___x_5024_);
lean_dec(v___x_5024_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; lean_object* v___x_5027_; 
lean_dec_ref(v_xs_5017_);
lean_dec_ref(v_value_u2080_5016_);
lean_dec_ref(v_perm_5015_);
v___x_5026_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5027_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5026_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_);
return v___x_5027_;
}
else
{
lean_object* v_mask_5028_; lean_object* v___x_5029_; 
v_mask_5028_ = lean_array_to_list(v_perm_5015_);
v___x_5029_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5017_, v_mask_5028_, v_value_u2080_5016_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_);
return v___x_5029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5030_, lean_object* v_value_u2080_5031_, lean_object* v_xs_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5030_, v_value_u2080_5031_, v_xs_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_);
lean_dec(v_a_5036_);
lean_dec_ref(v_a_5035_);
lean_dec(v_a_5034_);
lean_dec_ref(v_a_5033_);
return v_res_5038_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5046_; 
v___x_5046_ = l_Array_instInhabited(lean_box(0));
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5047_){
_start:
{
lean_object* v___f_5048_; lean_object* v___f_5049_; lean_object* v___f_5050_; lean_object* v___f_5051_; lean_object* v___f_5052_; lean_object* v___f_5053_; lean_object* v___f_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___f_5048_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5049_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5050_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5051_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5052_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5053_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5054_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5055_, 0, v___f_5048_);
lean_ctor_set(v___x_5055_, 1, v___f_5049_);
v___x_5056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5055_);
lean_ctor_set(v___x_5056_, 1, v___f_5050_);
lean_ctor_set(v___x_5056_, 2, v___f_5051_);
lean_ctor_set(v___x_5056_, 3, v___f_5052_);
lean_ctor_set(v___x_5056_, 4, v___f_5053_);
v___x_5057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
lean_ctor_set(v___x_5057_, 1, v___f_5054_);
v___x_5058_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5059_ = l_instInhabitedOfMonad___redArg(v___x_5057_, v___x_5058_);
v___x_5060_ = lean_panic_fn_borrowed(v___x_5059_, v_msg_5047_);
lean_dec(v___x_5059_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5061_, lean_object* v_msg_5062_){
_start:
{
lean_object* v___x_5063_; 
v___x_5063_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5062_);
return v___x_5063_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5066_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5067_ = lean_unsigned_to_nat(8u);
v___x_5068_ = lean_unsigned_to_nat(394u);
v___x_5069_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5070_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5071_ = l_mkPanicMessageWithDecl(v___x_5070_, v___x_5069_, v___x_5068_, v___x_5067_, v___x_5066_);
return v___x_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5072_, lean_object* v_x_5073_){
_start:
{
if (lean_obj_tag(v_x_5072_) == 0)
{
return v_x_5073_;
}
else
{
lean_object* v_head_5074_; lean_object* v_fst_5075_; 
v_head_5074_ = lean_ctor_get(v_x_5072_, 0);
v_fst_5075_ = lean_ctor_get(v_head_5074_, 0);
if (lean_obj_tag(v_fst_5075_) == 0)
{
lean_object* v_tail_5076_; 
v_tail_5076_ = lean_ctor_get(v_x_5072_, 1);
lean_inc(v_tail_5076_);
lean_dec_ref_known(v_x_5072_, 2);
v_x_5072_ = v_tail_5076_;
goto _start;
}
else
{
lean_object* v_tail_5078_; lean_object* v_snd_5079_; lean_object* v_val_5080_; lean_object* v___x_5081_; uint8_t v___x_5082_; 
lean_inc_ref(v_fst_5075_);
lean_inc(v_head_5074_);
v_tail_5078_ = lean_ctor_get(v_x_5072_, 1);
lean_inc(v_tail_5078_);
lean_dec_ref_known(v_x_5072_, 2);
v_snd_5079_ = lean_ctor_get(v_head_5074_, 1);
lean_inc(v_snd_5079_);
lean_dec(v_head_5074_);
v_val_5080_ = lean_ctor_get(v_fst_5075_, 0);
lean_inc(v_val_5080_);
lean_dec_ref_known(v_fst_5075_, 1);
v___x_5081_ = lean_array_get_size(v_x_5073_);
v___x_5082_ = lean_nat_dec_lt(v_val_5080_, v___x_5081_);
if (v___x_5082_ == 0)
{
lean_object* v___x_5083_; lean_object* v___x_5084_; 
lean_dec(v_val_5080_);
lean_dec(v_snd_5079_);
lean_dec(v_tail_5078_);
lean_dec_ref(v_x_5073_);
v___x_5083_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5084_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5083_);
return v___x_5084_;
}
else
{
lean_object* v___x_5085_; 
v___x_5085_ = lean_array_set(v_x_5073_, v_val_5080_, v_snd_5079_);
lean_dec(v_val_5080_);
v_x_5072_ = v_tail_5078_;
v_x_5073_ = v___x_5085_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5087_, lean_object* v_x_5088_, lean_object* v_x_5089_){
_start:
{
lean_object* v___x_5090_; 
v___x_5090_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5088_, v_x_5089_);
return v___x_5090_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5093_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5094_ = lean_unsigned_to_nat(2u);
v___x_5095_ = lean_unsigned_to_nat(384u);
v___x_5096_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5097_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5098_ = l_mkPanicMessageWithDecl(v___x_5097_, v___x_5096_, v___x_5095_, v___x_5094_, v___x_5093_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5101_, lean_object* v_xs_5102_){
_start:
{
lean_object* v___x_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; 
v___x_5103_ = lean_array_get_size(v_xs_5102_);
v___x_5104_ = lean_array_get_size(v_perm_5101_);
v___x_5105_ = lean_nat_dec_eq(v___x_5103_, v___x_5104_);
if (v___x_5105_ == 0)
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5107_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5106_);
return v___x_5107_;
}
else
{
lean_object* v___x_5108_; uint8_t v___x_5109_; 
v___x_5108_ = lean_unsigned_to_nat(0u);
v___x_5109_ = lean_nat_dec_eq(v___x_5103_, v___x_5108_);
if (v___x_5109_ == 0)
{
lean_object* v_dummy_5110_; lean_object* v___x_5111_; lean_object* v_ys_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
v_dummy_5110_ = lean_array_fget_borrowed(v_xs_5102_, v___x_5108_);
v___x_5111_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5101_);
lean_inc(v_dummy_5110_);
v_ys_5112_ = lean_mk_array(v___x_5111_, v_dummy_5110_);
v___x_5113_ = l_Array_zip___redArg(v_perm_5101_, v_xs_5102_);
v___x_5114_ = lean_array_to_list(v___x_5113_);
v___x_5115_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5114_, v_ys_5112_);
return v___x_5115_;
}
else
{
lean_object* v___x_5116_; 
v___x_5116_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5117_, lean_object* v_xs_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5117_, v_xs_5118_);
lean_dec_ref(v_xs_5118_);
lean_dec_ref(v_perm_5117_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5120_, lean_object* v_perm_5121_, lean_object* v_xs_5122_){
_start:
{
lean_object* v___x_5123_; 
v___x_5123_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5121_, v_xs_5122_);
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5124_, lean_object* v_perm_5125_, lean_object* v_xs_5126_){
_start:
{
lean_object* v_res_5127_; 
v_res_5127_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5124_, v_perm_5125_, v_xs_5126_);
lean_dec_ref(v_xs_5126_);
lean_dec_ref(v_perm_5125_);
return v_res_5127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5128_, lean_object* v_upperBound_5129_, lean_object* v_perm_5130_, lean_object* v_a_5131_, lean_object* v_b_5132_){
_start:
{
lean_object* v_a_5134_; uint8_t v___x_5141_; 
v___x_5141_ = lean_nat_dec_lt(v_a_5131_, v_upperBound_5129_);
if (v___x_5141_ == 0)
{
lean_dec(v_a_5131_);
return v_b_5132_;
}
else
{
lean_object* v___x_5142_; uint8_t v___x_5143_; 
v___x_5142_ = lean_array_get_size(v_perm_5130_);
v___x_5143_ = lean_nat_dec_lt(v_a_5131_, v___x_5142_);
if (v___x_5143_ == 0)
{
goto v___jp_5138_;
}
else
{
lean_object* v___x_5144_; 
v___x_5144_ = lean_array_fget_borrowed(v_perm_5130_, v_a_5131_);
if (lean_obj_tag(v___x_5144_) == 0)
{
goto v___jp_5138_;
}
else
{
v_a_5134_ = v_b_5132_;
goto v___jp_5133_;
}
}
}
v___jp_5133_:
{
lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5135_ = lean_unsigned_to_nat(1u);
v___x_5136_ = lean_nat_add(v_a_5131_, v___x_5135_);
lean_dec(v_a_5131_);
v_a_5131_ = v___x_5136_;
v_b_5132_ = v_a_5134_;
goto _start;
}
v___jp_5138_:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5139_ = lean_array_fget_borrowed(v_xs_5128_, v_a_5131_);
lean_inc(v___x_5139_);
v___x_5140_ = lean_array_push(v_b_5132_, v___x_5139_);
v_a_5134_ = v___x_5140_;
goto v___jp_5133_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5145_, lean_object* v_upperBound_5146_, lean_object* v_perm_5147_, lean_object* v_a_5148_, lean_object* v_b_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5145_, v_upperBound_5146_, v_perm_5147_, v_a_5148_, v_b_5149_);
lean_dec_ref(v_perm_5147_);
lean_dec(v_upperBound_5146_);
lean_dec_ref(v_xs_5145_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5151_, lean_object* v_xs_5152_){
_start:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v_ys_5155_; lean_object* v___x_5156_; 
v___x_5153_ = lean_array_get_size(v_xs_5152_);
v___x_5154_ = lean_unsigned_to_nat(0u);
v_ys_5155_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5152_, v___x_5153_, v_perm_5151_, v___x_5154_, v_ys_5155_);
return v___x_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5157_, lean_object* v_xs_5158_){
_start:
{
lean_object* v_res_5159_; 
v_res_5159_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5157_, v_xs_5158_);
lean_dec_ref(v_xs_5158_);
lean_dec_ref(v_perm_5157_);
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5160_, lean_object* v_perm_5161_, lean_object* v_xs_5162_){
_start:
{
lean_object* v___x_5163_; 
v___x_5163_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5161_, v_xs_5162_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5164_, lean_object* v_perm_5165_, lean_object* v_xs_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5164_, v_perm_5165_, v_xs_5166_);
lean_dec_ref(v_xs_5166_);
lean_dec_ref(v_perm_5165_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5168_, lean_object* v_xs_5169_, lean_object* v_upperBound_5170_, lean_object* v_perm_5171_, lean_object* v_inst_5172_, lean_object* v_R_5173_, lean_object* v_a_5174_, lean_object* v_b_5175_, lean_object* v_c_5176_){
_start:
{
lean_object* v___x_5177_; 
v___x_5177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5169_, v_upperBound_5170_, v_perm_5171_, v_a_5174_, v_b_5175_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5178_, lean_object* v_xs_5179_, lean_object* v_upperBound_5180_, lean_object* v_perm_5181_, lean_object* v_inst_5182_, lean_object* v_R_5183_, lean_object* v_a_5184_, lean_object* v_b_5185_, lean_object* v_c_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5178_, v_xs_5179_, v_upperBound_5180_, v_perm_5181_, v_inst_5182_, v_R_5183_, v_a_5184_, v_b_5185_, v_c_5186_);
lean_dec_ref(v_perm_5181_);
lean_dec(v_upperBound_5180_);
lean_dec_ref(v_xs_5179_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object* v_msg_5188_){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; 
v___x_5189_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5190_ = lean_panic_fn_borrowed(v___x_5189_, v_msg_5188_);
return v___x_5190_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_00_u03b1_5191_, lean_object* v_msg_5192_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v_msg_5192_);
return v___x_5193_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_as_5194_, size_t v_i_5195_, size_t v_stop_5196_){
_start:
{
uint8_t v___x_5197_; 
v___x_5197_ = lean_usize_dec_eq(v_i_5195_, v_stop_5196_);
if (v___x_5197_ == 0)
{
uint8_t v___x_5198_; lean_object* v___x_5199_; 
v___x_5198_ = 1;
v___x_5199_ = lean_array_uget_borrowed(v_as_5194_, v_i_5195_);
if (lean_obj_tag(v___x_5199_) == 0)
{
if (v___x_5197_ == 0)
{
size_t v___x_5200_; size_t v___x_5201_; 
v___x_5200_ = ((size_t)1ULL);
v___x_5201_ = lean_usize_add(v_i_5195_, v___x_5200_);
v_i_5195_ = v___x_5201_;
goto _start;
}
else
{
return v___x_5198_;
}
}
else
{
return v___x_5198_;
}
}
else
{
uint8_t v___x_5203_; 
v___x_5203_ = 0;
return v___x_5203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object* v_as_5204_, lean_object* v_i_5205_, lean_object* v_stop_5206_){
_start:
{
size_t v_i_boxed_5207_; size_t v_stop_boxed_5208_; uint8_t v_res_5209_; lean_object* v_r_5210_; 
v_i_boxed_5207_ = lean_unbox_usize(v_i_5205_);
lean_dec(v_i_5205_);
v_stop_boxed_5208_ = lean_unbox_usize(v_stop_5206_);
lean_dec(v_stop_5206_);
v_res_5209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v_as_5204_, v_i_boxed_5207_, v_stop_boxed_5208_);
lean_dec_ref(v_as_5204_);
v_r_5210_ = lean_box(v_res_5209_);
return v_r_5210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
v___x_5213_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5214_ = lean_unsigned_to_nat(12u);
v___x_5215_ = lean_unsigned_to_nat(433u);
v___x_5216_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5217_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5218_ = l_mkPanicMessageWithDecl(v___x_5217_, v___x_5216_, v___x_5215_, v___x_5214_, v___x_5213_);
return v___x_5218_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5220_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5221_ = lean_unsigned_to_nat(10u);
v___x_5222_ = lean_unsigned_to_nat(425u);
v___x_5223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5224_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5225_ = l_mkPanicMessageWithDecl(v___x_5224_, v___x_5223_, v___x_5222_, v___x_5221_, v___x_5220_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5226_, lean_object* v_fixedArgs_5227_, lean_object* v_varyingArgs_5228_, lean_object* v_i_5229_, lean_object* v_j_5230_, lean_object* v_xs_5231_){
_start:
{
lean_object* v_lower_5233_; lean_object* v_upper_5234_; lean_object* v___y_5239_; lean_object* v___y_5240_; lean_object* v___y_5241_; lean_object* v_lower_5249_; lean_object* v_upper_5250_; lean_object* v___x_5258_; uint8_t v___x_5259_; 
v___x_5258_ = lean_array_get_size(v_perm_5226_);
v___x_5259_ = lean_nat_dec_lt(v_i_5229_, v___x_5258_);
if (v___x_5259_ == 0)
{
lean_object* v___x_5260_; lean_object* v___x_5261_; uint8_t v___x_5262_; 
lean_dec(v_i_5229_);
lean_dec_ref(v_perm_5226_);
v___x_5260_ = lean_unsigned_to_nat(0u);
v___x_5261_ = lean_array_get_size(v_varyingArgs_5228_);
v___x_5262_ = lean_nat_dec_le(v_j_5230_, v___x_5260_);
if (v___x_5262_ == 0)
{
v_lower_5233_ = v_j_5230_;
v_upper_5234_ = v___x_5261_;
goto v___jp_5232_;
}
else
{
lean_dec(v_j_5230_);
v_lower_5233_ = v___x_5260_;
v_upper_5234_ = v___x_5261_;
goto v___jp_5232_;
}
}
else
{
lean_object* v___x_5263_; 
v___x_5263_ = lean_array_fget_borrowed(v_perm_5226_, v_i_5229_);
if (lean_obj_tag(v___x_5263_) == 1)
{
lean_object* v_val_5264_; lean_object* v___x_5265_; uint8_t v___x_5266_; 
v_val_5264_ = lean_ctor_get(v___x_5263_, 0);
v___x_5265_ = lean_array_get_size(v_fixedArgs_5227_);
v___x_5266_ = lean_nat_dec_lt(v_val_5264_, v___x_5265_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; lean_object* v___x_5268_; 
lean_dec_ref(v_xs_5231_);
lean_dec(v_j_5230_);
lean_dec(v_i_5229_);
lean_dec_ref(v_varyingArgs_5228_);
lean_dec_ref(v_perm_5226_);
v___x_5267_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5268_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5267_);
return v___x_5268_;
}
else
{
lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; 
v___x_5269_ = lean_unsigned_to_nat(1u);
v___x_5270_ = lean_nat_add(v_i_5229_, v___x_5269_);
lean_dec(v_i_5229_);
v___x_5271_ = lean_array_fget_borrowed(v_fixedArgs_5227_, v_val_5264_);
lean_inc(v___x_5271_);
v___x_5272_ = lean_array_push(v_xs_5231_, v___x_5271_);
v_i_5229_ = v___x_5270_;
v_xs_5231_ = v___x_5272_;
goto _start;
}
}
else
{
lean_object* v___x_5274_; uint8_t v___x_5275_; 
v___x_5274_ = lean_array_get_size(v_varyingArgs_5228_);
v___x_5275_ = lean_nat_dec_lt(v_j_5230_, v___x_5274_);
if (v___x_5275_ == 0)
{
lean_object* v___x_5276_; uint8_t v___x_5277_; 
lean_dec(v_j_5230_);
lean_dec_ref(v_varyingArgs_5228_);
v___x_5276_ = lean_unsigned_to_nat(0u);
v___x_5277_ = lean_nat_dec_le(v_i_5229_, v___x_5276_);
if (v___x_5277_ == 0)
{
v_lower_5249_ = v_i_5229_;
v_upper_5250_ = v___x_5258_;
goto v___jp_5248_;
}
else
{
lean_dec(v_i_5229_);
v_lower_5249_ = v___x_5276_;
v_upper_5250_ = v___x_5258_;
goto v___jp_5248_;
}
}
else
{
lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5278_ = lean_unsigned_to_nat(1u);
v___x_5279_ = lean_nat_add(v_i_5229_, v___x_5278_);
lean_dec(v_i_5229_);
v___x_5280_ = lean_nat_add(v_j_5230_, v___x_5278_);
v___x_5281_ = lean_array_fget_borrowed(v_varyingArgs_5228_, v_j_5230_);
lean_dec(v_j_5230_);
lean_inc(v___x_5281_);
v___x_5282_ = lean_array_push(v_xs_5231_, v___x_5281_);
v_i_5229_ = v___x_5279_;
v_j_5230_ = v___x_5280_;
v_xs_5231_ = v___x_5282_;
goto _start;
}
}
}
v___jp_5232_:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
v___x_5235_ = l_Array_toSubarray___redArg(v_varyingArgs_5228_, v_lower_5233_, v_upper_5234_);
v___x_5236_ = l_Subarray_copy___redArg(v___x_5235_);
v___x_5237_ = l_Array_append___redArg(v_xs_5231_, v___x_5236_);
lean_dec_ref(v___x_5236_);
return v___x_5237_;
}
v___jp_5238_:
{
uint8_t v___x_5242_; 
v___x_5242_ = lean_nat_dec_lt(v___y_5239_, v___y_5241_);
if (v___x_5242_ == 0)
{
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec(v___y_5239_);
return v_xs_5231_;
}
else
{
size_t v___x_5243_; size_t v___x_5244_; uint8_t v___x_5245_; 
v___x_5243_ = lean_usize_of_nat(v___y_5239_);
lean_dec(v___y_5239_);
v___x_5244_ = lean_usize_of_nat(v___y_5241_);
lean_dec(v___y_5241_);
v___x_5245_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v___y_5240_, v___x_5243_, v___x_5244_);
lean_dec_ref(v___y_5240_);
if (v___x_5245_ == 0)
{
return v_xs_5231_;
}
else
{
lean_object* v___x_5246_; lean_object* v___x_5247_; 
lean_dec_ref(v_xs_5231_);
v___x_5246_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5247_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5246_);
return v___x_5247_;
}
}
}
v___jp_5248_:
{
lean_object* v___x_5251_; lean_object* v_array_5252_; lean_object* v_start_5253_; lean_object* v_stop_5254_; uint8_t v___x_5255_; 
v___x_5251_ = l_Array_toSubarray___redArg(v_perm_5226_, v_lower_5249_, v_upper_5250_);
v_array_5252_ = lean_ctor_get(v___x_5251_, 0);
lean_inc_ref(v_array_5252_);
v_start_5253_ = lean_ctor_get(v___x_5251_, 1);
lean_inc(v_start_5253_);
v_stop_5254_ = lean_ctor_get(v___x_5251_, 2);
lean_inc(v_stop_5254_);
lean_dec_ref(v___x_5251_);
v___x_5255_ = lean_nat_dec_lt(v_start_5253_, v_stop_5254_);
if (v___x_5255_ == 0)
{
lean_dec(v_stop_5254_);
lean_dec(v_start_5253_);
lean_dec_ref(v_array_5252_);
return v_xs_5231_;
}
else
{
lean_object* v___x_5256_; uint8_t v___x_5257_; 
v___x_5256_ = lean_array_get_size(v_array_5252_);
v___x_5257_ = lean_nat_dec_le(v_stop_5254_, v___x_5256_);
if (v___x_5257_ == 0)
{
lean_dec(v_stop_5254_);
v___y_5239_ = v_start_5253_;
v___y_5240_ = v_array_5252_;
v___y_5241_ = v___x_5256_;
goto v___jp_5238_;
}
else
{
v___y_5239_ = v_start_5253_;
v___y_5240_ = v_array_5252_;
v___y_5241_ = v_stop_5254_;
goto v___jp_5238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5284_, lean_object* v_fixedArgs_5285_, lean_object* v_varyingArgs_5286_, lean_object* v_i_5287_, lean_object* v_j_5288_, lean_object* v_xs_5289_){
_start:
{
lean_object* v_res_5290_; 
v_res_5290_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5284_, v_fixedArgs_5285_, v_varyingArgs_5286_, v_i_5287_, v_j_5288_, v_xs_5289_);
lean_dec_ref(v_fixedArgs_5285_);
return v_res_5290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5291_, lean_object* v_perm_5292_, lean_object* v_fixedArgs_5293_, lean_object* v_varyingArgs_5294_, lean_object* v_i_5295_, lean_object* v_j_5296_, lean_object* v_xs_5297_){
_start:
{
lean_object* v___x_5298_; 
v___x_5298_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5292_, v_fixedArgs_5293_, v_varyingArgs_5294_, v_i_5295_, v_j_5296_, v_xs_5297_);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5299_, lean_object* v_perm_5300_, lean_object* v_fixedArgs_5301_, lean_object* v_varyingArgs_5302_, lean_object* v_i_5303_, lean_object* v_j_5304_, lean_object* v_xs_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5299_, v_perm_5300_, v_fixedArgs_5301_, v_varyingArgs_5302_, v_i_5303_, v_j_5304_, v_xs_5305_);
lean_dec_ref(v_fixedArgs_5301_);
return v_res_5306_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5309_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5310_ = lean_unsigned_to_nat(2u);
v___x_5311_ = lean_unsigned_to_nat(416u);
v___x_5312_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5314_ = l_mkPanicMessageWithDecl(v___x_5313_, v___x_5312_, v___x_5311_, v___x_5310_, v___x_5309_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5315_, lean_object* v_fixedArgs_5316_, lean_object* v_varyingArgs_5317_){
_start:
{
lean_object* v___x_5318_; lean_object* v___x_5319_; uint8_t v___x_5320_; 
v___x_5318_ = lean_array_get_size(v_fixedArgs_5316_);
v___x_5319_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5315_);
v___x_5320_ = lean_nat_dec_eq(v___x_5318_, v___x_5319_);
lean_dec(v___x_5319_);
if (v___x_5320_ == 0)
{
lean_object* v___x_5321_; lean_object* v___x_5322_; 
lean_dec_ref(v_varyingArgs_5317_);
lean_dec_ref(v_perm_5315_);
v___x_5321_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5322_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5321_);
return v___x_5322_;
}
else
{
lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5323_ = lean_unsigned_to_nat(0u);
v___x_5324_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5325_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5315_, v_fixedArgs_5316_, v_varyingArgs_5317_, v___x_5323_, v___x_5323_, v___x_5324_);
return v___x_5325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5326_, lean_object* v_fixedArgs_5327_, lean_object* v_varyingArgs_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5326_, v_fixedArgs_5327_, v_varyingArgs_5328_);
lean_dec_ref(v_fixedArgs_5327_);
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5330_, lean_object* v_perm_5331_, lean_object* v_fixedArgs_5332_, lean_object* v_varyingArgs_5333_){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5331_, v_fixedArgs_5332_, v_varyingArgs_5333_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5335_, lean_object* v_perm_5336_, lean_object* v_fixedArgs_5337_, lean_object* v_varyingArgs_5338_){
_start:
{
lean_object* v_res_5339_; 
v_res_5339_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5335_, v_perm_5336_, v_fixedArgs_5337_, v_varyingArgs_5338_);
lean_dec_ref(v_fixedArgs_5337_);
return v_res_5339_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5340_, lean_object* v_x_5341_){
_start:
{
if (lean_obj_tag(v_x_5340_) == 0)
{
if (lean_obj_tag(v_x_5341_) == 0)
{
uint8_t v___x_5342_; 
v___x_5342_ = 1;
return v___x_5342_;
}
else
{
uint8_t v___x_5343_; 
v___x_5343_ = 0;
return v___x_5343_;
}
}
else
{
if (lean_obj_tag(v_x_5341_) == 0)
{
uint8_t v___x_5344_; 
v___x_5344_ = 0;
return v___x_5344_;
}
else
{
lean_object* v_val_5345_; lean_object* v_val_5346_; uint8_t v___x_5347_; 
v_val_5345_ = lean_ctor_get(v_x_5340_, 0);
v_val_5346_ = lean_ctor_get(v_x_5341_, 0);
v___x_5347_ = lean_nat_dec_eq(v_val_5345_, v_val_5346_);
return v___x_5347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5348_, lean_object* v_x_5349_){
_start:
{
uint8_t v_res_5350_; lean_object* v_r_5351_; 
v_res_5350_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5348_, v_x_5349_);
lean_dec(v_x_5349_);
lean_dec(v_x_5348_);
v_r_5351_ = lean_box(v_res_5350_);
return v_r_5351_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5352_, lean_object* v_ys_5353_, lean_object* v_x_5354_){
_start:
{
lean_object* v_zero_5355_; uint8_t v_isZero_5356_; 
v_zero_5355_ = lean_unsigned_to_nat(0u);
v_isZero_5356_ = lean_nat_dec_eq(v_x_5354_, v_zero_5355_);
if (v_isZero_5356_ == 1)
{
lean_dec(v_x_5354_);
return v_isZero_5356_;
}
else
{
lean_object* v_one_5357_; lean_object* v_n_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; uint8_t v___x_5361_; 
v_one_5357_ = lean_unsigned_to_nat(1u);
v_n_5358_ = lean_nat_sub(v_x_5354_, v_one_5357_);
lean_dec(v_x_5354_);
v___x_5359_ = lean_array_fget_borrowed(v_xs_5352_, v_n_5358_);
v___x_5360_ = lean_array_fget_borrowed(v_ys_5353_, v_n_5358_);
v___x_5361_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5359_, v___x_5360_);
if (v___x_5361_ == 0)
{
lean_dec(v_n_5358_);
return v___x_5361_;
}
else
{
v_x_5354_ = v_n_5358_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5363_, lean_object* v_ys_5364_, lean_object* v_x_5365_){
_start:
{
uint8_t v_res_5366_; lean_object* v_r_5367_; 
v_res_5366_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5363_, v_ys_5364_, v_x_5365_);
lean_dec_ref(v_ys_5364_);
lean_dec_ref(v_xs_5363_);
v_r_5367_ = lean_box(v_res_5366_);
return v_r_5367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5368_, size_t v_i_5369_, lean_object* v_bs_5370_){
_start:
{
uint8_t v___x_5371_; 
v___x_5371_ = lean_usize_dec_lt(v_i_5369_, v_sz_5368_);
if (v___x_5371_ == 0)
{
return v_bs_5370_;
}
else
{
lean_object* v_v_5372_; lean_object* v___x_5373_; lean_object* v_bs_x27_5374_; lean_object* v___x_5375_; size_t v___x_5376_; size_t v___x_5377_; lean_object* v___x_5378_; 
v_v_5372_ = lean_array_uget(v_bs_5370_, v_i_5369_);
v___x_5373_ = lean_unsigned_to_nat(0u);
v_bs_x27_5374_ = lean_array_uset(v_bs_5370_, v_i_5369_, v___x_5373_);
v___x_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5375_, 0, v_v_5372_);
v___x_5376_ = ((size_t)1ULL);
v___x_5377_ = lean_usize_add(v_i_5369_, v___x_5376_);
v___x_5378_ = lean_array_uset(v_bs_x27_5374_, v_i_5369_, v___x_5375_);
v_i_5369_ = v___x_5377_;
v_bs_5370_ = v___x_5378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5380_, lean_object* v_i_5381_, lean_object* v_bs_5382_){
_start:
{
size_t v_sz_boxed_5383_; size_t v_i_boxed_5384_; lean_object* v_res_5385_; 
v_sz_boxed_5383_ = lean_unbox_usize(v_sz_5380_);
lean_dec(v_sz_5380_);
v_i_boxed_5384_ = lean_unbox_usize(v_i_5381_);
lean_dec(v_i_5381_);
v_res_5385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5383_, v_i_boxed_5384_, v_bs_5382_);
return v_res_5385_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5386_, lean_object* v_as_5387_, size_t v_i_5388_, size_t v_stop_5389_){
_start:
{
uint8_t v___x_5390_; 
v___x_5390_ = lean_usize_dec_eq(v_i_5388_, v_stop_5389_);
if (v___x_5390_ == 0)
{
lean_object* v_numFixed_5391_; uint8_t v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; size_t v_sz_5395_; size_t v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; uint8_t v___x_5404_; 
v_numFixed_5391_ = lean_ctor_get(v_fixedParamPerms_5386_, 0);
v___x_5392_ = 1;
v___x_5393_ = lean_array_uget_borrowed(v_as_5387_, v_i_5388_);
lean_inc(v_numFixed_5391_);
v___x_5394_ = l_Array_range(v_numFixed_5391_);
v_sz_5395_ = lean_array_size(v___x_5394_);
v___x_5396_ = ((size_t)0ULL);
v___x_5397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5395_, v___x_5396_, v___x_5394_);
v___x_5398_ = lean_array_get_size(v___x_5393_);
v___x_5399_ = lean_nat_sub(v___x_5398_, v_numFixed_5391_);
v___x_5400_ = lean_box(0);
v___x_5401_ = lean_mk_array(v___x_5399_, v___x_5400_);
v___x_5402_ = l_Array_append___redArg(v___x_5397_, v___x_5401_);
lean_dec_ref(v___x_5401_);
v___x_5403_ = lean_array_get_size(v___x_5402_);
v___x_5404_ = lean_nat_dec_eq(v___x_5398_, v___x_5403_);
if (v___x_5404_ == 0)
{
lean_dec_ref(v___x_5402_);
lean_dec_ref(v_fixedParamPerms_5386_);
return v___x_5392_;
}
else
{
uint8_t v___x_5405_; 
v___x_5405_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5393_, v___x_5402_, v___x_5398_);
lean_dec_ref(v___x_5402_);
if (v___x_5405_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5386_);
return v___x_5392_;
}
else
{
if (v___x_5390_ == 0)
{
size_t v___x_5406_; size_t v___x_5407_; 
v___x_5406_ = ((size_t)1ULL);
v___x_5407_ = lean_usize_add(v_i_5388_, v___x_5406_);
v_i_5388_ = v___x_5407_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5386_);
return v___x_5392_;
}
}
}
}
else
{
uint8_t v___x_5409_; 
lean_dec_ref(v_fixedParamPerms_5386_);
v___x_5409_ = 0;
return v___x_5409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5410_, lean_object* v_as_5411_, lean_object* v_i_5412_, lean_object* v_stop_5413_){
_start:
{
size_t v_i_boxed_5414_; size_t v_stop_boxed_5415_; uint8_t v_res_5416_; lean_object* v_r_5417_; 
v_i_boxed_5414_ = lean_unbox_usize(v_i_5412_);
lean_dec(v_i_5412_);
v_stop_boxed_5415_ = lean_unbox_usize(v_stop_5413_);
lean_dec(v_stop_5413_);
v_res_5416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5410_, v_as_5411_, v_i_boxed_5414_, v_stop_boxed_5415_);
lean_dec_ref(v_as_5411_);
v_r_5417_ = lean_box(v_res_5416_);
return v_r_5417_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5418_){
_start:
{
lean_object* v_perms_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; uint8_t v___x_5422_; 
v_perms_5419_ = lean_ctor_get(v_fixedParamPerms_5418_, 1);
lean_inc_ref(v_perms_5419_);
v___x_5420_ = lean_unsigned_to_nat(0u);
v___x_5421_ = lean_array_get_size(v_perms_5419_);
v___x_5422_ = lean_nat_dec_lt(v___x_5420_, v___x_5421_);
if (v___x_5422_ == 0)
{
uint8_t v___x_5423_; 
lean_dec_ref(v_perms_5419_);
lean_dec_ref(v_fixedParamPerms_5418_);
v___x_5423_ = 1;
return v___x_5423_;
}
else
{
if (v___x_5422_ == 0)
{
lean_dec_ref(v_perms_5419_);
lean_dec_ref(v_fixedParamPerms_5418_);
return v___x_5422_;
}
else
{
size_t v___x_5424_; size_t v___x_5425_; uint8_t v___x_5426_; 
v___x_5424_ = ((size_t)0ULL);
v___x_5425_ = lean_usize_of_nat(v___x_5421_);
v___x_5426_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5418_, v_perms_5419_, v___x_5424_, v___x_5425_);
lean_dec_ref(v_perms_5419_);
if (v___x_5426_ == 0)
{
return v___x_5422_;
}
else
{
uint8_t v___x_5427_; 
v___x_5427_ = 0;
return v___x_5427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5428_){
_start:
{
uint8_t v_res_5429_; lean_object* v_r_5430_; 
v_res_5429_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5428_);
v_r_5430_ = lean_box(v_res_5429_);
return v_r_5430_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5431_, lean_object* v_ys_5432_, lean_object* v_hsz_5433_, lean_object* v_x_5434_, lean_object* v_x_5435_){
_start:
{
uint8_t v___x_5436_; 
v___x_5436_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5431_, v_ys_5432_, v_x_5434_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5437_, lean_object* v_ys_5438_, lean_object* v_hsz_5439_, lean_object* v_x_5440_, lean_object* v_x_5441_){
_start:
{
uint8_t v_res_5442_; lean_object* v_r_5443_; 
v_res_5442_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5437_, v_ys_5438_, v_hsz_5439_, v_x_5440_, v_x_5441_);
lean_dec_ref(v_ys_5438_);
lean_dec_ref(v_xs_5437_);
v_r_5443_ = lean_box(v_res_5442_);
return v_r_5443_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5444_; 
v___x_5444_ = l_Array_instInhabited(lean_box(0));
return v___x_5444_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5445_){
_start:
{
lean_object* v___f_5446_; lean_object* v___f_5447_; lean_object* v___f_5448_; lean_object* v___f_5449_; lean_object* v___f_5450_; lean_object* v___f_5451_; lean_object* v___f_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___f_5446_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5447_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5448_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5449_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5450_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5451_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5452_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5453_, 0, v___f_5446_);
lean_ctor_set(v___x_5453_, 1, v___f_5447_);
v___x_5454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5454_, 0, v___x_5453_);
lean_ctor_set(v___x_5454_, 1, v___f_5448_);
lean_ctor_set(v___x_5454_, 2, v___f_5449_);
lean_ctor_set(v___x_5454_, 3, v___f_5450_);
lean_ctor_set(v___x_5454_, 4, v___f_5451_);
v___x_5455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5455_, 0, v___x_5454_);
lean_ctor_set(v___x_5455_, 1, v___f_5452_);
v___x_5456_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5457_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5458_, 0, v___x_5457_);
lean_ctor_set(v___x_5458_, 1, v___x_5457_);
v___x_5459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5459_, 0, v___x_5456_);
lean_ctor_set(v___x_5459_, 1, v___x_5458_);
v___x_5460_ = l_instInhabitedOfMonad___redArg(v___x_5455_, v___x_5459_);
v___x_5461_ = lean_panic_fn_borrowed(v___x_5460_, v_msg_5445_);
lean_dec(v___x_5460_);
return v___x_5461_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5462_; 
v___x_5462_ = l_Array_instInhabited(lean_box(0));
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5463_){
_start:
{
lean_object* v___f_5464_; lean_object* v___f_5465_; lean_object* v___f_5466_; lean_object* v___f_5467_; lean_object* v___f_5468_; lean_object* v___f_5469_; lean_object* v___f_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; 
v___f_5464_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5465_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5466_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5467_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5468_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5469_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5470_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5471_, 0, v___f_5464_);
lean_ctor_set(v___x_5471_, 1, v___f_5465_);
v___x_5472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5472_, 0, v___x_5471_);
lean_ctor_set(v___x_5472_, 1, v___f_5466_);
lean_ctor_set(v___x_5472_, 2, v___f_5467_);
lean_ctor_set(v___x_5472_, 3, v___f_5468_);
lean_ctor_set(v___x_5472_, 4, v___f_5469_);
v___x_5473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5473_, 0, v___x_5472_);
lean_ctor_set(v___x_5473_, 1, v___f_5470_);
v___x_5474_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5475_, 0, v___x_5474_);
v___x_5476_ = l_instInhabitedOfMonad___redArg(v___x_5473_, v___x_5475_);
v___x_5477_ = lean_panic_fn_borrowed(v___x_5476_, v_msg_5463_);
lean_dec(v___x_5476_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5478_, uint8_t v___x_5479_, lean_object* v_as_5480_, size_t v_sz_5481_, size_t v_i_5482_, lean_object* v_b_5483_){
_start:
{
lean_object* v_a_5485_; uint8_t v___x_5489_; 
v___x_5489_ = lean_usize_dec_lt(v_i_5482_, v_sz_5481_);
if (v___x_5489_ == 0)
{
return v_b_5483_;
}
else
{
lean_object* v_fst_5490_; lean_object* v_snd_5491_; lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5512_; 
v_fst_5490_ = lean_ctor_get(v_b_5483_, 0);
v_snd_5491_ = lean_ctor_get(v_b_5483_, 1);
v_isSharedCheck_5512_ = !lean_is_exclusive(v_b_5483_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5493_ = v_b_5483_;
v_isShared_5494_ = v_isSharedCheck_5512_;
goto v_resetjp_5492_;
}
else
{
lean_inc(v_snd_5491_);
lean_inc(v_fst_5490_);
lean_dec(v_b_5483_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5512_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v_a_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; 
v_a_5499_ = lean_array_uget_borrowed(v_as_5480_, v_i_5482_);
v___x_5500_ = lean_box(0);
v___x_5501_ = lean_array_get_borrowed(v___x_5500_, v___x_5478_, v_a_5499_);
if (lean_obj_tag(v___x_5501_) == 1)
{
lean_object* v_val_5502_; uint8_t v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; uint8_t v___x_5506_; 
v_val_5502_ = lean_ctor_get(v___x_5501_, 0);
v___x_5503_ = 0;
v___x_5504_ = lean_box(v___x_5503_);
v___x_5505_ = lean_array_get(v___x_5504_, v_fst_5490_, v_val_5502_);
lean_dec(v___x_5504_);
v___x_5506_ = lean_unbox(v___x_5505_);
lean_dec(v___x_5505_);
if (v___x_5506_ == 0)
{
if (v___x_5479_ == 0)
{
goto v___jp_5495_;
}
else
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; 
lean_del_object(v___x_5493_);
lean_dec(v_snd_5491_);
v___x_5507_ = lean_box(v___x_5479_);
v___x_5508_ = lean_array_set(v_fst_5490_, v_val_5502_, v___x_5507_);
v___x_5509_ = lean_box(v___x_5479_);
v___x_5510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5510_, 0, v___x_5508_);
lean_ctor_set(v___x_5510_, 1, v___x_5509_);
v_a_5485_ = v___x_5510_;
goto v___jp_5484_;
}
}
else
{
goto v___jp_5495_;
}
}
else
{
lean_object* v___x_5511_; 
lean_del_object(v___x_5493_);
v___x_5511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5511_, 0, v_fst_5490_);
lean_ctor_set(v___x_5511_, 1, v_snd_5491_);
v_a_5485_ = v___x_5511_;
goto v___jp_5484_;
}
v___jp_5495_:
{
lean_object* v___x_5497_; 
if (v_isShared_5494_ == 0)
{
v___x_5497_ = v___x_5493_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_fst_5490_);
lean_ctor_set(v_reuseFailAlloc_5498_, 1, v_snd_5491_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
v_a_5485_ = v___x_5497_;
goto v___jp_5484_;
}
}
}
}
v___jp_5484_:
{
size_t v___x_5486_; size_t v___x_5487_; 
v___x_5486_ = ((size_t)1ULL);
v___x_5487_ = lean_usize_add(v_i_5482_, v___x_5486_);
v_i_5482_ = v___x_5487_;
v_b_5483_ = v_a_5485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5513_, lean_object* v___x_5514_, lean_object* v_as_5515_, lean_object* v_sz_5516_, lean_object* v_i_5517_, lean_object* v_b_5518_){
_start:
{
uint8_t v___x_8295__boxed_5519_; size_t v_sz_boxed_5520_; size_t v_i_boxed_5521_; lean_object* v_res_5522_; 
v___x_8295__boxed_5519_ = lean_unbox(v___x_5514_);
v_sz_boxed_5520_ = lean_unbox_usize(v_sz_5516_);
lean_dec(v_sz_5516_);
v_i_boxed_5521_ = lean_unbox_usize(v_i_5517_);
lean_dec(v_i_5517_);
v_res_5522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5513_, v___x_8295__boxed_5519_, v_as_5515_, v_sz_boxed_5520_, v_i_boxed_5521_, v_b_5518_);
lean_dec_ref(v_as_5515_);
lean_dec_ref(v___x_5513_);
return v_res_5522_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5523_, lean_object* v___x_5524_, lean_object* v_fixedParamPerms_5525_, lean_object* v_next_5526_, lean_object* v_a_5527_, lean_object* v_b_5528_){
_start:
{
lean_object* v_a_5530_; uint8_t v___x_5534_; 
v___x_5534_ = lean_nat_dec_lt(v_a_5527_, v_upperBound_5523_);
if (v___x_5534_ == 0)
{
lean_dec(v_a_5527_);
return v_b_5528_;
}
else
{
lean_object* v_fst_5535_; lean_object* v_snd_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5572_; 
v_fst_5535_ = lean_ctor_get(v_b_5528_, 0);
v_snd_5536_ = lean_ctor_get(v_b_5528_, 1);
v_isSharedCheck_5572_ = !lean_is_exclusive(v_b_5528_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5538_ = v_b_5528_;
v_isShared_5539_ = v_isSharedCheck_5572_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_snd_5536_);
lean_inc(v_fst_5535_);
lean_dec(v_b_5528_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5572_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5540_; 
v___x_5540_ = lean_array_fget_borrowed(v___x_5524_, v_a_5527_);
if (lean_obj_tag(v___x_5540_) == 1)
{
lean_object* v_val_5541_; uint8_t v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; uint8_t v___x_5545_; 
v_val_5541_ = lean_ctor_get(v___x_5540_, 0);
v___x_5542_ = 0;
v___x_5543_ = lean_box(v___x_5542_);
v___x_5544_ = lean_array_get(v___x_5543_, v_fst_5535_, v_val_5541_);
lean_dec(v___x_5543_);
v___x_5545_ = lean_unbox(v___x_5544_);
if (v___x_5545_ == 0)
{
lean_object* v___x_5547_; 
lean_dec(v___x_5544_);
if (v_isShared_5539_ == 0)
{
v___x_5547_ = v___x_5538_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_fst_5535_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_snd_5536_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
v_a_5530_ = v___x_5547_;
goto v___jp_5529_;
}
}
else
{
lean_object* v_revDeps_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5554_; 
v_revDeps_5549_ = lean_ctor_get(v_fixedParamPerms_5525_, 2);
v___x_5550_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5551_ = lean_array_get_borrowed(v___x_5550_, v_revDeps_5549_, v_next_5526_);
v___x_5552_ = lean_array_get_borrowed(v___x_5550_, v___x_5551_, v_a_5527_);
if (v_isShared_5539_ == 0)
{
v___x_5554_ = v___x_5538_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_fst_5535_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v_snd_5536_);
v___x_5554_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
size_t v_sz_5555_; size_t v___x_5556_; uint8_t v___x_5557_; lean_object* v___x_5558_; lean_object* v_fst_5559_; lean_object* v_snd_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5567_; 
v_sz_5555_ = lean_array_size(v___x_5552_);
v___x_5556_ = ((size_t)0ULL);
v___x_5557_ = lean_unbox(v___x_5544_);
lean_dec(v___x_5544_);
v___x_5558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5524_, v___x_5557_, v___x_5552_, v_sz_5555_, v___x_5556_, v___x_5554_);
v_fst_5559_ = lean_ctor_get(v___x_5558_, 0);
v_snd_5560_ = lean_ctor_get(v___x_5558_, 1);
v_isSharedCheck_5567_ = !lean_is_exclusive(v___x_5558_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5562_ = v___x_5558_;
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_snd_5560_);
lean_inc(v_fst_5559_);
lean_dec(v___x_5558_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5565_; 
if (v_isShared_5563_ == 0)
{
v___x_5565_ = v___x_5562_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_fst_5559_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v_snd_5560_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
v_a_5530_ = v___x_5565_;
goto v___jp_5529_;
}
}
}
}
}
else
{
lean_object* v___x_5570_; 
if (v_isShared_5539_ == 0)
{
v___x_5570_ = v___x_5538_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_fst_5535_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_snd_5536_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
v_a_5530_ = v___x_5570_;
goto v___jp_5529_;
}
}
}
}
v___jp_5529_:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; 
v___x_5531_ = lean_unsigned_to_nat(1u);
v___x_5532_ = lean_nat_add(v_a_5527_, v___x_5531_);
lean_dec(v_a_5527_);
v_a_5527_ = v___x_5532_;
v_b_5528_ = v_a_5530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5573_, lean_object* v___x_5574_, lean_object* v_fixedParamPerms_5575_, lean_object* v_next_5576_, lean_object* v_a_5577_, lean_object* v_b_5578_){
_start:
{
lean_object* v_res_5579_; 
v_res_5579_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5573_, v___x_5574_, v_fixedParamPerms_5575_, v_next_5576_, v_a_5577_, v_b_5578_);
lean_dec(v_next_5576_);
lean_dec_ref(v_fixedParamPerms_5575_);
lean_dec_ref(v___x_5574_);
lean_dec(v_upperBound_5573_);
return v_res_5579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5580_, lean_object* v___x_5581_, lean_object* v_fixedParamPerms_5582_, lean_object* v_a_5583_, lean_object* v_b_5584_){
_start:
{
uint8_t v___x_5585_; 
v___x_5585_ = lean_nat_dec_lt(v_a_5583_, v_upperBound_5580_);
if (v___x_5585_ == 0)
{
lean_dec(v_a_5583_);
return v_b_5584_;
}
else
{
lean_object* v_fst_5586_; lean_object* v_snd_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5610_; 
v_fst_5586_ = lean_ctor_get(v_b_5584_, 0);
v_snd_5587_ = lean_ctor_get(v_b_5584_, 1);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_b_5584_);
if (v_isSharedCheck_5610_ == 0)
{
v___x_5589_ = v_b_5584_;
v_isShared_5590_ = v_isSharedCheck_5610_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_snd_5587_);
lean_inc(v_fst_5586_);
lean_dec(v_b_5584_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5610_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5595_; 
v___x_5591_ = lean_array_fget_borrowed(v___x_5581_, v_a_5583_);
v___x_5592_ = lean_array_get_size(v___x_5591_);
v___x_5593_ = lean_unsigned_to_nat(0u);
if (v_isShared_5590_ == 0)
{
v___x_5595_ = v___x_5589_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_fst_5586_);
lean_ctor_set(v_reuseFailAlloc_5609_, 1, v_snd_5587_);
v___x_5595_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
lean_object* v___x_5596_; lean_object* v_fst_5597_; lean_object* v_snd_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5608_; 
v___x_5596_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5592_, v___x_5591_, v_fixedParamPerms_5582_, v_a_5583_, v___x_5593_, v___x_5595_);
v_fst_5597_ = lean_ctor_get(v___x_5596_, 0);
v_snd_5598_ = lean_ctor_get(v___x_5596_, 1);
v_isSharedCheck_5608_ = !lean_is_exclusive(v___x_5596_);
if (v_isSharedCheck_5608_ == 0)
{
v___x_5600_ = v___x_5596_;
v_isShared_5601_ = v_isSharedCheck_5608_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_snd_5598_);
lean_inc(v_fst_5597_);
lean_dec(v___x_5596_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5608_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___x_5603_; 
if (v_isShared_5601_ == 0)
{
v___x_5603_ = v___x_5600_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_fst_5597_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v_snd_5598_);
v___x_5603_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5604_ = lean_unsigned_to_nat(1u);
v___x_5605_ = lean_nat_add(v_a_5583_, v___x_5604_);
lean_dec(v_a_5583_);
v_a_5583_ = v___x_5605_;
v_b_5584_ = v___x_5603_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5611_, lean_object* v___x_5612_, lean_object* v_fixedParamPerms_5613_, lean_object* v_a_5614_, lean_object* v_b_5615_){
_start:
{
lean_object* v_res_5616_; 
v_res_5616_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5611_, v___x_5612_, v_fixedParamPerms_5613_, v_a_5614_, v_b_5615_);
lean_dec_ref(v_fixedParamPerms_5613_);
lean_dec_ref(v___x_5612_);
lean_dec(v_upperBound_5611_);
return v_res_5616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5617_, lean_object* v___x_5618_, lean_object* v_fixedParamPerms_5619_, lean_object* v_a_5620_){
_start:
{
lean_object* v_snd_5621_; uint8_t v___x_5622_; 
v_snd_5621_ = lean_ctor_get(v_a_5620_, 1);
v___x_5622_ = lean_unbox(v_snd_5621_);
if (v___x_5622_ == 0)
{
lean_object* v_fst_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5630_; 
lean_inc(v_snd_5621_);
v_fst_5623_ = lean_ctor_get(v_a_5620_, 0);
v_isSharedCheck_5630_ = !lean_is_exclusive(v_a_5620_);
if (v_isSharedCheck_5630_ == 0)
{
lean_object* v_unused_5631_; 
v_unused_5631_ = lean_ctor_get(v_a_5620_, 1);
lean_dec(v_unused_5631_);
v___x_5625_ = v_a_5620_;
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_fst_5623_);
lean_dec(v_a_5620_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5628_; 
if (v_isShared_5626_ == 0)
{
v___x_5628_ = v___x_5625_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5629_, 1, v_snd_5621_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
else
{
lean_object* v_fst_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5653_; 
v_fst_5632_ = lean_ctor_get(v_a_5620_, 0);
v_isSharedCheck_5653_ = !lean_is_exclusive(v_a_5620_);
if (v_isSharedCheck_5653_ == 0)
{
lean_object* v_unused_5654_; 
v_unused_5654_ = lean_ctor_get(v_a_5620_, 1);
lean_dec(v_unused_5654_);
v___x_5634_ = v_a_5620_;
v_isShared_5635_ = v_isSharedCheck_5653_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_fst_5632_);
lean_dec(v_a_5620_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5653_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
uint8_t v_changed_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5640_; 
v_changed_5636_ = 0;
v___x_5637_ = lean_unsigned_to_nat(0u);
v___x_5638_ = lean_box(v_changed_5636_);
if (v_isShared_5635_ == 0)
{
lean_ctor_set(v___x_5634_, 1, v___x_5638_);
v___x_5640_ = v___x_5634_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_fst_5632_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v___x_5638_);
v___x_5640_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5641_; lean_object* v_fst_5642_; lean_object* v_snd_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5651_; 
v___x_5641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5617_, v___x_5618_, v_fixedParamPerms_5619_, v___x_5637_, v___x_5640_);
v_fst_5642_ = lean_ctor_get(v___x_5641_, 0);
v_snd_5643_ = lean_ctor_get(v___x_5641_, 1);
v_isSharedCheck_5651_ = !lean_is_exclusive(v___x_5641_);
if (v_isSharedCheck_5651_ == 0)
{
v___x_5645_ = v___x_5641_;
v_isShared_5646_ = v_isSharedCheck_5651_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_snd_5643_);
lean_inc(v_fst_5642_);
lean_dec(v___x_5641_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5651_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_fst_5642_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v_snd_5643_);
v___x_5648_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
v_a_5620_ = v___x_5648_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5655_, lean_object* v___x_5656_, lean_object* v_fixedParamPerms_5657_, lean_object* v_a_5658_){
_start:
{
lean_object* v_res_5659_; 
v_res_5659_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5655_, v___x_5656_, v_fixedParamPerms_5657_, v_a_5658_);
lean_dec_ref(v_fixedParamPerms_5657_);
lean_dec_ref(v___x_5656_);
lean_dec(v___x_5655_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5660_, lean_object* v_a_5661_, lean_object* v_b_5662_){
_start:
{
lean_object* v_a_5664_; uint8_t v___x_5668_; 
v___x_5668_ = lean_nat_dec_lt(v_a_5661_, v_upperBound_5660_);
if (v___x_5668_ == 0)
{
lean_dec(v_a_5661_);
return v_b_5662_;
}
else
{
lean_object* v_snd_5669_; lean_object* v_snd_5670_; lean_object* v_snd_5671_; lean_object* v_snd_5672_; lean_object* v_fst_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5785_; 
v_snd_5669_ = lean_ctor_get(v_b_5662_, 1);
lean_inc(v_snd_5669_);
v_snd_5670_ = lean_ctor_get(v_snd_5669_, 1);
lean_inc(v_snd_5670_);
v_snd_5671_ = lean_ctor_get(v_snd_5670_, 1);
lean_inc(v_snd_5671_);
v_snd_5672_ = lean_ctor_get(v_snd_5671_, 1);
lean_inc(v_snd_5672_);
v_fst_5673_ = lean_ctor_get(v_b_5662_, 0);
v_isSharedCheck_5785_ = !lean_is_exclusive(v_b_5662_);
if (v_isSharedCheck_5785_ == 0)
{
lean_object* v_unused_5786_; 
v_unused_5786_ = lean_ctor_get(v_b_5662_, 1);
lean_dec(v_unused_5786_);
v___x_5675_ = v_b_5662_;
v_isShared_5676_ = v_isSharedCheck_5785_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_fst_5673_);
lean_dec(v_b_5662_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5785_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v_fst_5677_; lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5783_; 
v_fst_5677_ = lean_ctor_get(v_snd_5669_, 0);
v_isSharedCheck_5783_ = !lean_is_exclusive(v_snd_5669_);
if (v_isSharedCheck_5783_ == 0)
{
lean_object* v_unused_5784_; 
v_unused_5784_ = lean_ctor_get(v_snd_5669_, 1);
lean_dec(v_unused_5784_);
v___x_5679_ = v_snd_5669_;
v_isShared_5680_ = v_isSharedCheck_5783_;
goto v_resetjp_5678_;
}
else
{
lean_inc(v_fst_5677_);
lean_dec(v_snd_5669_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5783_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v_fst_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5781_; 
v_fst_5681_ = lean_ctor_get(v_snd_5670_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v_snd_5670_);
if (v_isSharedCheck_5781_ == 0)
{
lean_object* v_unused_5782_; 
v_unused_5782_ = lean_ctor_get(v_snd_5670_, 1);
lean_dec(v_unused_5782_);
v___x_5683_ = v_snd_5670_;
v_isShared_5684_ = v_isSharedCheck_5781_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_fst_5681_);
lean_dec(v_snd_5670_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5781_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v_fst_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5779_; 
v_fst_5685_ = lean_ctor_get(v_snd_5671_, 0);
v_isSharedCheck_5779_ = !lean_is_exclusive(v_snd_5671_);
if (v_isSharedCheck_5779_ == 0)
{
lean_object* v_unused_5780_; 
v_unused_5780_ = lean_ctor_get(v_snd_5671_, 1);
lean_dec(v_unused_5780_);
v___x_5687_ = v_snd_5671_;
v_isShared_5688_ = v_isSharedCheck_5779_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_fst_5685_);
lean_dec(v_snd_5671_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5779_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v_array_5689_; lean_object* v_start_5690_; lean_object* v_stop_5691_; uint8_t v___x_5692_; 
v_array_5689_ = lean_ctor_get(v_snd_5672_, 0);
v_start_5690_ = lean_ctor_get(v_snd_5672_, 1);
v_stop_5691_ = lean_ctor_get(v_snd_5672_, 2);
v___x_5692_ = lean_nat_dec_lt(v_start_5690_, v_stop_5691_);
if (v___x_5692_ == 0)
{
lean_object* v___x_5694_; 
lean_dec(v_a_5661_);
if (v_isShared_5688_ == 0)
{
v___x_5694_ = v___x_5687_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_fst_5685_);
lean_ctor_set(v_reuseFailAlloc_5704_, 1, v_snd_5672_);
v___x_5694_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
lean_object* v___x_5696_; 
if (v_isShared_5684_ == 0)
{
lean_ctor_set(v___x_5683_, 1, v___x_5694_);
v___x_5696_ = v___x_5683_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_fst_5681_);
lean_ctor_set(v_reuseFailAlloc_5703_, 1, v___x_5694_);
v___x_5696_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
lean_object* v___x_5698_; 
if (v_isShared_5680_ == 0)
{
lean_ctor_set(v___x_5679_, 1, v___x_5696_);
v___x_5698_ = v___x_5679_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_fst_5677_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v___x_5696_);
v___x_5698_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
lean_object* v___x_5700_; 
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 1, v___x_5698_);
v___x_5700_ = v___x_5675_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_fst_5673_);
lean_ctor_set(v_reuseFailAlloc_5701_, 1, v___x_5698_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
}
}
}
else
{
lean_object* v___x_5706_; uint8_t v_isShared_5707_; uint8_t v_isSharedCheck_5775_; 
lean_inc(v_stop_5691_);
lean_inc(v_start_5690_);
lean_inc_ref(v_array_5689_);
v_isSharedCheck_5775_ = !lean_is_exclusive(v_snd_5672_);
if (v_isSharedCheck_5775_ == 0)
{
lean_object* v_unused_5776_; lean_object* v_unused_5777_; lean_object* v_unused_5778_; 
v_unused_5776_ = lean_ctor_get(v_snd_5672_, 2);
lean_dec(v_unused_5776_);
v_unused_5777_ = lean_ctor_get(v_snd_5672_, 1);
lean_dec(v_unused_5777_);
v_unused_5778_ = lean_ctor_get(v_snd_5672_, 0);
lean_dec(v_unused_5778_);
v___x_5706_ = v_snd_5672_;
v_isShared_5707_ = v_isSharedCheck_5775_;
goto v_resetjp_5705_;
}
else
{
lean_dec(v_snd_5672_);
v___x_5706_ = lean_box(0);
v_isShared_5707_ = v_isSharedCheck_5775_;
goto v_resetjp_5705_;
}
v_resetjp_5705_:
{
lean_object* v_array_5708_; lean_object* v_start_5709_; lean_object* v_stop_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5715_; 
v_array_5708_ = lean_ctor_get(v_fst_5685_, 0);
v_start_5709_ = lean_ctor_get(v_fst_5685_, 1);
v_stop_5710_ = lean_ctor_get(v_fst_5685_, 2);
v___x_5711_ = lean_array_fget(v_array_5689_, v_start_5690_);
v___x_5712_ = lean_unsigned_to_nat(1u);
v___x_5713_ = lean_nat_add(v_start_5690_, v___x_5712_);
lean_dec(v_start_5690_);
if (v_isShared_5707_ == 0)
{
lean_ctor_set(v___x_5706_, 1, v___x_5713_);
v___x_5715_ = v___x_5706_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_array_5689_);
lean_ctor_set(v_reuseFailAlloc_5774_, 1, v___x_5713_);
lean_ctor_set(v_reuseFailAlloc_5774_, 2, v_stop_5691_);
v___x_5715_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
uint8_t v___x_5716_; 
v___x_5716_ = lean_nat_dec_lt(v_start_5709_, v_stop_5710_);
if (v___x_5716_ == 0)
{
lean_object* v___x_5718_; 
lean_dec(v___x_5711_);
lean_dec(v_a_5661_);
if (v_isShared_5688_ == 0)
{
lean_ctor_set(v___x_5687_, 1, v___x_5715_);
v___x_5718_ = v___x_5687_;
goto v_reusejp_5717_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v_fst_5685_);
lean_ctor_set(v_reuseFailAlloc_5728_, 1, v___x_5715_);
v___x_5718_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5717_;
}
v_reusejp_5717_:
{
lean_object* v___x_5720_; 
if (v_isShared_5684_ == 0)
{
lean_ctor_set(v___x_5683_, 1, v___x_5718_);
v___x_5720_ = v___x_5683_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_fst_5681_);
lean_ctor_set(v_reuseFailAlloc_5727_, 1, v___x_5718_);
v___x_5720_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
lean_object* v___x_5722_; 
if (v_isShared_5680_ == 0)
{
lean_ctor_set(v___x_5679_, 1, v___x_5720_);
v___x_5722_ = v___x_5679_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_fst_5677_);
lean_ctor_set(v_reuseFailAlloc_5726_, 1, v___x_5720_);
v___x_5722_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
lean_object* v___x_5724_; 
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 1, v___x_5722_);
v___x_5724_ = v___x_5675_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_fst_5673_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v___x_5722_);
v___x_5724_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
return v___x_5724_;
}
}
}
}
}
else
{
lean_object* v___x_5730_; uint8_t v_isShared_5731_; uint8_t v_isSharedCheck_5770_; 
lean_inc(v_stop_5710_);
lean_inc(v_start_5709_);
lean_inc_ref(v_array_5708_);
v_isSharedCheck_5770_ = !lean_is_exclusive(v_fst_5685_);
if (v_isSharedCheck_5770_ == 0)
{
lean_object* v_unused_5771_; lean_object* v_unused_5772_; lean_object* v_unused_5773_; 
v_unused_5771_ = lean_ctor_get(v_fst_5685_, 2);
lean_dec(v_unused_5771_);
v_unused_5772_ = lean_ctor_get(v_fst_5685_, 1);
lean_dec(v_unused_5772_);
v_unused_5773_ = lean_ctor_get(v_fst_5685_, 0);
lean_dec(v_unused_5773_);
v___x_5730_ = v_fst_5685_;
v_isShared_5731_ = v_isSharedCheck_5770_;
goto v_resetjp_5729_;
}
else
{
lean_dec(v_fst_5685_);
v___x_5730_ = lean_box(0);
v_isShared_5731_ = v_isSharedCheck_5770_;
goto v_resetjp_5729_;
}
v_resetjp_5729_:
{
lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5735_; 
v___x_5732_ = lean_array_fget(v_array_5708_, v_start_5709_);
v___x_5733_ = lean_nat_add(v_start_5709_, v___x_5712_);
lean_dec(v_start_5709_);
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 1, v___x_5733_);
v___x_5735_ = v___x_5730_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5769_; 
v_reuseFailAlloc_5769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5769_, 0, v_array_5708_);
lean_ctor_set(v_reuseFailAlloc_5769_, 1, v___x_5733_);
lean_ctor_set(v_reuseFailAlloc_5769_, 2, v_stop_5710_);
v___x_5735_ = v_reuseFailAlloc_5769_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
uint8_t v___x_5736_; 
v___x_5736_ = lean_unbox(v___x_5732_);
lean_dec(v___x_5732_);
if (v___x_5736_ == 0)
{
lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5742_; 
v___x_5737_ = lean_array_get_size(v_fst_5681_);
v___x_5738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5737_);
v___x_5739_ = lean_array_push(v_fst_5673_, v___x_5738_);
v___x_5740_ = lean_array_push(v_fst_5681_, v___x_5711_);
if (v_isShared_5688_ == 0)
{
lean_ctor_set(v___x_5687_, 1, v___x_5715_);
lean_ctor_set(v___x_5687_, 0, v___x_5735_);
v___x_5742_ = v___x_5687_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v___x_5735_);
lean_ctor_set(v_reuseFailAlloc_5752_, 1, v___x_5715_);
v___x_5742_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
lean_object* v___x_5744_; 
if (v_isShared_5684_ == 0)
{
lean_ctor_set(v___x_5683_, 1, v___x_5742_);
lean_ctor_set(v___x_5683_, 0, v___x_5740_);
v___x_5744_ = v___x_5683_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v___x_5740_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v___x_5742_);
v___x_5744_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
lean_object* v___x_5746_; 
if (v_isShared_5680_ == 0)
{
lean_ctor_set(v___x_5679_, 1, v___x_5744_);
v___x_5746_ = v___x_5679_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_fst_5677_);
lean_ctor_set(v_reuseFailAlloc_5750_, 1, v___x_5744_);
v___x_5746_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
lean_object* v___x_5748_; 
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 1, v___x_5746_);
lean_ctor_set(v___x_5675_, 0, v___x_5739_);
v___x_5748_ = v___x_5675_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v___x_5739_);
lean_ctor_set(v_reuseFailAlloc_5749_, 1, v___x_5746_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
v_a_5664_ = v___x_5748_;
goto v___jp_5663_;
}
}
}
}
}
else
{
lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5758_; 
v___x_5753_ = lean_box(0);
v___x_5754_ = lean_array_push(v_fst_5673_, v___x_5753_);
v___x_5755_ = l_Lean_Expr_fvarId_x21(v___x_5711_);
lean_dec(v___x_5711_);
v___x_5756_ = lean_array_push(v_fst_5677_, v___x_5755_);
if (v_isShared_5688_ == 0)
{
lean_ctor_set(v___x_5687_, 1, v___x_5715_);
lean_ctor_set(v___x_5687_, 0, v___x_5735_);
v___x_5758_ = v___x_5687_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v___x_5735_);
lean_ctor_set(v_reuseFailAlloc_5768_, 1, v___x_5715_);
v___x_5758_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
lean_object* v___x_5760_; 
if (v_isShared_5684_ == 0)
{
lean_ctor_set(v___x_5683_, 1, v___x_5758_);
v___x_5760_ = v___x_5683_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_fst_5681_);
lean_ctor_set(v_reuseFailAlloc_5767_, 1, v___x_5758_);
v___x_5760_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
lean_object* v___x_5762_; 
if (v_isShared_5680_ == 0)
{
lean_ctor_set(v___x_5679_, 1, v___x_5760_);
lean_ctor_set(v___x_5679_, 0, v___x_5756_);
v___x_5762_ = v___x_5679_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5766_; 
v_reuseFailAlloc_5766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5766_, 0, v___x_5756_);
lean_ctor_set(v_reuseFailAlloc_5766_, 1, v___x_5760_);
v___x_5762_ = v_reuseFailAlloc_5766_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
lean_object* v___x_5764_; 
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 1, v___x_5762_);
lean_ctor_set(v___x_5675_, 0, v___x_5754_);
v___x_5764_ = v___x_5675_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v___x_5754_);
lean_ctor_set(v_reuseFailAlloc_5765_, 1, v___x_5762_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
v_a_5664_ = v___x_5764_;
goto v___jp_5663_;
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
v___jp_5663_:
{
lean_object* v___x_5665_; lean_object* v___x_5666_; 
v___x_5665_ = lean_unsigned_to_nat(1u);
v___x_5666_ = lean_nat_add(v_a_5661_, v___x_5665_);
lean_dec(v_a_5661_);
v_a_5661_ = v___x_5666_;
v_b_5662_ = v_a_5664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5787_, lean_object* v_a_5788_, lean_object* v_b_5789_){
_start:
{
lean_object* v_res_5790_; 
v_res_5790_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5787_, v_a_5788_, v_b_5789_);
lean_dec(v_upperBound_5787_);
return v_res_5790_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5791_, size_t v_i_5792_, size_t v_stop_5793_){
_start:
{
uint8_t v___x_5794_; 
v___x_5794_ = lean_usize_dec_eq(v_i_5792_, v_stop_5793_);
if (v___x_5794_ == 0)
{
uint8_t v___x_5795_; lean_object* v___x_5796_; uint8_t v___x_5797_; 
v___x_5795_ = 1;
v___x_5796_ = lean_array_uget_borrowed(v_as_5791_, v_i_5792_);
v___x_5797_ = l_Lean_Expr_isFVar(v___x_5796_);
if (v___x_5797_ == 0)
{
return v___x_5795_;
}
else
{
if (v___x_5794_ == 0)
{
size_t v___x_5798_; size_t v___x_5799_; 
v___x_5798_ = ((size_t)1ULL);
v___x_5799_ = lean_usize_add(v_i_5792_, v___x_5798_);
v_i_5792_ = v___x_5799_;
goto _start;
}
else
{
return v___x_5795_;
}
}
}
else
{
uint8_t v___x_5801_; 
v___x_5801_ = 0;
return v___x_5801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5802_, lean_object* v_i_5803_, lean_object* v_stop_5804_){
_start:
{
size_t v_i_boxed_5805_; size_t v_stop_boxed_5806_; uint8_t v_res_5807_; lean_object* v_r_5808_; 
v_i_boxed_5805_ = lean_unbox_usize(v_i_5803_);
lean_dec(v_i_5803_);
v_stop_boxed_5806_ = lean_unbox_usize(v_stop_5804_);
lean_dec(v_stop_5804_);
v_res_5807_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5802_, v_i_boxed_5805_, v_stop_boxed_5806_);
lean_dec_ref(v_as_5802_);
v_r_5808_ = lean_box(v_res_5807_);
return v_r_5808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5809_, size_t v_sz_5810_, size_t v_i_5811_, lean_object* v_bs_5812_){
_start:
{
uint8_t v___x_5813_; 
v___x_5813_ = lean_usize_dec_lt(v_i_5811_, v_sz_5810_);
if (v___x_5813_ == 0)
{
return v_bs_5812_;
}
else
{
lean_object* v_v_5814_; lean_object* v___x_5815_; lean_object* v_bs_x27_5816_; lean_object* v___y_5818_; 
v_v_5814_ = lean_array_uget(v_bs_5812_, v_i_5811_);
v___x_5815_ = lean_unsigned_to_nat(0u);
v_bs_x27_5816_ = lean_array_uset(v_bs_5812_, v_i_5811_, v___x_5815_);
if (lean_obj_tag(v_v_5814_) == 0)
{
v___y_5818_ = v_v_5814_;
goto v___jp_5817_;
}
else
{
lean_object* v_val_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; 
v_val_5823_ = lean_ctor_get(v_v_5814_, 0);
lean_inc(v_val_5823_);
lean_dec_ref_known(v_v_5814_, 1);
v___x_5824_ = lean_box(0);
v___x_5825_ = lean_array_get_borrowed(v___x_5824_, v___x_5809_, v_val_5823_);
lean_dec(v_val_5823_);
lean_inc(v___x_5825_);
v___y_5818_ = v___x_5825_;
goto v___jp_5817_;
}
v___jp_5817_:
{
size_t v___x_5819_; size_t v___x_5820_; lean_object* v___x_5821_; 
v___x_5819_ = ((size_t)1ULL);
v___x_5820_ = lean_usize_add(v_i_5811_, v___x_5819_);
v___x_5821_ = lean_array_uset(v_bs_x27_5816_, v_i_5811_, v___y_5818_);
v_i_5811_ = v___x_5820_;
v_bs_5812_ = v___x_5821_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5826_, lean_object* v_sz_5827_, lean_object* v_i_5828_, lean_object* v_bs_5829_){
_start:
{
size_t v_sz_boxed_5830_; size_t v_i_boxed_5831_; lean_object* v_res_5832_; 
v_sz_boxed_5830_ = lean_unbox_usize(v_sz_5827_);
lean_dec(v_sz_5827_);
v_i_boxed_5831_ = lean_unbox_usize(v_i_5828_);
lean_dec(v_i_5828_);
v_res_5832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5826_, v_sz_boxed_5830_, v_i_boxed_5831_, v_bs_5829_);
lean_dec_ref(v___x_5826_);
return v_res_5832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5833_, size_t v_sz_5834_, size_t v_i_5835_, lean_object* v_bs_5836_){
_start:
{
uint8_t v___x_5837_; 
v___x_5837_ = lean_usize_dec_lt(v_i_5835_, v_sz_5834_);
if (v___x_5837_ == 0)
{
return v_bs_5836_;
}
else
{
lean_object* v_v_5838_; lean_object* v___x_5839_; lean_object* v_bs_x27_5840_; size_t v_sz_5841_; size_t v___x_5842_; lean_object* v___x_5843_; size_t v___x_5844_; size_t v___x_5845_; lean_object* v___x_5846_; 
v_v_5838_ = lean_array_uget(v_bs_5836_, v_i_5835_);
v___x_5839_ = lean_unsigned_to_nat(0u);
v_bs_x27_5840_ = lean_array_uset(v_bs_5836_, v_i_5835_, v___x_5839_);
v_sz_5841_ = lean_array_size(v_v_5838_);
v___x_5842_ = ((size_t)0ULL);
v___x_5843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5833_, v_sz_5841_, v___x_5842_, v_v_5838_);
v___x_5844_ = ((size_t)1ULL);
v___x_5845_ = lean_usize_add(v_i_5835_, v___x_5844_);
v___x_5846_ = lean_array_uset(v_bs_x27_5840_, v_i_5835_, v___x_5843_);
v_i_5835_ = v___x_5845_;
v_bs_5836_ = v___x_5846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5848_, lean_object* v_sz_5849_, lean_object* v_i_5850_, lean_object* v_bs_5851_){
_start:
{
size_t v_sz_boxed_5852_; size_t v_i_boxed_5853_; lean_object* v_res_5854_; 
v_sz_boxed_5852_ = lean_unbox_usize(v_sz_5849_);
lean_dec(v_sz_5849_);
v_i_boxed_5853_ = lean_unbox_usize(v_i_5850_);
lean_dec(v_i_5850_);
v_res_5854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5848_, v_sz_boxed_5852_, v_i_boxed_5853_, v_bs_5851_);
lean_dec_ref(v___x_5848_);
return v_res_5854_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5858_ = lean_unsigned_to_nat(6u);
v___x_5859_ = lean_unsigned_to_nat(463u);
v___x_5860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5861_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5862_ = l_mkPanicMessageWithDecl(v___x_5861_, v___x_5860_, v___x_5859_, v___x_5858_, v___x_5857_);
return v___x_5862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5863_, lean_object* v_as_5864_, size_t v_sz_5865_, size_t v_i_5866_, lean_object* v_b_5867_){
_start:
{
lean_object* v_a_5869_; uint8_t v___x_5873_; 
v___x_5873_ = lean_usize_dec_lt(v_i_5866_, v_sz_5865_);
if (v___x_5873_ == 0)
{
return v_b_5867_;
}
else
{
lean_object* v_a_5874_; lean_object* v___x_5875_; uint8_t v_changed_5876_; 
v_a_5874_ = lean_array_uget_borrowed(v_as_5864_, v_i_5866_);
v___x_5875_ = lean_array_get_size(v___x_5863_);
v_changed_5876_ = lean_nat_dec_lt(v_a_5874_, v___x_5875_);
if (v_changed_5876_ == 0)
{
lean_object* v___x_5877_; lean_object* v___x_5878_; 
lean_dec_ref(v_b_5867_);
v___x_5877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5878_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5877_);
if (lean_obj_tag(v___x_5878_) == 0)
{
lean_object* v_a_5879_; 
v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
lean_inc(v_a_5879_);
lean_dec_ref_known(v___x_5878_, 1);
return v_a_5879_;
}
else
{
lean_object* v_a_5880_; 
v_a_5880_ = lean_ctor_get(v___x_5878_, 0);
lean_inc(v_a_5880_);
lean_dec_ref_known(v___x_5878_, 1);
v_a_5869_ = v_a_5880_;
goto v___jp_5868_;
}
}
else
{
lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5881_ = lean_box(0);
v___x_5882_ = lean_array_get_borrowed(v___x_5881_, v___x_5863_, v_a_5874_);
if (lean_obj_tag(v___x_5882_) == 1)
{
lean_object* v_val_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; 
v_val_5883_ = lean_ctor_get(v___x_5882_, 0);
v___x_5884_ = lean_box(v_changed_5876_);
v___x_5885_ = lean_array_set(v_b_5867_, v_val_5883_, v___x_5884_);
v_a_5869_ = v___x_5885_;
goto v___jp_5868_;
}
else
{
v_a_5869_ = v_b_5867_;
goto v___jp_5868_;
}
}
}
v___jp_5868_:
{
size_t v___x_5870_; size_t v___x_5871_; 
v___x_5870_ = ((size_t)1ULL);
v___x_5871_ = lean_usize_add(v_i_5866_, v___x_5870_);
v_i_5866_ = v___x_5871_;
v_b_5867_ = v_a_5869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5886_, lean_object* v_as_5887_, lean_object* v_sz_5888_, lean_object* v_i_5889_, lean_object* v_b_5890_){
_start:
{
size_t v_sz_boxed_5891_; size_t v_i_boxed_5892_; lean_object* v_res_5893_; 
v_sz_boxed_5891_ = lean_unbox_usize(v_sz_5888_);
lean_dec(v_sz_5888_);
v_i_boxed_5892_ = lean_unbox_usize(v_i_5889_);
lean_dec(v_i_5889_);
v_res_5893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5886_, v_as_5887_, v_sz_boxed_5891_, v_i_boxed_5892_, v_b_5890_);
lean_dec_ref(v_as_5887_);
lean_dec_ref(v___x_5886_);
return v_res_5893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5894_, lean_object* v_a_5895_, lean_object* v_b_5896_){
_start:
{
uint8_t v___x_5897_; 
v___x_5897_ = lean_nat_dec_lt(v_a_5895_, v_upperBound_5894_);
if (v___x_5897_ == 0)
{
lean_dec(v_a_5895_);
return v_b_5896_;
}
else
{
lean_object* v_snd_5898_; lean_object* v_snd_5899_; lean_object* v_fst_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5966_; 
v_snd_5898_ = lean_ctor_get(v_b_5896_, 1);
lean_inc(v_snd_5898_);
v_snd_5899_ = lean_ctor_get(v_snd_5898_, 1);
lean_inc(v_snd_5899_);
v_fst_5900_ = lean_ctor_get(v_b_5896_, 0);
v_isSharedCheck_5966_ = !lean_is_exclusive(v_b_5896_);
if (v_isSharedCheck_5966_ == 0)
{
lean_object* v_unused_5967_; 
v_unused_5967_ = lean_ctor_get(v_b_5896_, 1);
lean_dec(v_unused_5967_);
v___x_5902_ = v_b_5896_;
v_isShared_5903_ = v_isSharedCheck_5966_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_fst_5900_);
lean_dec(v_b_5896_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5966_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v_fst_5904_; lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_5964_; 
v_fst_5904_ = lean_ctor_get(v_snd_5898_, 0);
v_isSharedCheck_5964_ = !lean_is_exclusive(v_snd_5898_);
if (v_isSharedCheck_5964_ == 0)
{
lean_object* v_unused_5965_; 
v_unused_5965_ = lean_ctor_get(v_snd_5898_, 1);
lean_dec(v_unused_5965_);
v___x_5906_ = v_snd_5898_;
v_isShared_5907_ = v_isSharedCheck_5964_;
goto v_resetjp_5905_;
}
else
{
lean_inc(v_fst_5904_);
lean_dec(v_snd_5898_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_5964_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v_array_5908_; lean_object* v_start_5909_; lean_object* v_stop_5910_; uint8_t v___x_5911_; 
v_array_5908_ = lean_ctor_get(v_snd_5899_, 0);
v_start_5909_ = lean_ctor_get(v_snd_5899_, 1);
v_stop_5910_ = lean_ctor_get(v_snd_5899_, 2);
v___x_5911_ = lean_nat_dec_lt(v_start_5909_, v_stop_5910_);
if (v___x_5911_ == 0)
{
lean_object* v___x_5913_; 
lean_dec(v_a_5895_);
if (v_isShared_5907_ == 0)
{
v___x_5913_ = v___x_5906_;
goto v_reusejp_5912_;
}
else
{
lean_object* v_reuseFailAlloc_5917_; 
v_reuseFailAlloc_5917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_fst_5904_);
lean_ctor_set(v_reuseFailAlloc_5917_, 1, v_snd_5899_);
v___x_5913_ = v_reuseFailAlloc_5917_;
goto v_reusejp_5912_;
}
v_reusejp_5912_:
{
lean_object* v___x_5915_; 
if (v_isShared_5903_ == 0)
{
lean_ctor_set(v___x_5902_, 1, v___x_5913_);
v___x_5915_ = v___x_5902_;
goto v_reusejp_5914_;
}
else
{
lean_object* v_reuseFailAlloc_5916_; 
v_reuseFailAlloc_5916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5916_, 0, v_fst_5900_);
lean_ctor_set(v_reuseFailAlloc_5916_, 1, v___x_5913_);
v___x_5915_ = v_reuseFailAlloc_5916_;
goto v_reusejp_5914_;
}
v_reusejp_5914_:
{
return v___x_5915_;
}
}
}
else
{
lean_object* v___x_5919_; uint8_t v_isShared_5920_; uint8_t v_isSharedCheck_5960_; 
lean_inc(v_stop_5910_);
lean_inc(v_start_5909_);
lean_inc_ref(v_array_5908_);
v_isSharedCheck_5960_ = !lean_is_exclusive(v_snd_5899_);
if (v_isSharedCheck_5960_ == 0)
{
lean_object* v_unused_5961_; lean_object* v_unused_5962_; lean_object* v_unused_5963_; 
v_unused_5961_ = lean_ctor_get(v_snd_5899_, 2);
lean_dec(v_unused_5961_);
v_unused_5962_ = lean_ctor_get(v_snd_5899_, 1);
lean_dec(v_unused_5962_);
v_unused_5963_ = lean_ctor_get(v_snd_5899_, 0);
lean_dec(v_unused_5963_);
v___x_5919_ = v_snd_5899_;
v_isShared_5920_ = v_isSharedCheck_5960_;
goto v_resetjp_5918_;
}
else
{
lean_dec(v_snd_5899_);
v___x_5919_ = lean_box(0);
v_isShared_5920_ = v_isSharedCheck_5960_;
goto v_resetjp_5918_;
}
v_resetjp_5918_:
{
lean_object* v_array_5921_; lean_object* v_start_5922_; lean_object* v_stop_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5928_; 
v_array_5921_ = lean_ctor_get(v_fst_5904_, 0);
v_start_5922_ = lean_ctor_get(v_fst_5904_, 1);
v_stop_5923_ = lean_ctor_get(v_fst_5904_, 2);
v___x_5924_ = lean_array_fget(v_array_5908_, v_start_5909_);
v___x_5925_ = lean_unsigned_to_nat(1u);
v___x_5926_ = lean_nat_add(v_start_5909_, v___x_5925_);
lean_dec(v_start_5909_);
if (v_isShared_5920_ == 0)
{
lean_ctor_set(v___x_5919_, 1, v___x_5926_);
v___x_5928_ = v___x_5919_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5959_; 
v_reuseFailAlloc_5959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_array_5908_);
lean_ctor_set(v_reuseFailAlloc_5959_, 1, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5959_, 2, v_stop_5910_);
v___x_5928_ = v_reuseFailAlloc_5959_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
uint8_t v___x_5929_; 
v___x_5929_ = lean_nat_dec_lt(v_start_5922_, v_stop_5923_);
if (v___x_5929_ == 0)
{
lean_object* v___x_5931_; 
lean_dec(v___x_5924_);
lean_dec(v_a_5895_);
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 1, v___x_5928_);
v___x_5931_ = v___x_5906_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_fst_5904_);
lean_ctor_set(v_reuseFailAlloc_5935_, 1, v___x_5928_);
v___x_5931_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
lean_object* v___x_5933_; 
if (v_isShared_5903_ == 0)
{
lean_ctor_set(v___x_5902_, 1, v___x_5931_);
v___x_5933_ = v___x_5902_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_fst_5900_);
lean_ctor_set(v_reuseFailAlloc_5934_, 1, v___x_5931_);
v___x_5933_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
return v___x_5933_;
}
}
}
else
{
lean_object* v___x_5937_; uint8_t v_isShared_5938_; uint8_t v_isSharedCheck_5955_; 
lean_inc(v_stop_5923_);
lean_inc(v_start_5922_);
lean_inc_ref(v_array_5921_);
v_isSharedCheck_5955_ = !lean_is_exclusive(v_fst_5904_);
if (v_isSharedCheck_5955_ == 0)
{
lean_object* v_unused_5956_; lean_object* v_unused_5957_; lean_object* v_unused_5958_; 
v_unused_5956_ = lean_ctor_get(v_fst_5904_, 2);
lean_dec(v_unused_5956_);
v_unused_5957_ = lean_ctor_get(v_fst_5904_, 1);
lean_dec(v_unused_5957_);
v_unused_5958_ = lean_ctor_get(v_fst_5904_, 0);
lean_dec(v_unused_5958_);
v___x_5937_ = v_fst_5904_;
v_isShared_5938_ = v_isSharedCheck_5955_;
goto v_resetjp_5936_;
}
else
{
lean_dec(v_fst_5904_);
v___x_5937_ = lean_box(0);
v_isShared_5938_ = v_isSharedCheck_5955_;
goto v_resetjp_5936_;
}
v_resetjp_5936_:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5942_; 
v___x_5939_ = lean_array_fget(v_array_5921_, v_start_5922_);
v___x_5940_ = lean_nat_add(v_start_5922_, v___x_5925_);
lean_dec(v_start_5922_);
if (v_isShared_5938_ == 0)
{
lean_ctor_set(v___x_5937_, 1, v___x_5940_);
v___x_5942_ = v___x_5937_;
goto v_reusejp_5941_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_array_5921_);
lean_ctor_set(v_reuseFailAlloc_5954_, 1, v___x_5940_);
lean_ctor_set(v_reuseFailAlloc_5954_, 2, v_stop_5923_);
v___x_5942_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5941_;
}
v_reusejp_5941_:
{
size_t v_sz_5943_; size_t v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5947_; 
v_sz_5943_ = lean_array_size(v___x_5939_);
v___x_5944_ = ((size_t)0ULL);
v___x_5945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5924_, v___x_5939_, v_sz_5943_, v___x_5944_, v_fst_5900_);
lean_dec(v___x_5939_);
lean_dec(v___x_5924_);
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 1, v___x_5928_);
lean_ctor_set(v___x_5906_, 0, v___x_5942_);
v___x_5947_ = v___x_5906_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v___x_5942_);
lean_ctor_set(v_reuseFailAlloc_5953_, 1, v___x_5928_);
v___x_5947_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
lean_object* v___x_5949_; 
if (v_isShared_5903_ == 0)
{
lean_ctor_set(v___x_5902_, 1, v___x_5947_);
lean_ctor_set(v___x_5902_, 0, v___x_5945_);
v___x_5949_ = v___x_5902_;
goto v_reusejp_5948_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v___x_5945_);
lean_ctor_set(v_reuseFailAlloc_5952_, 1, v___x_5947_);
v___x_5949_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5948_;
}
v_reusejp_5948_:
{
lean_object* v___x_5950_; 
v___x_5950_ = lean_nat_add(v_a_5895_, v___x_5925_);
lean_dec(v_a_5895_);
v_a_5895_ = v___x_5950_;
v_b_5896_ = v___x_5949_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_5968_, lean_object* v_a_5969_, lean_object* v_b_5970_){
_start:
{
lean_object* v_res_5971_; 
v_res_5971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_5968_, v_a_5969_, v_b_5970_);
lean_dec(v_upperBound_5968_);
return v_res_5971_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5973_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_5974_ = lean_unsigned_to_nat(2u);
v___x_5975_ = lean_unsigned_to_nat(457u);
v___x_5976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5977_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5978_ = l_mkPanicMessageWithDecl(v___x_5977_, v___x_5976_, v___x_5975_, v___x_5974_, v___x_5973_);
return v___x_5978_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5980_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_5981_ = lean_unsigned_to_nat(2u);
v___x_5982_ = lean_unsigned_to_nat(458u);
v___x_5983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5984_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5985_ = l_mkPanicMessageWithDecl(v___x_5984_, v___x_5983_, v___x_5982_, v___x_5981_, v___x_5980_);
return v___x_5985_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; 
v___x_5987_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_5988_ = lean_unsigned_to_nat(2u);
v___x_5989_ = lean_unsigned_to_nat(456u);
v___x_5990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5991_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5992_ = l_mkPanicMessageWithDecl(v___x_5991_, v___x_5990_, v___x_5989_, v___x_5988_, v___x_5987_);
return v___x_5992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_5993_, lean_object* v_xs_5994_, lean_object* v_toErase_5995_){
_start:
{
lean_object* v___x_5996_; lean_object* v___x_5997_; uint8_t v___x_6081_; 
v___x_5996_ = lean_unsigned_to_nat(0u);
v___x_5997_ = lean_array_get_size(v_xs_5994_);
v___x_6081_ = lean_nat_dec_lt(v___x_5996_, v___x_5997_);
if (v___x_6081_ == 0)
{
goto v___jp_5998_;
}
else
{
if (v___x_6081_ == 0)
{
goto v___jp_5998_;
}
else
{
size_t v___x_6082_; size_t v___x_6083_; uint8_t v___x_6084_; 
v___x_6082_ = ((size_t)0ULL);
v___x_6083_ = lean_usize_of_nat(v___x_5997_);
v___x_6084_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_5994_, v___x_6082_, v___x_6083_);
if (v___x_6084_ == 0)
{
goto v___jp_5998_;
}
else
{
lean_object* v___x_6085_; lean_object* v___x_6086_; 
lean_dec_ref(v_toErase_5995_);
lean_dec_ref(v_xs_5994_);
lean_dec_ref(v_fixedParamPerms_5993_);
v___x_6085_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6086_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6085_);
return v___x_6086_;
}
}
}
v___jp_5998_:
{
lean_object* v_numFixed_5999_; lean_object* v_perms_6000_; lean_object* v_revDeps_6001_; uint8_t v___x_6002_; 
v_numFixed_5999_ = lean_ctor_get(v_fixedParamPerms_5993_, 0);
v_perms_6000_ = lean_ctor_get(v_fixedParamPerms_5993_, 1);
lean_inc_ref(v_perms_6000_);
v_revDeps_6001_ = lean_ctor_get(v_fixedParamPerms_5993_, 2);
lean_inc_ref(v_revDeps_6001_);
v___x_6002_ = lean_nat_dec_eq(v_numFixed_5999_, v___x_5997_);
if (v___x_6002_ == 0)
{
lean_object* v___x_6003_; lean_object* v___x_6004_; 
lean_dec_ref(v_revDeps_6001_);
lean_dec_ref(v_perms_6000_);
lean_dec_ref(v_toErase_5995_);
lean_dec_ref(v_xs_5994_);
lean_dec_ref(v_fixedParamPerms_5993_);
v___x_6003_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6004_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6003_);
return v___x_6004_;
}
else
{
lean_object* v___x_6005_; lean_object* v___x_6006_; uint8_t v_changed_6007_; 
v___x_6005_ = lean_array_get_size(v_toErase_5995_);
v___x_6006_ = lean_array_get_size(v_perms_6000_);
v_changed_6007_ = lean_nat_dec_eq(v___x_6005_, v___x_6006_);
if (v_changed_6007_ == 0)
{
lean_object* v___x_6008_; lean_object* v___x_6009_; 
lean_dec_ref(v_revDeps_6001_);
lean_dec_ref(v_perms_6000_);
lean_dec_ref(v_toErase_5995_);
lean_dec_ref(v_xs_5994_);
lean_dec_ref(v_fixedParamPerms_5993_);
v___x_6008_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6009_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6008_);
return v___x_6009_;
}
else
{
uint8_t v_changed_6010_; lean_object* v___x_6011_; lean_object* v_mask_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v_fst_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6079_; 
v_changed_6010_ = 0;
v___x_6011_ = lean_box(v_changed_6010_);
lean_inc(v_numFixed_5999_);
v_mask_6012_ = lean_mk_array(v_numFixed_5999_, v___x_6011_);
v___x_6013_ = l_Array_toSubarray___redArg(v_toErase_5995_, v___x_5996_, v___x_6005_);
lean_inc_ref(v_perms_6000_);
v___x_6014_ = l_Array_toSubarray___redArg(v_perms_6000_, v___x_5996_, v___x_6006_);
v___x_6015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6013_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
v___x_6016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6016_, 0, v_mask_6012_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6005_, v___x_5996_, v___x_6016_);
v_fst_6018_ = lean_ctor_get(v___x_6017_, 0);
v_isSharedCheck_6079_ = !lean_is_exclusive(v___x_6017_);
if (v_isSharedCheck_6079_ == 0)
{
lean_object* v_unused_6080_; 
v_unused_6080_ = lean_ctor_get(v___x_6017_, 1);
lean_dec(v_unused_6080_);
v___x_6020_ = v___x_6017_;
v_isShared_6021_ = v_isSharedCheck_6079_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_fst_6018_);
lean_dec(v___x_6017_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6079_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6022_; lean_object* v___x_6024_; 
v___x_6022_ = lean_box(v_changed_6007_);
if (v_isShared_6021_ == 0)
{
lean_ctor_set(v___x_6020_, 1, v___x_6022_);
v___x_6024_ = v___x_6020_;
goto v_reusejp_6023_;
}
else
{
lean_object* v_reuseFailAlloc_6078_; 
v_reuseFailAlloc_6078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6078_, 0, v_fst_6018_);
lean_ctor_set(v_reuseFailAlloc_6078_, 1, v___x_6022_);
v___x_6024_ = v_reuseFailAlloc_6078_;
goto v_reusejp_6023_;
}
v_reusejp_6023_:
{
lean_object* v___x_6025_; lean_object* v___x_6027_; uint8_t v_isShared_6028_; uint8_t v_isSharedCheck_6074_; 
v___x_6025_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6006_, v_perms_6000_, v_fixedParamPerms_5993_, v___x_6024_);
v_isSharedCheck_6074_ = !lean_is_exclusive(v_fixedParamPerms_5993_);
if (v_isSharedCheck_6074_ == 0)
{
lean_object* v_unused_6075_; lean_object* v_unused_6076_; lean_object* v_unused_6077_; 
v_unused_6075_ = lean_ctor_get(v_fixedParamPerms_5993_, 2);
lean_dec(v_unused_6075_);
v_unused_6076_ = lean_ctor_get(v_fixedParamPerms_5993_, 1);
lean_dec(v_unused_6076_);
v_unused_6077_ = lean_ctor_get(v_fixedParamPerms_5993_, 0);
lean_dec(v_unused_6077_);
v___x_6027_ = v_fixedParamPerms_5993_;
v_isShared_6028_ = v_isSharedCheck_6074_;
goto v_resetjp_6026_;
}
else
{
lean_dec(v_fixedParamPerms_5993_);
v___x_6027_ = lean_box(0);
v_isShared_6028_ = v_isSharedCheck_6074_;
goto v_resetjp_6026_;
}
v_resetjp_6026_:
{
lean_object* v_fst_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6072_; 
v_fst_6029_ = lean_ctor_get(v___x_6025_, 0);
v_isSharedCheck_6072_ = !lean_is_exclusive(v___x_6025_);
if (v_isSharedCheck_6072_ == 0)
{
lean_object* v_unused_6073_; 
v_unused_6073_ = lean_ctor_get(v___x_6025_, 1);
lean_dec(v_unused_6073_);
v___x_6031_ = v___x_6025_;
v_isShared_6032_ = v_isSharedCheck_6072_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_fst_6029_);
lean_dec(v___x_6025_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6072_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6038_; 
v___x_6033_ = lean_array_get_size(v_fst_6029_);
v___x_6034_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6035_ = l_Array_toSubarray___redArg(v_fst_6029_, v___x_5996_, v___x_6033_);
v___x_6036_ = l_Array_toSubarray___redArg(v_xs_5994_, v___x_5996_, v___x_5997_);
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 1, v___x_6036_);
lean_ctor_set(v___x_6031_, 0, v___x_6035_);
v___x_6038_ = v___x_6031_;
goto v_reusejp_6037_;
}
else
{
lean_object* v_reuseFailAlloc_6071_; 
v_reuseFailAlloc_6071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6071_, 0, v___x_6035_);
lean_ctor_set(v_reuseFailAlloc_6071_, 1, v___x_6036_);
v___x_6038_ = v_reuseFailAlloc_6071_;
goto v_reusejp_6037_;
}
v_reusejp_6037_:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v_snd_6043_; lean_object* v_snd_6044_; lean_object* v_fst_6045_; lean_object* v_fst_6046_; lean_object* v___x_6048_; uint8_t v_isShared_6049_; uint8_t v_isSharedCheck_6069_; 
v___x_6039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6034_);
lean_ctor_set(v___x_6039_, 1, v___x_6038_);
v___x_6040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6034_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6034_);
lean_ctor_set(v___x_6041_, 1, v___x_6040_);
v___x_6042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6033_, v___x_5996_, v___x_6041_);
v_snd_6043_ = lean_ctor_get(v___x_6042_, 1);
lean_inc(v_snd_6043_);
v_snd_6044_ = lean_ctor_get(v_snd_6043_, 1);
lean_inc(v_snd_6044_);
v_fst_6045_ = lean_ctor_get(v___x_6042_, 0);
lean_inc(v_fst_6045_);
lean_dec_ref(v___x_6042_);
v_fst_6046_ = lean_ctor_get(v_snd_6043_, 0);
v_isSharedCheck_6069_ = !lean_is_exclusive(v_snd_6043_);
if (v_isSharedCheck_6069_ == 0)
{
lean_object* v_unused_6070_; 
v_unused_6070_ = lean_ctor_get(v_snd_6043_, 1);
lean_dec(v_unused_6070_);
v___x_6048_ = v_snd_6043_;
v_isShared_6049_ = v_isSharedCheck_6069_;
goto v_resetjp_6047_;
}
else
{
lean_inc(v_fst_6046_);
lean_dec(v_snd_6043_);
v___x_6048_ = lean_box(0);
v_isShared_6049_ = v_isSharedCheck_6069_;
goto v_resetjp_6047_;
}
v_resetjp_6047_:
{
lean_object* v_fst_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6067_; 
v_fst_6050_ = lean_ctor_get(v_snd_6044_, 0);
v_isSharedCheck_6067_ = !lean_is_exclusive(v_snd_6044_);
if (v_isSharedCheck_6067_ == 0)
{
lean_object* v_unused_6068_; 
v_unused_6068_ = lean_ctor_get(v_snd_6044_, 1);
lean_dec(v_unused_6068_);
v___x_6052_ = v_snd_6044_;
v_isShared_6053_ = v_isSharedCheck_6067_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_fst_6050_);
lean_dec(v_snd_6044_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6067_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6054_; size_t v_sz_6055_; size_t v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6059_; 
v___x_6054_ = lean_array_get_size(v_fst_6050_);
v_sz_6055_ = lean_array_size(v_perms_6000_);
v___x_6056_ = ((size_t)0ULL);
v___x_6057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6045_, v_sz_6055_, v___x_6056_, v_perms_6000_);
lean_dec(v_fst_6045_);
if (v_isShared_6028_ == 0)
{
lean_ctor_set(v___x_6027_, 1, v___x_6057_);
lean_ctor_set(v___x_6027_, 0, v___x_6054_);
v___x_6059_ = v___x_6027_;
goto v_reusejp_6058_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v___x_6054_);
lean_ctor_set(v_reuseFailAlloc_6066_, 1, v___x_6057_);
lean_ctor_set(v_reuseFailAlloc_6066_, 2, v_revDeps_6001_);
v___x_6059_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6058_;
}
v_reusejp_6058_:
{
lean_object* v___x_6061_; 
if (v_isShared_6053_ == 0)
{
lean_ctor_set(v___x_6052_, 1, v_fst_6046_);
v___x_6061_ = v___x_6052_;
goto v_reusejp_6060_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_fst_6050_);
lean_ctor_set(v_reuseFailAlloc_6065_, 1, v_fst_6046_);
v___x_6061_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6060_;
}
v_reusejp_6060_:
{
lean_object* v___x_6063_; 
if (v_isShared_6049_ == 0)
{
lean_ctor_set(v___x_6048_, 1, v___x_6061_);
lean_ctor_set(v___x_6048_, 0, v___x_6059_);
v___x_6063_ = v___x_6048_;
goto v_reusejp_6062_;
}
else
{
lean_object* v_reuseFailAlloc_6064_; 
v_reuseFailAlloc_6064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6064_, 0, v___x_6059_);
lean_ctor_set(v_reuseFailAlloc_6064_, 1, v___x_6061_);
v___x_6063_ = v_reuseFailAlloc_6064_;
goto v_reusejp_6062_;
}
v_reusejp_6062_:
{
return v___x_6063_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6087_, lean_object* v___x_6088_, lean_object* v_fixedParamPerms_6089_, lean_object* v_next_6090_, lean_object* v_inst_6091_, lean_object* v_R_6092_, lean_object* v_a_6093_, lean_object* v_b_6094_, lean_object* v_c_6095_){
_start:
{
lean_object* v___x_6096_; 
v___x_6096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6087_, v___x_6088_, v_fixedParamPerms_6089_, v_next_6090_, v_a_6093_, v_b_6094_);
return v___x_6096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6097_, lean_object* v___x_6098_, lean_object* v_fixedParamPerms_6099_, lean_object* v_next_6100_, lean_object* v_inst_6101_, lean_object* v_R_6102_, lean_object* v_a_6103_, lean_object* v_b_6104_, lean_object* v_c_6105_){
_start:
{
lean_object* v_res_6106_; 
v_res_6106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6097_, v___x_6098_, v_fixedParamPerms_6099_, v_next_6100_, v_inst_6101_, v_R_6102_, v_a_6103_, v_b_6104_, v_c_6105_);
lean_dec(v_next_6100_);
lean_dec_ref(v_fixedParamPerms_6099_);
lean_dec_ref(v___x_6098_);
lean_dec(v_upperBound_6097_);
return v_res_6106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6107_, lean_object* v___x_6108_, lean_object* v_fixedParamPerms_6109_, lean_object* v_inst_6110_, lean_object* v_R_6111_, lean_object* v_a_6112_, lean_object* v_b_6113_, lean_object* v_c_6114_){
_start:
{
lean_object* v___x_6115_; 
v___x_6115_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6107_, v___x_6108_, v_fixedParamPerms_6109_, v_a_6112_, v_b_6113_);
return v___x_6115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6116_, lean_object* v___x_6117_, lean_object* v_fixedParamPerms_6118_, lean_object* v_inst_6119_, lean_object* v_R_6120_, lean_object* v_a_6121_, lean_object* v_b_6122_, lean_object* v_c_6123_){
_start:
{
lean_object* v_res_6124_; 
v_res_6124_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6116_, v___x_6117_, v_fixedParamPerms_6118_, v_inst_6119_, v_R_6120_, v_a_6121_, v_b_6122_, v_c_6123_);
lean_dec_ref(v_fixedParamPerms_6118_);
lean_dec_ref(v___x_6117_);
lean_dec(v_upperBound_6116_);
return v_res_6124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6125_, lean_object* v___x_6126_, lean_object* v_fixedParamPerms_6127_, lean_object* v_inst_6128_, lean_object* v_a_6129_){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6125_, v___x_6126_, v_fixedParamPerms_6127_, v_a_6129_);
return v___x_6130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6131_, lean_object* v___x_6132_, lean_object* v_fixedParamPerms_6133_, lean_object* v_inst_6134_, lean_object* v_a_6135_){
_start:
{
lean_object* v_res_6136_; 
v_res_6136_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6131_, v___x_6132_, v_fixedParamPerms_6133_, v_inst_6134_, v_a_6135_);
lean_dec_ref(v_fixedParamPerms_6133_);
lean_dec_ref(v___x_6132_);
lean_dec(v___x_6131_);
return v_res_6136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6137_, lean_object* v_inst_6138_, lean_object* v_R_6139_, lean_object* v_a_6140_, lean_object* v_b_6141_, lean_object* v_c_6142_){
_start:
{
lean_object* v___x_6143_; 
v___x_6143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6137_, v_a_6140_, v_b_6141_);
return v___x_6143_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6144_, lean_object* v_inst_6145_, lean_object* v_R_6146_, lean_object* v_a_6147_, lean_object* v_b_6148_, lean_object* v_c_6149_){
_start:
{
lean_object* v_res_6150_; 
v_res_6150_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6144_, v_inst_6145_, v_R_6146_, v_a_6147_, v_b_6148_, v_c_6149_);
lean_dec(v_upperBound_6144_);
return v_res_6150_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6151_, lean_object* v_inst_6152_, lean_object* v_R_6153_, lean_object* v_a_6154_, lean_object* v_b_6155_, lean_object* v_c_6156_){
_start:
{
lean_object* v___x_6157_; 
v___x_6157_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6151_, v_a_6154_, v_b_6155_);
return v___x_6157_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6158_, lean_object* v_inst_6159_, lean_object* v_R_6160_, lean_object* v_a_6161_, lean_object* v_b_6162_, lean_object* v_c_6163_){
_start:
{
lean_object* v_res_6164_; 
v_res_6164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6158_, v_inst_6159_, v_R_6160_, v_a_6161_, v_b_6162_, v_c_6163_);
lean_dec(v_upperBound_6158_);
return v_res_6164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6222_; uint8_t v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; 
v___x_6222_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6223_ = 0;
v___x_6224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6225_ = l_Lean_registerTraceClass(v___x_6222_, v___x_6223_, v___x_6224_);
return v___x_6225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6226_){
_start:
{
lean_object* v_res_6227_; 
v_res_6227_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6227_;
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
