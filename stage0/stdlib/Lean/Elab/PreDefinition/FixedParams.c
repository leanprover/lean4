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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "assertion violation: !( __do_lift._@.Lean.Elab.PreDefinition.FixedParams.75993854._hygCtx._hyg.102.0 ).hasLooseBVars\n        "};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: fixedParamIdx < xs.size\n        "};
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___closed__0;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_FixedParamPerms_erase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 41, .m_data = "assertion violation: xs.all (·.isFVar)\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__0 = (const lean_object*)&l_Lean_Elab_FixedParamPerms_erase___closed__0_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerms_erase___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__1;
static const lean_string_object l_Lean_Elab_FixedParamPerms_erase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "assertion violation: fixedParamPerms.numFixed  = xs.size\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__2 = (const lean_object*)&l_Lean_Elab_FixedParamPerms_erase___closed__2_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerms_erase___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__3;
static const lean_string_object l_Lean_Elab_FixedParamPerms_erase___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 134, .m_capacity = 134, .m_length = 133, .m_data = "assertion violation: toErase.size = fixedParamPerms.perms.size\n  -- Calculate a mask on the fixed parameters of variables to erase\n  "};
static const lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__4 = (const lean_object*)&l_Lean_Elab_FixedParamPerms_erase___closed__4_value;
static lean_once_cell_t l_Lean_Elab_FixedParamPerms_erase___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParamPerms_erase___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_681_; uint8_t v_fst_683_; lean_object* v_mctx_684_; lean_object* v_mctx_701_; lean_object* v___f_702_; lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___y_707_; uint8_t v___x_714_; uint8_t v___x_715_; 
v___x_681_ = lean_st_ref_get(v___y_679_);
v_mctx_701_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref_n(v_mctx_701_, 2);
lean_dec(v___x_681_);
v___f_702_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0));
v___f_703_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_703_, 0, v_fvarId_678_);
v___x_704_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_mctx_701_);
v___x_714_ = l_Lean_Expr_hasFVar(v_e_677_);
v___x_715_ = lean_bool_not(v___x_714_);
if (v___x_715_ == 0)
{
v___y_707_ = v___x_715_;
goto v___jp_706_;
}
else
{
uint8_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = l_Lean_Expr_hasMVar(v_e_677_);
v___x_717_ = lean_bool_not(v___x_716_);
v___y_707_ = v___x_717_;
goto v___jp_706_;
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
v___jp_706_:
{
if (v___y_707_ == 0)
{
lean_object* v___x_708_; lean_object* v_snd_709_; lean_object* v_fst_710_; lean_object* v_mctx_711_; uint8_t v___x_712_; 
lean_dec_ref(v_mctx_701_);
v___x_708_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_703_, v___f_702_, v_e_677_, v___x_705_);
v_snd_709_ = lean_ctor_get(v___x_708_, 1);
lean_inc(v_snd_709_);
v_fst_710_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_fst_710_);
lean_dec_ref(v___x_708_);
v_mctx_711_ = lean_ctor_get(v_snd_709_, 1);
lean_inc_ref(v_mctx_711_);
lean_dec(v_snd_709_);
v___x_712_ = lean_unbox(v_fst_710_);
lean_dec(v_fst_710_);
v_fst_683_ = v___x_712_;
v_mctx_684_ = v_mctx_711_;
goto v___jp_682_;
}
else
{
uint8_t v___x_713_; 
lean_dec_ref_known(v___x_705_, 2);
lean_dec_ref(v___f_703_);
lean_dec_ref(v_e_677_);
v___x_713_ = 0;
v_fst_683_ = v___x_713_;
v_mctx_684_ = v_mctx_701_;
goto v___jp_682_;
}
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
lean_object* v___f_1011_; lean_object* v___x_32928__overap_1012_; lean_object* v___x_1013_; 
v___f_1011_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_32928__overap_1012_ = lean_panic_fn_borrowed(v___f_1011_, v_msg_1005_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
v___x_1013_ = lean_apply_5(v___x_32928__overap_1012_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, lean_box(0));
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
v___x_1149_ = lean_st_ref_set(v___y_1110_, v___x_1148_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
if (lean_obj_tag(v_x_1185_) == 0)
{
return v_x_1184_;
}
else
{
lean_object* v_key_1186_; lean_object* v_value_1187_; lean_object* v_tail_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1211_; 
v_key_1186_ = lean_ctor_get(v_x_1185_, 0);
v_value_1187_ = lean_ctor_get(v_x_1185_, 1);
v_tail_1188_ = lean_ctor_get(v_x_1185_, 2);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_x_1185_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1190_ = v_x_1185_;
v_isShared_1191_ = v_isSharedCheck_1211_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_tail_1188_);
lean_inc(v_value_1187_);
lean_inc(v_key_1186_);
lean_dec(v_x_1185_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1211_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; uint64_t v___x_1193_; uint64_t v___x_1194_; uint64_t v___x_1195_; uint64_t v_fold_1196_; uint64_t v___x_1197_; uint64_t v___x_1198_; uint64_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1192_ = lean_array_get_size(v_x_1184_);
v___x_1193_ = l_Lean_ExprStructEq_hash(v_key_1186_);
v___x_1194_ = 32ULL;
v___x_1195_ = lean_uint64_shift_right(v___x_1193_, v___x_1194_);
v_fold_1196_ = lean_uint64_xor(v___x_1193_, v___x_1195_);
v___x_1197_ = 16ULL;
v___x_1198_ = lean_uint64_shift_right(v_fold_1196_, v___x_1197_);
v___x_1199_ = lean_uint64_xor(v_fold_1196_, v___x_1198_);
v___x_1200_ = lean_uint64_to_usize(v___x_1199_);
v___x_1201_ = lean_usize_of_nat(v___x_1192_);
v___x_1202_ = ((size_t)1ULL);
v___x_1203_ = lean_usize_sub(v___x_1201_, v___x_1202_);
v___x_1204_ = lean_usize_land(v___x_1200_, v___x_1203_);
v___x_1205_ = lean_array_uget_borrowed(v_x_1184_, v___x_1204_);
lean_inc(v___x_1205_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 2, v___x_1205_);
v___x_1207_ = v___x_1190_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_key_1186_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_value_1187_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_array_uset(v_x_1184_, v___x_1204_, v___x_1207_);
v_x_1184_ = v___x_1208_;
v_x_1185_ = v_tail_1188_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object* v_i_1212_, lean_object* v_source_1213_, lean_object* v_target_1214_){
_start:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_array_get_size(v_source_1213_);
v___x_1216_ = lean_nat_dec_lt(v_i_1212_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec_ref(v_source_1213_);
lean_dec(v_i_1212_);
return v_target_1214_;
}
else
{
lean_object* v_es_1217_; lean_object* v___x_1218_; lean_object* v_source_1219_; lean_object* v_target_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_es_1217_ = lean_array_fget(v_source_1213_, v_i_1212_);
v___x_1218_ = lean_box(0);
v_source_1219_ = lean_array_fset(v_source_1213_, v_i_1212_, v___x_1218_);
v_target_1220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_target_1214_, v_es_1217_);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_i_1212_, v___x_1221_);
lean_dec(v_i_1212_);
v_i_1212_ = v___x_1222_;
v_source_1213_ = v_source_1219_;
v_target_1214_ = v_target_1220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object* v_data_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_nbuckets_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1225_ = lean_array_get_size(v_data_1224_);
v___x_1226_ = lean_unsigned_to_nat(2u);
v_nbuckets_1227_ = lean_nat_mul(v___x_1225_, v___x_1226_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_mk_array(v_nbuckets_1227_, v___x_1229_);
v___x_1231_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1228_, v_data_1224_, v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object* v_a_1232_, lean_object* v_b_1233_, lean_object* v_x_1234_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
lean_dec(v_b_1233_);
lean_dec_ref(v_a_1232_);
return v_x_1234_;
}
else
{
lean_object* v_key_1235_; lean_object* v_value_1236_; lean_object* v_tail_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1249_; 
v_key_1235_ = lean_ctor_get(v_x_1234_, 0);
v_value_1236_ = lean_ctor_get(v_x_1234_, 1);
v_tail_1237_ = lean_ctor_get(v_x_1234_, 2);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1234_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1239_ = v_x_1234_;
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_tail_1237_);
lean_inc(v_value_1236_);
lean_inc(v_key_1235_);
lean_dec(v_x_1234_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
uint8_t v___x_1241_; 
v___x_1241_ = l_Lean_ExprStructEq_beq(v_key_1235_, v_a_1232_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1232_, v_b_1233_, v_tail_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 2, v___x_1242_);
v___x_1244_ = v___x_1239_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_key_1235_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_value_1236_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
else
{
lean_object* v___x_1247_; 
lean_dec(v_value_1236_);
lean_dec(v_key_1235_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v_b_1233_);
lean_ctor_set(v___x_1239_, 0, v_a_1232_);
v___x_1247_ = v___x_1239_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1232_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_b_1233_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_tail_1237_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_a_1250_, lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = 0;
return v___x_1252_;
}
else
{
lean_object* v_key_1253_; lean_object* v_tail_1254_; uint8_t v___x_1255_; 
v_key_1253_ = lean_ctor_get(v_x_1251_, 0);
v_tail_1254_ = lean_ctor_get(v_x_1251_, 2);
v___x_1255_ = l_Lean_ExprStructEq_beq(v_key_1253_, v_a_1250_);
if (v___x_1255_ == 0)
{
v_x_1251_ = v_tail_1254_;
goto _start;
}
else
{
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_a_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1257_, v_x_1258_);
lean_dec(v_x_1258_);
lean_dec_ref(v_a_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1261_, lean_object* v_a_1262_, lean_object* v_b_1263_){
_start:
{
lean_object* v_size_1264_; lean_object* v_buckets_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1308_; 
v_size_1264_ = lean_ctor_get(v_m_1261_, 0);
v_buckets_1265_ = lean_ctor_get(v_m_1261_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_m_1261_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1267_ = v_m_1261_;
v_isShared_1268_ = v_isSharedCheck_1308_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_buckets_1265_);
lean_inc(v_size_1264_);
lean_dec(v_m_1261_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1308_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v___x_1272_; uint64_t v_fold_1273_; uint64_t v___x_1274_; uint64_t v___x_1275_; uint64_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; lean_object* v_bkt_1282_; uint8_t v___x_1283_; 
v___x_1269_ = lean_array_get_size(v_buckets_1265_);
v___x_1270_ = l_Lean_ExprStructEq_hash(v_a_1262_);
v___x_1271_ = 32ULL;
v___x_1272_ = lean_uint64_shift_right(v___x_1270_, v___x_1271_);
v_fold_1273_ = lean_uint64_xor(v___x_1270_, v___x_1272_);
v___x_1274_ = 16ULL;
v___x_1275_ = lean_uint64_shift_right(v_fold_1273_, v___x_1274_);
v___x_1276_ = lean_uint64_xor(v_fold_1273_, v___x_1275_);
v___x_1277_ = lean_uint64_to_usize(v___x_1276_);
v___x_1278_ = lean_usize_of_nat(v___x_1269_);
v___x_1279_ = ((size_t)1ULL);
v___x_1280_ = lean_usize_sub(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_usize_land(v___x_1277_, v___x_1280_);
v_bkt_1282_ = lean_array_uget_borrowed(v_buckets_1265_, v___x_1281_);
v___x_1283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1262_, v_bkt_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; lean_object* v_size_x27_1285_; lean_object* v___x_1286_; lean_object* v_buckets_x27_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1284_ = lean_unsigned_to_nat(1u);
v_size_x27_1285_ = lean_nat_add(v_size_1264_, v___x_1284_);
lean_dec(v_size_1264_);
lean_inc(v_bkt_1282_);
v___x_1286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1286_, 0, v_a_1262_);
lean_ctor_set(v___x_1286_, 1, v_b_1263_);
lean_ctor_set(v___x_1286_, 2, v_bkt_1282_);
v_buckets_x27_1287_ = lean_array_uset(v_buckets_1265_, v___x_1281_, v___x_1286_);
v___x_1288_ = lean_unsigned_to_nat(4u);
v___x_1289_ = lean_nat_mul(v_size_x27_1285_, v___x_1288_);
v___x_1290_ = lean_unsigned_to_nat(3u);
v___x_1291_ = lean_nat_div(v___x_1289_, v___x_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_array_get_size(v_buckets_x27_1287_);
v___x_1293_ = lean_nat_dec_le(v___x_1291_, v___x_1292_);
lean_dec(v___x_1291_);
if (v___x_1293_ == 0)
{
lean_object* v_val_1294_; lean_object* v___x_1296_; 
v_val_1294_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_buckets_x27_1287_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v_val_1294_);
lean_ctor_set(v___x_1267_, 0, v_size_x27_1285_);
v___x_1296_ = v___x_1267_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_size_x27_1285_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_val_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
else
{
lean_object* v___x_1299_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v_buckets_x27_1287_);
lean_ctor_set(v___x_1267_, 0, v_size_x27_1285_);
v___x_1299_ = v___x_1267_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_size_x27_1285_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_buckets_x27_1287_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v___x_1301_; lean_object* v_buckets_x27_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
lean_inc(v_bkt_1282_);
v___x_1301_ = lean_box(0);
v_buckets_x27_1302_ = lean_array_uset(v_buckets_1265_, v___x_1281_, v___x_1301_);
v___x_1303_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1262_, v_b_1263_, v_bkt_1282_);
v___x_1304_ = lean_array_uset(v_buckets_x27_1302_, v___x_1281_, v___x_1303_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v___x_1304_);
v___x_1306_ = v___x_1267_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_size_1264_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1309_, lean_object* v_e_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1313_ = lean_st_ref_take(v_a_1309_);
v___x_1314_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1313_, v_e_1310_, v_a_1311_);
v___x_1315_ = lean_st_ref_set(v_a_1309_, v___x_1314_);
v___x_1316_ = lean_box(0);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1317_, lean_object* v_e_1318_, lean_object* v_a_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1317_, v_e_1318_, v_a_1319_);
lean_dec(v_a_1317_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1322_, lean_object* v___y_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; 
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
lean_inc(v___y_1323_);
v___x_1330_ = lean_apply_7(v_k_1322_, v_b_1324_, v___y_1323_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, lean_box(0));
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1331_, lean_object* v___y_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1331_, v___y_1332_, v_b_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1332_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1340_, uint8_t v_bi_1341_, lean_object* v_type_1342_, lean_object* v_k_1343_, uint8_t v_kind_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___f_1351_; lean_object* v___x_1352_; 
lean_inc(v___y_1345_);
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1351_, 0, v_k_1343_);
lean_closure_set(v___f_1351_, 1, v___y_1345_);
v___x_1352_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1340_, v_bi_1341_, v_type_1342_, v___f_1351_, v_kind_1344_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1352_) == 0)
{
return v___x_1352_;
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1361_, lean_object* v_bi_1362_, lean_object* v_type_1363_, lean_object* v_k_1364_, lean_object* v_kind_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v_bi_boxed_1372_; uint8_t v_kind_boxed_1373_; lean_object* v_res_1374_; 
v_bi_boxed_1372_ = lean_unbox(v_bi_1362_);
v_kind_boxed_1373_ = lean_unbox(v_kind_1365_);
v_res_1374_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1361_, v_bi_boxed_1372_, v_type_1363_, v_k_1364_, v_kind_boxed_1373_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object* v___x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1375_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object* v___x_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1389_, lean_object* v_type_1390_, lean_object* v_val_1391_, lean_object* v_k_1392_, uint8_t v_nondep_1393_, uint8_t v_kind_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___f_1401_; lean_object* v___x_1402_; 
lean_inc(v___y_1395_);
v___f_1401_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1401_, 0, v_k_1392_);
lean_closure_set(v___f_1401_, 1, v___y_1395_);
v___x_1402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1389_, v_type_1390_, v_val_1391_, v___f_1401_, v_nondep_1393_, v_kind_1394_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1402_) == 0)
{
return v___x_1402_;
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1411_, lean_object* v_type_1412_, lean_object* v_val_1413_, lean_object* v_k_1414_, lean_object* v_nondep_1415_, lean_object* v_kind_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
uint8_t v_nondep_boxed_1423_; uint8_t v_kind_boxed_1424_; lean_object* v_res_1425_; 
v_nondep_boxed_1423_ = lean_unbox(v_nondep_1415_);
v_kind_boxed_1424_ = lean_unbox(v_kind_1416_);
v_res_1425_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1411_, v_type_1412_, v_val_1413_, v_k_1414_, v_nondep_boxed_1423_, v_kind_boxed_1424_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_apply_1(v_x_1427_, lean_box(0));
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_x_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1435_, v_x_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
return v_res_1442_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = l_Lean_maxRecDepthErrorMessage;
v___x_1449_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1451_ = l_Lean_MessageData_ofFormat(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1453_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1454_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
lean_ctor_set(v___x_1454_, 1, v___x_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_ref_1455_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___y_1471_; lean_object* v_fileName_1480_; lean_object* v_fileMap_1481_; lean_object* v_options_1482_; lean_object* v_currRecDepth_1483_; lean_object* v_maxRecDepth_1484_; lean_object* v_ref_1485_; lean_object* v_currNamespace_1486_; lean_object* v_openDecls_1487_; lean_object* v_initHeartbeats_1488_; lean_object* v_maxHeartbeats_1489_; lean_object* v_quotContext_1490_; lean_object* v_currMacroScope_1491_; uint8_t v_diag_1492_; lean_object* v_cancelTk_x3f_1493_; uint8_t v_suppressElabErrors_1494_; lean_object* v_inheritedTraceOptions_1495_; uint8_t v___y_1497_; lean_object* v___x_1503_; uint8_t v___x_1504_; uint8_t v___x_1505_; 
v_fileName_1480_ = lean_ctor_get(v___y_1467_, 0);
v_fileMap_1481_ = lean_ctor_get(v___y_1467_, 1);
v_options_1482_ = lean_ctor_get(v___y_1467_, 2);
v_currRecDepth_1483_ = lean_ctor_get(v___y_1467_, 3);
v_maxRecDepth_1484_ = lean_ctor_get(v___y_1467_, 4);
v_ref_1485_ = lean_ctor_get(v___y_1467_, 5);
v_currNamespace_1486_ = lean_ctor_get(v___y_1467_, 6);
v_openDecls_1487_ = lean_ctor_get(v___y_1467_, 7);
v_initHeartbeats_1488_ = lean_ctor_get(v___y_1467_, 8);
v_maxHeartbeats_1489_ = lean_ctor_get(v___y_1467_, 9);
v_quotContext_1490_ = lean_ctor_get(v___y_1467_, 10);
v_currMacroScope_1491_ = lean_ctor_get(v___y_1467_, 11);
v_diag_1492_ = lean_ctor_get_uint8(v___y_1467_, sizeof(void*)*14);
v_cancelTk_x3f_1493_ = lean_ctor_get(v___y_1467_, 12);
v_suppressElabErrors_1494_ = lean_ctor_get_uint8(v___y_1467_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1495_ = lean_ctor_get(v___y_1467_, 13);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_nat_dec_eq(v_maxRecDepth_1484_, v___x_1503_);
v___x_1505_ = lean_bool_not(v___x_1504_);
if (v___x_1505_ == 0)
{
v___y_1497_ = v___x_1505_;
goto v___jp_1496_;
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_nat_dec_eq(v_currRecDepth_1483_, v_maxRecDepth_1484_);
v___y_1497_ = v___x_1506_;
goto v___jp_1496_;
}
v___jp_1470_:
{
if (lean_obj_tag(v___y_1471_) == 0)
{
return v___y_1471_;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___y_1471_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___y_1471_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___y_1471_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___y_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
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
v___jp_1496_:
{
if (v___y_1497_ == 0)
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_add(v_currRecDepth_1483_, v___x_1498_);
lean_inc_ref(v_inheritedTraceOptions_1495_);
lean_inc(v_cancelTk_x3f_1493_);
lean_inc(v_currMacroScope_1491_);
lean_inc(v_quotContext_1490_);
lean_inc(v_maxHeartbeats_1489_);
lean_inc(v_initHeartbeats_1488_);
lean_inc(v_openDecls_1487_);
lean_inc(v_currNamespace_1486_);
lean_inc(v_ref_1485_);
lean_inc(v_maxRecDepth_1484_);
lean_inc_ref(v_options_1482_);
lean_inc_ref(v_fileMap_1481_);
lean_inc_ref(v_fileName_1480_);
v___x_1500_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1500_, 0, v_fileName_1480_);
lean_ctor_set(v___x_1500_, 1, v_fileMap_1481_);
lean_ctor_set(v___x_1500_, 2, v_options_1482_);
lean_ctor_set(v___x_1500_, 3, v___x_1499_);
lean_ctor_set(v___x_1500_, 4, v_maxRecDepth_1484_);
lean_ctor_set(v___x_1500_, 5, v_ref_1485_);
lean_ctor_set(v___x_1500_, 6, v_currNamespace_1486_);
lean_ctor_set(v___x_1500_, 7, v_openDecls_1487_);
lean_ctor_set(v___x_1500_, 8, v_initHeartbeats_1488_);
lean_ctor_set(v___x_1500_, 9, v_maxHeartbeats_1489_);
lean_ctor_set(v___x_1500_, 10, v_quotContext_1490_);
lean_ctor_set(v___x_1500_, 11, v_currMacroScope_1491_);
lean_ctor_set(v___x_1500_, 12, v_cancelTk_x3f_1493_);
lean_ctor_set(v___x_1500_, 13, v_inheritedTraceOptions_1495_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*14, v_diag_1492_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*14 + 1, v_suppressElabErrors_1494_);
lean_inc(v___y_1468_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
v___x_1501_ = lean_apply_6(v_x_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___x_1500_, v___y_1468_, lean_box(0));
v___y_1471_ = v___x_1501_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1502_; 
lean_dec_ref(v_x_1463_);
lean_inc(v_ref_1485_);
v___x_1502_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1485_);
v___y_1471_ = v___x_1502_;
goto v___jp_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1515_, lean_object* v_x_1516_){
_start:
{
if (lean_obj_tag(v_x_1516_) == 0)
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_box(0);
return v___x_1517_;
}
else
{
lean_object* v_key_1518_; lean_object* v_value_1519_; lean_object* v_tail_1520_; uint8_t v___x_1521_; 
v_key_1518_ = lean_ctor_get(v_x_1516_, 0);
v_value_1519_ = lean_ctor_get(v_x_1516_, 1);
v_tail_1520_ = lean_ctor_get(v_x_1516_, 2);
v___x_1521_ = l_Lean_ExprStructEq_beq(v_key_1518_, v_a_1515_);
if (v___x_1521_ == 0)
{
v_x_1516_ = v_tail_1520_;
goto _start;
}
else
{
lean_object* v___x_1523_; 
lean_inc(v_value_1519_);
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_value_1519_);
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1524_, lean_object* v_x_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1524_, v_x_1525_);
lean_dec(v_x_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v_buckets_1529_; lean_object* v___x_1530_; uint64_t v___x_1531_; uint64_t v___x_1532_; uint64_t v___x_1533_; uint64_t v_fold_1534_; uint64_t v___x_1535_; uint64_t v___x_1536_; uint64_t v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_buckets_1529_ = lean_ctor_get(v_m_1527_, 1);
v___x_1530_ = lean_array_get_size(v_buckets_1529_);
v___x_1531_ = l_Lean_ExprStructEq_hash(v_a_1528_);
v___x_1532_ = 32ULL;
v___x_1533_ = lean_uint64_shift_right(v___x_1531_, v___x_1532_);
v_fold_1534_ = lean_uint64_xor(v___x_1531_, v___x_1533_);
v___x_1535_ = 16ULL;
v___x_1536_ = lean_uint64_shift_right(v_fold_1534_, v___x_1535_);
v___x_1537_ = lean_uint64_xor(v_fold_1534_, v___x_1536_);
v___x_1538_ = lean_uint64_to_usize(v___x_1537_);
v___x_1539_ = lean_usize_of_nat(v___x_1530_);
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_sub(v___x_1539_, v___x_1540_);
v___x_1542_ = lean_usize_land(v___x_1538_, v___x_1541_);
v___x_1543_ = lean_array_uget_borrowed(v_buckets_1529_, v___x_1542_);
v___x_1544_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1528_, v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1545_, v_a_1546_);
lean_dec_ref(v_a_1546_);
lean_dec_ref(v_m_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1551_, lean_object* v_pre_1552_, lean_object* v_post_1553_, uint8_t v_usedLetOnly_1554_, uint8_t v_skipConstInApp_1555_, uint8_t v_skipInstances_1556_, lean_object* v_body_1557_, lean_object* v_x_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_array_push(v_fvars_1551_, v_x_1558_);
v___x_1566_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1552_, v_post_1553_, v_usedLetOnly_1554_, v_skipConstInApp_1555_, v_skipInstances_1556_, v___x_1565_, v_body_1557_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1567_, lean_object* v_pre_1568_, lean_object* v_post_1569_, lean_object* v_usedLetOnly_1570_, lean_object* v_skipConstInApp_1571_, lean_object* v_skipInstances_1572_, lean_object* v_body_1573_, lean_object* v_x_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v_usedLetOnly_boxed_1581_; uint8_t v_skipConstInApp_boxed_1582_; uint8_t v_skipInstances_boxed_1583_; lean_object* v_res_1584_; 
v_usedLetOnly_boxed_1581_ = lean_unbox(v_usedLetOnly_1570_);
v_skipConstInApp_boxed_1582_ = lean_unbox(v_skipConstInApp_1571_);
v_skipInstances_boxed_1583_ = lean_unbox(v_skipInstances_1572_);
v_res_1584_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1567_, v_pre_1568_, v_post_1569_, v_usedLetOnly_boxed_1581_, v_skipConstInApp_boxed_1582_, v_skipInstances_boxed_1583_, v_body_1573_, v_x_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1585_, lean_object* v_post_1586_, uint8_t v_usedLetOnly_1587_, uint8_t v_skipConstInApp_1588_, uint8_t v_skipInstances_1589_, lean_object* v_e_1590_, lean_object* v_a_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
lean_inc_ref(v_post_1586_);
lean_inc(v___y_1595_);
lean_inc_ref(v___y_1594_);
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc_ref(v_e_1590_);
v___x_1597_ = lean_apply_6(v_post_1586_, v_e_1590_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, lean_box(0));
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1616_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1616_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1616_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
switch(lean_obj_tag(v_a_1598_))
{
case 0:
{
lean_object* v_e_1602_; lean_object* v___x_1604_; 
lean_dec_ref(v_e_1590_);
lean_dec_ref(v_post_1586_);
lean_dec_ref(v_pre_1585_);
v_e_1602_ = lean_ctor_get(v_a_1598_, 0);
lean_inc_ref(v_e_1602_);
lean_dec_ref_known(v_a_1598_, 1);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_e_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_e_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
case 1:
{
lean_object* v_e_1606_; lean_object* v___x_1607_; 
lean_del_object(v___x_1600_);
lean_dec_ref(v_e_1590_);
v_e_1606_ = lean_ctor_get(v_a_1598_, 0);
lean_inc_ref(v_e_1606_);
lean_dec_ref_known(v_a_1598_, 1);
v___x_1607_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1585_, v_post_1586_, v_usedLetOnly_1587_, v_skipConstInApp_1588_, v_skipInstances_1589_, v_e_1606_, v_a_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1607_;
}
default: 
{
lean_object* v_e_x3f_1608_; 
lean_dec_ref(v_post_1586_);
lean_dec_ref(v_pre_1585_);
v_e_x3f_1608_ = lean_ctor_get(v_a_1598_, 0);
lean_inc(v_e_x3f_1608_);
lean_dec_ref_known(v_a_1598_, 1);
if (lean_obj_tag(v_e_x3f_1608_) == 0)
{
lean_object* v___x_1610_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_e_1590_);
v___x_1610_ = v___x_1600_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_e_1590_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v_val_1612_; lean_object* v___x_1614_; 
lean_dec_ref(v_e_1590_);
v_val_1612_ = lean_ctor_get(v_e_x3f_1608_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v_e_x3f_1608_, 1);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v_val_1612_);
v___x_1614_ = v___x_1600_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_val_1612_);
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
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_e_1590_);
lean_dec_ref(v_post_1586_);
lean_dec_ref(v_pre_1585_);
v_a_1617_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1597_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1597_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1625_, lean_object* v_post_1626_, uint8_t v_usedLetOnly_1627_, uint8_t v_skipConstInApp_1628_, uint8_t v_skipInstances_1629_, lean_object* v_fvars_1630_, lean_object* v_e_1631_, lean_object* v_a_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
if (lean_obj_tag(v_e_1631_) == 6)
{
lean_object* v_binderName_1638_; lean_object* v_binderType_1639_; lean_object* v_body_1640_; uint8_t v_binderInfo_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_binderName_1638_ = lean_ctor_get(v_e_1631_, 0);
lean_inc(v_binderName_1638_);
v_binderType_1639_ = lean_ctor_get(v_e_1631_, 1);
lean_inc_ref(v_binderType_1639_);
v_body_1640_ = lean_ctor_get(v_e_1631_, 2);
lean_inc_ref(v_body_1640_);
v_binderInfo_1641_ = lean_ctor_get_uint8(v_e_1631_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1631_, 3);
v___x_1642_ = lean_expr_instantiate_rev(v_binderType_1639_, v_fvars_1630_);
lean_dec_ref(v_binderType_1639_);
lean_inc_ref(v_post_1626_);
lean_inc_ref(v_pre_1625_);
v___x_1643_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1625_, v_post_1626_, v_usedLetOnly_1627_, v_skipConstInApp_1628_, v_skipInstances_1629_, v___x_1642_, v_a_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___f_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = lean_box(v_usedLetOnly_1627_);
v___x_1646_ = lean_box(v_skipConstInApp_1628_);
v___x_1647_ = lean_box(v_skipInstances_1629_);
v___f_1648_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1648_, 0, v_fvars_1630_);
lean_closure_set(v___f_1648_, 1, v_pre_1625_);
lean_closure_set(v___f_1648_, 2, v_post_1626_);
lean_closure_set(v___f_1648_, 3, v___x_1645_);
lean_closure_set(v___f_1648_, 4, v___x_1646_);
lean_closure_set(v___f_1648_, 5, v___x_1647_);
lean_closure_set(v___f_1648_, 6, v_body_1640_);
v___x_1649_ = 0;
v___x_1650_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1638_, v_binderInfo_1641_, v_a_1644_, v___f_1648_, v___x_1649_, v_a_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1650_;
}
else
{
lean_dec_ref(v_body_1640_);
lean_dec(v_binderName_1638_);
lean_dec_ref(v_fvars_1630_);
lean_dec_ref(v_post_1626_);
lean_dec_ref(v_pre_1625_);
return v___x_1643_;
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_expr_instantiate_rev(v_e_1631_, v_fvars_1630_);
lean_dec_ref(v_e_1631_);
lean_inc_ref(v_post_1626_);
lean_inc_ref(v_pre_1625_);
v___x_1652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1625_, v_post_1626_, v_usedLetOnly_1627_, v_skipConstInApp_1628_, v_skipInstances_1629_, v___x_1651_, v_a_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; uint8_t v___x_1654_; uint8_t v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = 0;
v___x_1655_ = 1;
v___x_1656_ = 1;
v___x_1657_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1630_, v_a_1653_, v___x_1654_, v_usedLetOnly_1627_, v___x_1654_, v___x_1655_, v___x_1656_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec_ref(v_fvars_1630_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1625_, v_post_1626_, v_usedLetOnly_1627_, v_skipConstInApp_1628_, v_skipInstances_1629_, v_a_1658_, v_a_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1659_;
}
else
{
lean_dec_ref(v_post_1626_);
lean_dec_ref(v_pre_1625_);
return v___x_1657_;
}
}
else
{
lean_dec_ref(v_fvars_1630_);
lean_dec_ref(v_post_1626_);
lean_dec_ref(v_pre_1625_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1660_, lean_object* v_pre_1661_, lean_object* v_post_1662_, uint8_t v_usedLetOnly_1663_, uint8_t v_skipConstInApp_1664_, uint8_t v_skipInstances_1665_, lean_object* v_body_1666_, lean_object* v_x_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_array_push(v_fvars_1660_, v_x_1667_);
v___x_1675_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1661_, v_post_1662_, v_usedLetOnly_1663_, v_skipConstInApp_1664_, v_skipInstances_1665_, v___x_1674_, v_body_1666_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1676_, lean_object* v_pre_1677_, lean_object* v_post_1678_, lean_object* v_usedLetOnly_1679_, lean_object* v_skipConstInApp_1680_, lean_object* v_skipInstances_1681_, lean_object* v_body_1682_, lean_object* v_x_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
uint8_t v_usedLetOnly_boxed_1690_; uint8_t v_skipConstInApp_boxed_1691_; uint8_t v_skipInstances_boxed_1692_; lean_object* v_res_1693_; 
v_usedLetOnly_boxed_1690_ = lean_unbox(v_usedLetOnly_1679_);
v_skipConstInApp_boxed_1691_ = lean_unbox(v_skipConstInApp_1680_);
v_skipInstances_boxed_1692_ = lean_unbox(v_skipInstances_1681_);
v_res_1693_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1676_, v_pre_1677_, v_post_1678_, v_usedLetOnly_boxed_1690_, v_skipConstInApp_boxed_1691_, v_skipInstances_boxed_1692_, v_body_1682_, v_x_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1694_, lean_object* v_post_1695_, uint8_t v_usedLetOnly_1696_, uint8_t v_skipConstInApp_1697_, uint8_t v_skipInstances_1698_, lean_object* v_fvars_1699_, lean_object* v_e_1700_, lean_object* v_a_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
if (lean_obj_tag(v_e_1700_) == 8)
{
lean_object* v_declName_1707_; lean_object* v_type_1708_; lean_object* v_value_1709_; lean_object* v_body_1710_; uint8_t v_nondep_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_declName_1707_ = lean_ctor_get(v_e_1700_, 0);
lean_inc(v_declName_1707_);
v_type_1708_ = lean_ctor_get(v_e_1700_, 1);
lean_inc_ref(v_type_1708_);
v_value_1709_ = lean_ctor_get(v_e_1700_, 2);
lean_inc_ref(v_value_1709_);
v_body_1710_ = lean_ctor_get(v_e_1700_, 3);
lean_inc_ref(v_body_1710_);
v_nondep_1711_ = lean_ctor_get_uint8(v_e_1700_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1700_, 4);
v___x_1712_ = lean_expr_instantiate_rev(v_type_1708_, v_fvars_1699_);
lean_dec_ref(v_type_1708_);
lean_inc_ref(v_post_1695_);
lean_inc_ref(v_pre_1694_);
v___x_1713_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1694_, v_post_1695_, v_usedLetOnly_1696_, v_skipConstInApp_1697_, v_skipInstances_1698_, v___x_1712_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = lean_expr_instantiate_rev(v_value_1709_, v_fvars_1699_);
lean_dec_ref(v_value_1709_);
lean_inc_ref(v_post_1695_);
lean_inc_ref(v_pre_1694_);
v___x_1716_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1694_, v_post_1695_, v_usedLetOnly_1696_, v_skipConstInApp_1697_, v_skipInstances_1698_, v___x_1715_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = lean_box(v_usedLetOnly_1696_);
v___x_1719_ = lean_box(v_skipConstInApp_1697_);
v___x_1720_ = lean_box(v_skipInstances_1698_);
v___f_1721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1721_, 0, v_fvars_1699_);
lean_closure_set(v___f_1721_, 1, v_pre_1694_);
lean_closure_set(v___f_1721_, 2, v_post_1695_);
lean_closure_set(v___f_1721_, 3, v___x_1718_);
lean_closure_set(v___f_1721_, 4, v___x_1719_);
lean_closure_set(v___f_1721_, 5, v___x_1720_);
lean_closure_set(v___f_1721_, 6, v_body_1710_);
v___x_1722_ = 0;
v___x_1723_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1707_, v_a_1714_, v_a_1717_, v___f_1721_, v_nondep_1711_, v___x_1722_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1723_;
}
else
{
lean_dec(v_a_1714_);
lean_dec_ref(v_body_1710_);
lean_dec(v_declName_1707_);
lean_dec_ref(v_fvars_1699_);
lean_dec_ref(v_post_1695_);
lean_dec_ref(v_pre_1694_);
return v___x_1716_;
}
}
else
{
lean_dec_ref(v_body_1710_);
lean_dec_ref(v_value_1709_);
lean_dec(v_declName_1707_);
lean_dec_ref(v_fvars_1699_);
lean_dec_ref(v_post_1695_);
lean_dec_ref(v_pre_1694_);
return v___x_1713_;
}
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_expr_instantiate_rev(v_e_1700_, v_fvars_1699_);
lean_dec_ref(v_e_1700_);
lean_inc_ref(v_post_1695_);
lean_inc_ref(v_pre_1694_);
v___x_1725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1694_, v_post_1695_, v_usedLetOnly_1696_, v_skipConstInApp_1697_, v_skipInstances_1698_, v___x_1724_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; uint8_t v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = 0;
v___x_1728_ = 1;
v___x_1729_ = l_Lean_Meta_mkLetFVars(v_fvars_1699_, v_a_1726_, v_usedLetOnly_1696_, v___x_1727_, v___x_1728_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec_ref(v_fvars_1699_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1694_, v_post_1695_, v_usedLetOnly_1696_, v_skipConstInApp_1697_, v_skipInstances_1698_, v_a_1730_, v_a_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1731_;
}
else
{
lean_dec_ref(v_post_1695_);
lean_dec_ref(v_pre_1694_);
return v___x_1729_;
}
}
else
{
lean_dec_ref(v_fvars_1699_);
lean_dec_ref(v_post_1695_);
lean_dec_ref(v_pre_1694_);
return v___x_1725_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1732_; lean_object* v_dummy_1733_; 
v___x_1732_ = lean_box(0);
v_dummy_1733_ = l_Lean_Expr_sort___override(v___x_1732_);
return v_dummy_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1734_, lean_object* v_post_1735_, uint8_t v_usedLetOnly_1736_, uint8_t v_skipConstInApp_1737_, uint8_t v_skipInstances_1738_, size_t v_sz_1739_, size_t v_i_1740_, lean_object* v_bs_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_usize_dec_lt(v_i_1740_, v_sz_1739_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; 
lean_dec_ref(v_post_1735_);
lean_dec_ref(v_pre_1734_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_bs_1741_);
return v___x_1749_;
}
else
{
lean_object* v_v_1750_; lean_object* v___x_1751_; 
v_v_1750_ = lean_array_uget_borrowed(v_bs_1741_, v_i_1740_);
lean_inc(v_v_1750_);
lean_inc_ref(v_post_1735_);
lean_inc_ref(v_pre_1734_);
v___x_1751_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1734_, v_post_1735_, v_usedLetOnly_1736_, v_skipConstInApp_1737_, v_skipInstances_1738_, v_v_1750_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v_bs_x27_1754_; size_t v___x_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = lean_unsigned_to_nat(0u);
v_bs_x27_1754_ = lean_array_uset(v_bs_1741_, v_i_1740_, v___x_1753_);
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1740_, v___x_1755_);
v___x_1757_ = lean_array_uset(v_bs_x27_1754_, v_i_1740_, v_a_1752_);
v_i_1740_ = v___x_1756_;
v_bs_1741_ = v___x_1757_;
goto _start;
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec_ref(v_bs_1741_);
lean_dec_ref(v_post_1735_);
lean_dec_ref(v_pre_1734_);
v_a_1759_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1751_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1751_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1767_, lean_object* v_post_1768_, uint8_t v_usedLetOnly_1769_, uint8_t v_skipConstInApp_1770_, uint8_t v_skipInstances_1771_, lean_object* v___x_1772_, lean_object* v___y_1773_, lean_object* v_b_1774_, lean_object* v_a_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1767_, v_post_1768_, v_usedLetOnly_1769_, v_skipConstInApp_1770_, v_skipInstances_1771_, v___x_1772_, v___y_1773_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1791_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1791_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1786_ = lean_array_fset(v_b_1774_, v_a_1775_, v_a_1782_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1787_);
v___x_1789_ = v___x_1784_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec_ref(v_b_1774_);
v_a_1792_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1781_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1781_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1800_, lean_object* v_post_1801_, lean_object* v_usedLetOnly_1802_, lean_object* v_skipConstInApp_1803_, lean_object* v_skipInstances_1804_, lean_object* v___x_1805_, lean_object* v___y_1806_, lean_object* v_b_1807_, lean_object* v_a_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v_usedLetOnly_boxed_1814_; uint8_t v_skipConstInApp_boxed_1815_; uint8_t v_skipInstances_boxed_1816_; lean_object* v_res_1817_; 
v_usedLetOnly_boxed_1814_ = lean_unbox(v_usedLetOnly_1802_);
v_skipConstInApp_boxed_1815_ = lean_unbox(v_skipConstInApp_1803_);
v_skipInstances_boxed_1816_ = lean_unbox(v_skipInstances_1804_);
v_res_1817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1800_, v_post_1801_, v_usedLetOnly_boxed_1814_, v_skipConstInApp_boxed_1815_, v_skipInstances_boxed_1816_, v___x_1805_, v___y_1806_, v_b_1807_, v_a_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v_a_1808_);
lean_dec(v___y_1806_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1818_, lean_object* v___x_1819_, lean_object* v_pre_1820_, lean_object* v_post_1821_, uint8_t v_usedLetOnly_1822_, uint8_t v_skipConstInApp_1823_, uint8_t v_skipInstances_1824_, lean_object* v_a_1825_, lean_object* v_b_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v___y_1834_; uint8_t v___x_1857_; 
v___x_1857_ = lean_nat_dec_lt(v_a_1825_, v_upperBound_1818_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_dec(v_a_1825_);
lean_dec_ref(v_post_1821_);
lean_dec_ref(v_pre_1820_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_b_1826_);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1859_ = lean_array_fget_borrowed(v_b_1826_, v_a_1825_);
v___x_1860_ = lean_array_get_size(v___x_1819_);
v___x_1861_ = lean_nat_dec_lt(v_a_1825_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___f_1865_; 
lean_inc(v___x_1859_);
v___x_1862_ = lean_box(v_usedLetOnly_1822_);
v___x_1863_ = lean_box(v_skipConstInApp_1823_);
v___x_1864_ = lean_box(v_skipInstances_1824_);
lean_inc(v_a_1825_);
lean_inc(v___y_1827_);
lean_inc_ref(v_post_1821_);
lean_inc_ref(v_pre_1820_);
v___f_1865_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1865_, 0, v_pre_1820_);
lean_closure_set(v___f_1865_, 1, v_post_1821_);
lean_closure_set(v___f_1865_, 2, v___x_1862_);
lean_closure_set(v___f_1865_, 3, v___x_1863_);
lean_closure_set(v___f_1865_, 4, v___x_1864_);
lean_closure_set(v___f_1865_, 5, v___x_1859_);
lean_closure_set(v___f_1865_, 6, v___y_1827_);
lean_closure_set(v___f_1865_, 7, v_b_1826_);
lean_closure_set(v___f_1865_, 8, v_a_1825_);
v___y_1834_ = v___f_1865_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1866_; uint8_t v_isInstance_1867_; 
v___x_1866_ = lean_array_fget_borrowed(v___x_1819_, v_a_1825_);
v_isInstance_1867_ = lean_ctor_get_uint8(v___x_1866_, sizeof(void*)*1 + 4);
if (v_isInstance_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___f_1871_; 
lean_inc(v___x_1859_);
v___x_1868_ = lean_box(v_usedLetOnly_1822_);
v___x_1869_ = lean_box(v_skipConstInApp_1823_);
v___x_1870_ = lean_box(v_skipInstances_1824_);
lean_inc(v_a_1825_);
lean_inc(v___y_1827_);
lean_inc_ref(v_post_1821_);
lean_inc_ref(v_pre_1820_);
v___f_1871_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1871_, 0, v_pre_1820_);
lean_closure_set(v___f_1871_, 1, v_post_1821_);
lean_closure_set(v___f_1871_, 2, v___x_1868_);
lean_closure_set(v___f_1871_, 3, v___x_1869_);
lean_closure_set(v___f_1871_, 4, v___x_1870_);
lean_closure_set(v___f_1871_, 5, v___x_1859_);
lean_closure_set(v___f_1871_, 6, v___y_1827_);
lean_closure_set(v___f_1871_, 7, v_b_1826_);
lean_closure_set(v___f_1871_, 8, v_a_1825_);
v___y_1834_ = v___f_1871_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1872_; lean_object* v___f_1873_; 
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_b_1826_);
v___f_1873_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1873_, 0, v___x_1872_);
v___y_1834_ = v___f_1873_;
goto v___jp_1833_;
}
}
}
v___jp_1833_:
{
lean_object* v___x_1835_; 
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
v___x_1835_ = lean_apply_5(v___y_1834_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, lean_box(0));
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1848_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1848_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1848_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
if (lean_obj_tag(v_a_1836_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; 
lean_dec(v_a_1825_);
lean_dec_ref(v_post_1821_);
lean_dec_ref(v_pre_1820_);
v_a_1840_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v_a_1836_, 1);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v_a_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_del_object(v___x_1838_);
v_a_1844_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v_a_1836_, 1);
v___x_1845_ = lean_unsigned_to_nat(1u);
v___x_1846_ = lean_nat_add(v_a_1825_, v___x_1845_);
lean_dec(v_a_1825_);
v_a_1825_ = v___x_1846_;
v_b_1826_ = v_a_1844_;
goto _start;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1825_);
lean_dec_ref(v_post_1821_);
lean_dec_ref(v_pre_1820_);
v_a_1849_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1835_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1835_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1874_, lean_object* v_pre_1875_, lean_object* v_post_1876_, uint8_t v_usedLetOnly_1877_, uint8_t v_skipConstInApp_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_f_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; 
if (lean_obj_tag(v_x_1879_) == 5)
{
lean_object* v_fn_1937_; lean_object* v_arg_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_fn_1937_ = lean_ctor_get(v_x_1879_, 0);
lean_inc_ref(v_fn_1937_);
v_arg_1938_ = lean_ctor_get(v_x_1879_, 1);
lean_inc_ref(v_arg_1938_);
lean_dec_ref_known(v_x_1879_, 2);
v___x_1939_ = lean_array_set(v_x_1880_, v_x_1881_, v_arg_1938_);
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_sub(v_x_1881_, v___x_1940_);
lean_dec(v_x_1881_);
v_x_1879_ = v_fn_1937_;
v_x_1880_ = v___x_1939_;
v_x_1881_ = v___x_1941_;
goto _start;
}
else
{
lean_dec(v_x_1881_);
if (v_skipConstInApp_1878_ == 0)
{
goto v___jp_1934_;
}
else
{
uint8_t v___x_1943_; 
v___x_1943_ = l_Lean_Expr_isConst(v_x_1879_);
if (v___x_1943_ == 0)
{
goto v___jp_1934_;
}
else
{
v_f_1889_ = v_x_1879_;
v___y_1890_ = v___y_1882_;
v___y_1891_ = v___y_1883_;
v___y_1892_ = v___y_1884_;
v___y_1893_ = v___y_1885_;
v___y_1894_ = v___y_1886_;
goto v___jp_1888_;
}
}
}
v___jp_1888_:
{
if (v_skipInstances_1874_ == 0)
{
size_t v_sz_1895_; size_t v___x_1896_; lean_object* v___x_1897_; 
v_sz_1895_ = lean_array_size(v_x_1880_);
v___x_1896_ = ((size_t)0ULL);
lean_inc_ref(v_post_1876_);
lean_inc_ref(v_pre_1875_);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1875_, v_post_1876_, v_usedLetOnly_1877_, v_skipConstInApp_1878_, v_skipInstances_1874_, v_sz_1895_, v___x_1896_, v_x_1880_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = l_Lean_mkAppN(v_f_1889_, v_a_1898_);
lean_dec(v_a_1898_);
v___x_1900_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1875_, v_post_1876_, v_usedLetOnly_1877_, v_skipConstInApp_1878_, v_skipInstances_1874_, v___x_1899_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
return v___x_1900_;
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref(v_f_1889_);
lean_dec_ref(v_post_1876_);
lean_dec_ref(v_pre_1875_);
v_a_1901_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1897_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1897_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_array_get_size(v_x_1880_);
lean_inc_ref(v_f_1889_);
v___x_1910_ = l_Lean_Meta_getFunInfoNArgs(v_f_1889_, v___x_1909_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_paramInfo_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v_paramInfo_1912_ = lean_ctor_get(v_a_1911_, 0);
lean_inc_ref(v_paramInfo_1912_);
lean_dec(v_a_1911_);
v___x_1913_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1876_);
lean_inc_ref(v_pre_1875_);
v___x_1914_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1909_, v_paramInfo_1912_, v_pre_1875_, v_post_1876_, v_usedLetOnly_1877_, v_skipConstInApp_1878_, v_skipInstances_1874_, v___x_1913_, v_x_1880_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec_ref(v_paramInfo_1912_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1916_ = l_Lean_mkAppN(v_f_1889_, v_a_1915_);
lean_dec(v_a_1915_);
v___x_1917_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1875_, v_post_1876_, v_usedLetOnly_1877_, v_skipConstInApp_1878_, v_skipInstances_1874_, v___x_1916_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
return v___x_1917_;
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref(v_f_1889_);
lean_dec_ref(v_post_1876_);
lean_dec_ref(v_pre_1875_);
v_a_1918_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1914_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1914_);
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
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v_f_1889_);
lean_dec_ref(v_x_1880_);
lean_dec_ref(v_post_1876_);
lean_dec_ref(v_pre_1875_);
v_a_1926_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1910_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1910_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
v___jp_1934_:
{
lean_object* v___x_1935_; 
lean_inc_ref(v_post_1876_);
lean_inc_ref(v_pre_1875_);
v___x_1935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1875_, v_post_1876_, v_usedLetOnly_1877_, v_skipConstInApp_1878_, v_skipInstances_1874_, v_x_1879_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v_f_1889_ = v_a_1936_;
v___y_1890_ = v___y_1882_;
v___y_1891_ = v___y_1883_;
v___y_1892_ = v___y_1884_;
v___y_1893_ = v___y_1885_;
v___y_1894_ = v___y_1886_;
goto v___jp_1888_;
}
else
{
lean_dec_ref(v_x_1880_);
lean_dec_ref(v_post_1876_);
lean_dec_ref(v_pre_1875_);
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1944_, lean_object* v_pre_1945_, lean_object* v_e_1946_, lean_object* v_post_1947_, uint8_t v_usedLetOnly_1948_, uint8_t v_skipConstInApp_1949_, uint8_t v_skipInstances_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_Core_checkSystem(v___x_1944_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1958_; 
lean_dec_ref_known(v___x_1957_, 1);
lean_inc_ref(v_pre_1945_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc_ref(v_e_1946_);
v___x_1958_ = lean_apply_6(v_pre_1945_, v_e_1946_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, lean_box(0));
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_2007_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_2007_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_2007_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___y_1964_; 
switch(lean_obj_tag(v_a_1959_))
{
case 0:
{
lean_object* v_e_1999_; lean_object* v___x_2001_; 
lean_dec_ref(v_post_1947_);
lean_dec_ref(v_e_1946_);
lean_dec_ref(v_pre_1945_);
v_e_1999_ = lean_ctor_get(v_a_1959_, 0);
lean_inc_ref(v_e_1999_);
lean_dec_ref_known(v_a_1959_, 1);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v_e_1999_);
v___x_2001_ = v___x_1961_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_e_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
case 1:
{
lean_object* v_e_2003_; lean_object* v___x_2004_; 
lean_del_object(v___x_1961_);
lean_dec_ref(v_e_1946_);
v_e_2003_ = lean_ctor_get(v_a_1959_, 0);
lean_inc_ref(v_e_2003_);
lean_dec_ref_known(v_a_1959_, 1);
v___x_2004_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v_e_2003_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_2004_;
}
default: 
{
lean_object* v_e_x3f_2005_; 
lean_del_object(v___x_1961_);
v_e_x3f_2005_ = lean_ctor_get(v_a_1959_, 0);
lean_inc(v_e_x3f_2005_);
lean_dec_ref_known(v_a_1959_, 1);
if (lean_obj_tag(v_e_x3f_2005_) == 0)
{
v___y_1964_ = v_e_1946_;
goto v___jp_1963_;
}
else
{
lean_object* v_val_2006_; 
lean_dec_ref(v_e_1946_);
v_val_2006_ = lean_ctor_get(v_e_x3f_2005_, 0);
lean_inc(v_val_2006_);
lean_dec_ref_known(v_e_x3f_2005_, 1);
v___y_1964_ = v_val_2006_;
goto v___jp_1963_;
}
}
}
v___jp_1963_:
{
switch(lean_obj_tag(v___y_1964_))
{
case 7:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v___x_1965_, v___y_1964_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1966_;
}
case 6:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1968_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v___x_1967_, v___y_1964_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1968_;
}
case 8:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v___x_1969_, v___y_1964_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1970_;
}
case 5:
{
lean_object* v_dummy_1971_; lean_object* v_nargs_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_dummy_1971_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1972_ = l_Lean_Expr_getAppNumArgs(v___y_1964_);
lean_inc(v_nargs_1972_);
v___x_1973_ = lean_mk_array(v_nargs_1972_, v_dummy_1971_);
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_sub(v_nargs_1972_, v___x_1974_);
lean_dec(v_nargs_1972_);
v___x_1976_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1950_, v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v___y_1964_, v___x_1973_, v___x_1975_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1976_;
}
case 10:
{
lean_object* v_data_1977_; lean_object* v_expr_1978_; lean_object* v___x_1979_; 
v_data_1977_ = lean_ctor_get(v___y_1964_, 0);
v_expr_1978_ = lean_ctor_get(v___y_1964_, 1);
lean_inc_ref(v_expr_1978_);
lean_inc_ref(v_post_1947_);
lean_inc_ref(v_pre_1945_);
v___x_1979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v_expr_1978_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; size_t v___x_1981_; size_t v___x_1982_; uint8_t v___x_1983_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_1981_ = lean_ptr_addr(v_expr_1978_);
v___x_1982_ = lean_ptr_addr(v_a_1980_);
v___x_1983_ = lean_usize_dec_eq(v___x_1981_, v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_inc(v_data_1977_);
lean_dec_ref_known(v___y_1964_, 2);
v___x_1984_ = l_Lean_Expr_mdata___override(v_data_1977_, v_a_1980_);
v___x_1985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v___x_1984_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1985_;
}
else
{
lean_object* v___x_1986_; 
lean_dec(v_a_1980_);
v___x_1986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v___y_1964_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1986_;
}
}
else
{
lean_dec_ref_known(v___y_1964_, 2);
lean_dec_ref(v_post_1947_);
lean_dec_ref(v_pre_1945_);
return v___x_1979_;
}
}
case 11:
{
lean_object* v_typeName_1987_; lean_object* v_idx_1988_; lean_object* v_struct_1989_; lean_object* v___x_1990_; 
v_typeName_1987_ = lean_ctor_get(v___y_1964_, 0);
v_idx_1988_ = lean_ctor_get(v___y_1964_, 1);
v_struct_1989_ = lean_ctor_get(v___y_1964_, 2);
lean_inc_ref(v_struct_1989_);
lean_inc_ref(v_post_1947_);
lean_inc_ref(v_pre_1945_);
v___x_1990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v_struct_1989_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; size_t v___x_1992_; size_t v___x_1993_; uint8_t v___x_1994_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = lean_ptr_addr(v_struct_1989_);
v___x_1993_ = lean_ptr_addr(v_a_1991_);
v___x_1994_ = lean_usize_dec_eq(v___x_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc(v_idx_1988_);
lean_inc(v_typeName_1987_);
lean_dec_ref_known(v___y_1964_, 3);
v___x_1995_ = l_Lean_Expr_proj___override(v_typeName_1987_, v_idx_1988_, v_a_1991_);
v___x_1996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v___x_1995_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; 
lean_dec(v_a_1991_);
v___x_1997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v___y_1964_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1997_;
}
}
else
{
lean_dec_ref_known(v___y_1964_, 3);
lean_dec_ref(v_post_1947_);
lean_dec_ref(v_pre_1945_);
return v___x_1990_;
}
}
default: 
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1945_, v_post_1947_, v_usedLetOnly_1948_, v_skipConstInApp_1949_, v_skipInstances_1950_, v___y_1964_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1998_;
}
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_post_1947_);
lean_dec_ref(v_e_1946_);
lean_dec_ref(v_pre_1945_);
v_a_2008_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1958_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1958_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_post_1947_);
lean_dec_ref(v_e_1946_);
lean_dec_ref(v_pre_1945_);
v_a_2016_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1957_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1957_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2024_, lean_object* v_pre_2025_, lean_object* v_e_2026_, lean_object* v_post_2027_, lean_object* v_usedLetOnly_2028_, lean_object* v_skipConstInApp_2029_, lean_object* v_skipInstances_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
uint8_t v_usedLetOnly_boxed_2037_; uint8_t v_skipConstInApp_boxed_2038_; uint8_t v_skipInstances_boxed_2039_; lean_object* v_res_2040_; 
v_usedLetOnly_boxed_2037_ = lean_unbox(v_usedLetOnly_2028_);
v_skipConstInApp_boxed_2038_ = lean_unbox(v_skipConstInApp_2029_);
v_skipInstances_boxed_2039_ = lean_unbox(v_skipInstances_2030_);
v_res_2040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2024_, v_pre_2025_, v_e_2026_, v_post_2027_, v_usedLetOnly_boxed_2037_, v_skipConstInApp_boxed_2038_, v_skipInstances_boxed_2039_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2041_, lean_object* v_post_2042_, uint8_t v_usedLetOnly_2043_, uint8_t v_skipConstInApp_2044_, uint8_t v_skipInstances_2045_, lean_object* v_e_2046_, lean_object* v_a_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_inc(v_a_2047_);
v___x_2053_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2053_, 0, lean_box(0));
lean_closure_set(v___x_2053_, 1, lean_box(0));
lean_closure_set(v___x_2053_, 2, v_a_2047_);
v___x_2054_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2053_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2089_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2089_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2089_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2055_, v_e_2046_);
lean_dec(v_a_2055_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___f_2064_; lean_object* v___x_2065_; 
lean_del_object(v___x_2057_);
v___x_2060_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2061_ = lean_box(v_usedLetOnly_2043_);
v___x_2062_ = lean_box(v_skipConstInApp_2044_);
v___x_2063_ = lean_box(v_skipInstances_2045_);
lean_inc_ref(v_e_2046_);
v___f_2064_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2064_, 0, v___x_2060_);
lean_closure_set(v___f_2064_, 1, v_pre_2041_);
lean_closure_set(v___f_2064_, 2, v_e_2046_);
lean_closure_set(v___f_2064_, 3, v_post_2042_);
lean_closure_set(v___f_2064_, 4, v___x_2061_);
lean_closure_set(v___f_2064_, 5, v___x_2062_);
lean_closure_set(v___f_2064_, 6, v___x_2063_);
v___x_2065_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2064_, v_a_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_n(v_a_2066_, 2);
lean_dec_ref_known(v___x_2065_, 1);
lean_inc(v_a_2047_);
v___f_2067_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2067_, 0, v_a_2047_);
lean_closure_set(v___f_2067_, 1, v_e_2046_);
lean_closure_set(v___f_2067_, 2, v_a_2066_);
v___x_2068_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2067_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2068_, 0);
lean_dec(v_unused_2076_);
v___x_2070_ = v___x_2068_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_dec(v___x_2068_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v_a_2066_);
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2066_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec(v_a_2066_);
v_a_2077_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2068_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2068_);
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
lean_dec_ref(v_e_2046_);
return v___x_2065_;
}
}
else
{
lean_object* v_val_2085_; lean_object* v___x_2087_; 
lean_dec_ref(v_e_2046_);
lean_dec_ref(v_post_2042_);
lean_dec_ref(v_pre_2041_);
v_val_2085_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_val_2085_);
lean_dec_ref_known(v___x_2059_, 1);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_val_2085_);
v___x_2087_ = v___x_2057_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_val_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec_ref(v_e_2046_);
lean_dec_ref(v_post_2042_);
lean_dec_ref(v_pre_2041_);
v_a_2090_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2054_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2054_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2098_, lean_object* v_pre_2099_, lean_object* v_post_2100_, lean_object* v_usedLetOnly_2101_, lean_object* v_skipConstInApp_2102_, lean_object* v_skipInstances_2103_, lean_object* v_body_2104_, lean_object* v_x_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
uint8_t v_usedLetOnly_boxed_2112_; uint8_t v_skipConstInApp_boxed_2113_; uint8_t v_skipInstances_boxed_2114_; lean_object* v_res_2115_; 
v_usedLetOnly_boxed_2112_ = lean_unbox(v_usedLetOnly_2101_);
v_skipConstInApp_boxed_2113_ = lean_unbox(v_skipConstInApp_2102_);
v_skipInstances_boxed_2114_ = lean_unbox(v_skipInstances_2103_);
v_res_2115_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2098_, v_pre_2099_, v_post_2100_, v_usedLetOnly_boxed_2112_, v_skipConstInApp_boxed_2113_, v_skipInstances_boxed_2114_, v_body_2104_, v_x_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2116_, lean_object* v_post_2117_, uint8_t v_usedLetOnly_2118_, uint8_t v_skipConstInApp_2119_, uint8_t v_skipInstances_2120_, lean_object* v_fvars_2121_, lean_object* v_e_2122_, lean_object* v_a_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
if (lean_obj_tag(v_e_2122_) == 7)
{
lean_object* v_binderName_2129_; lean_object* v_binderType_2130_; lean_object* v_body_2131_; uint8_t v_binderInfo_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_binderName_2129_ = lean_ctor_get(v_e_2122_, 0);
lean_inc(v_binderName_2129_);
v_binderType_2130_ = lean_ctor_get(v_e_2122_, 1);
lean_inc_ref(v_binderType_2130_);
v_body_2131_ = lean_ctor_get(v_e_2122_, 2);
lean_inc_ref(v_body_2131_);
v_binderInfo_2132_ = lean_ctor_get_uint8(v_e_2122_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2122_, 3);
v___x_2133_ = lean_expr_instantiate_rev(v_binderType_2130_, v_fvars_2121_);
lean_dec_ref(v_binderType_2130_);
lean_inc_ref(v_post_2117_);
lean_inc_ref(v_pre_2116_);
v___x_2134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2116_, v_post_2117_, v_usedLetOnly_2118_, v_skipConstInApp_2119_, v_skipInstances_2120_, v___x_2133_, v_a_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___f_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = lean_box(v_usedLetOnly_2118_);
v___x_2137_ = lean_box(v_skipConstInApp_2119_);
v___x_2138_ = lean_box(v_skipInstances_2120_);
v___f_2139_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2139_, 0, v_fvars_2121_);
lean_closure_set(v___f_2139_, 1, v_pre_2116_);
lean_closure_set(v___f_2139_, 2, v_post_2117_);
lean_closure_set(v___f_2139_, 3, v___x_2136_);
lean_closure_set(v___f_2139_, 4, v___x_2137_);
lean_closure_set(v___f_2139_, 5, v___x_2138_);
lean_closure_set(v___f_2139_, 6, v_body_2131_);
v___x_2140_ = 0;
v___x_2141_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2129_, v_binderInfo_2132_, v_a_2135_, v___f_2139_, v___x_2140_, v_a_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v___x_2141_;
}
else
{
lean_dec_ref(v_body_2131_);
lean_dec(v_binderName_2129_);
lean_dec_ref(v_fvars_2121_);
lean_dec_ref(v_post_2117_);
lean_dec_ref(v_pre_2116_);
return v___x_2134_;
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_expr_instantiate_rev(v_e_2122_, v_fvars_2121_);
lean_dec_ref(v_e_2122_);
lean_inc_ref(v_post_2117_);
lean_inc_ref(v_pre_2116_);
v___x_2143_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2116_, v_post_2117_, v_usedLetOnly_2118_, v_skipConstInApp_2119_, v_skipInstances_2120_, v___x_2142_, v_a_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; uint8_t v___x_2145_; uint8_t v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = 0;
v___x_2146_ = 1;
v___x_2147_ = 1;
v___x_2148_ = l_Lean_Meta_mkForallFVars(v_fvars_2121_, v_a_2144_, v___x_2145_, v_usedLetOnly_2118_, v___x_2146_, v___x_2147_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec_ref(v_fvars_2121_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2150_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2116_, v_post_2117_, v_usedLetOnly_2118_, v_skipConstInApp_2119_, v_skipInstances_2120_, v_a_2149_, v_a_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
return v___x_2150_;
}
else
{
lean_dec_ref(v_post_2117_);
lean_dec_ref(v_pre_2116_);
return v___x_2148_;
}
}
else
{
lean_dec_ref(v_fvars_2121_);
lean_dec_ref(v_post_2117_);
lean_dec_ref(v_pre_2116_);
return v___x_2143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2151_, lean_object* v_pre_2152_, lean_object* v_post_2153_, uint8_t v_usedLetOnly_2154_, uint8_t v_skipConstInApp_2155_, uint8_t v_skipInstances_2156_, lean_object* v_body_2157_, lean_object* v_x_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_array_push(v_fvars_2151_, v_x_2158_);
v___x_2166_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2152_, v_post_2153_, v_usedLetOnly_2154_, v_skipConstInApp_2155_, v_skipInstances_2156_, v___x_2165_, v_body_2157_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2167_, lean_object* v_post_2168_, lean_object* v_usedLetOnly_2169_, lean_object* v_skipConstInApp_2170_, lean_object* v_skipInstances_2171_, lean_object* v_e_2172_, lean_object* v_a_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v_usedLetOnly_boxed_2179_; uint8_t v_skipConstInApp_boxed_2180_; uint8_t v_skipInstances_boxed_2181_; lean_object* v_res_2182_; 
v_usedLetOnly_boxed_2179_ = lean_unbox(v_usedLetOnly_2169_);
v_skipConstInApp_boxed_2180_ = lean_unbox(v_skipConstInApp_2170_);
v_skipInstances_boxed_2181_ = lean_unbox(v_skipInstances_2171_);
v_res_2182_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2167_, v_post_2168_, v_usedLetOnly_boxed_2179_, v_skipConstInApp_boxed_2180_, v_skipInstances_boxed_2181_, v_e_2172_, v_a_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v_a_2173_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2183_, lean_object* v_post_2184_, lean_object* v_usedLetOnly_2185_, lean_object* v_skipConstInApp_2186_, lean_object* v_skipInstances_2187_, lean_object* v_sz_2188_, lean_object* v_i_2189_, lean_object* v_bs_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
uint8_t v_usedLetOnly_boxed_2197_; uint8_t v_skipConstInApp_boxed_2198_; uint8_t v_skipInstances_boxed_2199_; size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_usedLetOnly_boxed_2197_ = lean_unbox(v_usedLetOnly_2185_);
v_skipConstInApp_boxed_2198_ = lean_unbox(v_skipConstInApp_2186_);
v_skipInstances_boxed_2199_ = lean_unbox(v_skipInstances_2187_);
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2188_);
lean_dec(v_sz_2188_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2189_);
lean_dec(v_i_2189_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2183_, v_post_2184_, v_usedLetOnly_boxed_2197_, v_skipConstInApp_boxed_2198_, v_skipInstances_boxed_2199_, v_sz_boxed_2200_, v_i_boxed_2201_, v_bs_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2203_, lean_object* v_post_2204_, lean_object* v_usedLetOnly_2205_, lean_object* v_skipConstInApp_2206_, lean_object* v_skipInstances_2207_, lean_object* v_e_2208_, lean_object* v_a_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
uint8_t v_usedLetOnly_boxed_2215_; uint8_t v_skipConstInApp_boxed_2216_; uint8_t v_skipInstances_boxed_2217_; lean_object* v_res_2218_; 
v_usedLetOnly_boxed_2215_ = lean_unbox(v_usedLetOnly_2205_);
v_skipConstInApp_boxed_2216_ = lean_unbox(v_skipConstInApp_2206_);
v_skipInstances_boxed_2217_ = lean_unbox(v_skipInstances_2207_);
v_res_2218_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2203_, v_post_2204_, v_usedLetOnly_boxed_2215_, v_skipConstInApp_boxed_2216_, v_skipInstances_boxed_2217_, v_e_2208_, v_a_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v_a_2209_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2219_, lean_object* v_post_2220_, lean_object* v_usedLetOnly_2221_, lean_object* v_skipConstInApp_2222_, lean_object* v_skipInstances_2223_, lean_object* v_fvars_2224_, lean_object* v_e_2225_, lean_object* v_a_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
uint8_t v_usedLetOnly_boxed_2232_; uint8_t v_skipConstInApp_boxed_2233_; uint8_t v_skipInstances_boxed_2234_; lean_object* v_res_2235_; 
v_usedLetOnly_boxed_2232_ = lean_unbox(v_usedLetOnly_2221_);
v_skipConstInApp_boxed_2233_ = lean_unbox(v_skipConstInApp_2222_);
v_skipInstances_boxed_2234_ = lean_unbox(v_skipInstances_2223_);
v_res_2235_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2219_, v_post_2220_, v_usedLetOnly_boxed_2232_, v_skipConstInApp_boxed_2233_, v_skipInstances_boxed_2234_, v_fvars_2224_, v_e_2225_, v_a_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v_a_2226_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2236_, lean_object* v_post_2237_, lean_object* v_usedLetOnly_2238_, lean_object* v_skipConstInApp_2239_, lean_object* v_skipInstances_2240_, lean_object* v_fvars_2241_, lean_object* v_e_2242_, lean_object* v_a_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_usedLetOnly_boxed_2249_; uint8_t v_skipConstInApp_boxed_2250_; uint8_t v_skipInstances_boxed_2251_; lean_object* v_res_2252_; 
v_usedLetOnly_boxed_2249_ = lean_unbox(v_usedLetOnly_2238_);
v_skipConstInApp_boxed_2250_ = lean_unbox(v_skipConstInApp_2239_);
v_skipInstances_boxed_2251_ = lean_unbox(v_skipInstances_2240_);
v_res_2252_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2236_, v_post_2237_, v_usedLetOnly_boxed_2249_, v_skipConstInApp_boxed_2250_, v_skipInstances_boxed_2251_, v_fvars_2241_, v_e_2242_, v_a_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v_a_2243_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2253_, lean_object* v_post_2254_, lean_object* v_usedLetOnly_2255_, lean_object* v_skipConstInApp_2256_, lean_object* v_skipInstances_2257_, lean_object* v_fvars_2258_, lean_object* v_e_2259_, lean_object* v_a_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
uint8_t v_usedLetOnly_boxed_2266_; uint8_t v_skipConstInApp_boxed_2267_; uint8_t v_skipInstances_boxed_2268_; lean_object* v_res_2269_; 
v_usedLetOnly_boxed_2266_ = lean_unbox(v_usedLetOnly_2255_);
v_skipConstInApp_boxed_2267_ = lean_unbox(v_skipConstInApp_2256_);
v_skipInstances_boxed_2268_ = lean_unbox(v_skipInstances_2257_);
v_res_2269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2253_, v_post_2254_, v_usedLetOnly_boxed_2266_, v_skipConstInApp_boxed_2267_, v_skipInstances_boxed_2268_, v_fvars_2258_, v_e_2259_, v_a_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v_a_2260_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2270_, lean_object* v___x_2271_, lean_object* v_pre_2272_, lean_object* v_post_2273_, lean_object* v_usedLetOnly_2274_, lean_object* v_skipConstInApp_2275_, lean_object* v_skipInstances_2276_, lean_object* v_a_2277_, lean_object* v_b_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
uint8_t v_usedLetOnly_boxed_2285_; uint8_t v_skipConstInApp_boxed_2286_; uint8_t v_skipInstances_boxed_2287_; lean_object* v_res_2288_; 
v_usedLetOnly_boxed_2285_ = lean_unbox(v_usedLetOnly_2274_);
v_skipConstInApp_boxed_2286_ = lean_unbox(v_skipConstInApp_2275_);
v_skipInstances_boxed_2287_ = lean_unbox(v_skipInstances_2276_);
v_res_2288_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2270_, v___x_2271_, v_pre_2272_, v_post_2273_, v_usedLetOnly_boxed_2285_, v_skipConstInApp_boxed_2286_, v_skipInstances_boxed_2287_, v_a_2277_, v_b_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___x_2271_);
lean_dec(v_upperBound_2270_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2289_, lean_object* v_pre_2290_, lean_object* v_post_2291_, lean_object* v_usedLetOnly_2292_, lean_object* v_skipConstInApp_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
uint8_t v_skipInstances_boxed_2303_; uint8_t v_usedLetOnly_boxed_2304_; uint8_t v_skipConstInApp_boxed_2305_; lean_object* v_res_2306_; 
v_skipInstances_boxed_2303_ = lean_unbox(v_skipInstances_2289_);
v_usedLetOnly_boxed_2304_ = lean_unbox(v_usedLetOnly_2292_);
v_skipConstInApp_boxed_2305_ = lean_unbox(v_skipConstInApp_2293_);
v_res_2306_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2303_, v_pre_2290_, v_post_2291_, v_usedLetOnly_boxed_2304_, v_skipConstInApp_boxed_2305_, v_x_2294_, v_x_2295_, v_x_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
return v_res_2306_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2308_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2308_, 0, lean_box(0));
lean_closure_set(v___x_2308_, 1, lean_box(0));
lean_closure_set(v___x_2308_, 2, v___x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2309_, lean_object* v_pre_2310_, lean_object* v_post_2311_, uint8_t v_usedLetOnly_2312_, uint8_t v_skipConstInApp_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_a_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; 
v___x_2319_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2320_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2319_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = 0;
v___x_2323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2310_, v_post_2311_, v_usedLetOnly_2312_, v_skipConstInApp_2313_, v___x_2322_, v_input_2309_, v_a_2321_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2325_, 0, lean_box(0));
lean_closure_set(v___x_2325_, 1, lean_box(0));
lean_closure_set(v___x_2325_, 2, v_a_2321_);
v___x_2326_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2325_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v___x_2326_, 0);
lean_dec(v_unused_2334_);
v___x_2328_ = v___x_2326_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v___x_2326_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v_a_2324_);
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2324_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
lean_dec(v_a_2321_);
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2335_, lean_object* v_pre_2336_, lean_object* v_post_2337_, lean_object* v_usedLetOnly_2338_, lean_object* v_skipConstInApp_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
uint8_t v_usedLetOnly_boxed_2345_; uint8_t v_skipConstInApp_boxed_2346_; lean_object* v_res_2347_; 
v_usedLetOnly_boxed_2345_ = lean_unbox(v_usedLetOnly_2338_);
v_skipConstInApp_boxed_2346_ = lean_unbox(v_skipConstInApp_2339_);
v_res_2347_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2335_, v_pre_2336_, v_post_2337_, v_usedLetOnly_boxed_2345_, v_skipConstInApp_boxed_2346_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2348_, lean_object* v_as_2349_, lean_object* v_j_2350_){
_start:
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
v___x_2351_ = lean_array_get_size(v_as_2349_);
v___x_2352_ = lean_nat_dec_lt(v_j_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v_j_2350_);
v___x_2353_ = lean_box(0);
return v___x_2353_;
}
else
{
lean_object* v___x_2354_; lean_object* v_declName_2355_; uint8_t v___x_2356_; 
v___x_2354_ = lean_array_fget_borrowed(v_as_2349_, v_j_2350_);
v_declName_2355_ = lean_ctor_get(v___x_2354_, 3);
v___x_2356_ = lean_name_eq(v_declName_2355_, v___x_2348_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_add(v_j_2350_, v___x_2357_);
lean_dec(v_j_2350_);
v_j_2350_ = v___x_2358_;
goto _start;
}
else
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2360_, 0, v_j_2350_);
return v___x_2360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2361_, lean_object* v_as_2362_, lean_object* v_j_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2361_, v_as_2362_, v_j_2363_);
lean_dec_ref(v_as_2362_);
lean_dec(v___x_2361_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_st_ref_get(v_val_2365_);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v_val_2373_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2380_, lean_object* v_val_2381_, lean_object* v_a_2382_, lean_object* v___x_2383_, lean_object* v_____r_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2390_ = lean_st_ref_take(v_val_2380_);
v___x_2391_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2381_, v_a_2382_, v___x_2390_);
v___x_2392_ = lean_st_ref_set(v_val_2380_, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2383_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2395_, lean_object* v_val_2396_, lean_object* v_a_2397_, lean_object* v___x_2398_, lean_object* v_____r_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2395_, v_val_2396_, v_a_2397_, v___x_2398_, v_____r_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_val_2396_);
lean_dec(v_val_2395_);
return v_res_2405_;
}
}
static uint64_t _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0(void){
_start:
{
uint8_t v___x_2406_; uint64_t v___x_2407_; 
v___x_2406_ = 2;
v___x_2407_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2406_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_upperBound_2408_, lean_object* v_val_2409_, lean_object* v_next_2410_, lean_object* v_params_2411_, lean_object* v___x_2412_, lean_object* v_val_2413_, lean_object* v_next_2414_, uint8_t v___x_2415_, lean_object* v_a_2416_, uint8_t v_b_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
uint8_t v_a_2424_; uint8_t v___x_2428_; 
v___x_2428_ = lean_nat_dec_lt(v_a_2416_, v_upperBound_2408_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_dec(v_a_2416_);
lean_dec(v_next_2414_);
lean_dec_ref(v___x_2412_);
v___x_2429_ = lean_box(v_b_2417_);
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
else
{
lean_object* v___x_2431_; uint8_t v___x_2432_; 
v___x_2431_ = lean_st_ref_get(v_val_2409_);
v___x_2432_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2410_, v_a_2416_, v___x_2431_);
lean_dec(v___x_2431_);
if (v___x_2432_ == 0)
{
v_a_2424_ = v_b_2417_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2433_; uint8_t v_foApprox_2434_; uint8_t v_ctxApprox_2435_; uint8_t v_quasiPatternApprox_2436_; uint8_t v_constApprox_2437_; uint8_t v_isDefEqStuckEx_2438_; uint8_t v_unificationHints_2439_; uint8_t v_assignSyntheticOpaque_2440_; uint8_t v_offsetCnstrs_2441_; uint8_t v_transparency_2442_; uint8_t v_etaStruct_2443_; uint8_t v_univApprox_2444_; uint8_t v_iota_2445_; uint8_t v_beta_2446_; uint8_t v_proj_2447_; uint8_t v_zeta_2448_; uint8_t v_zetaDelta_2449_; uint8_t v_zetaUnused_2450_; uint8_t v_zetaHave_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2514_; 
v___x_2433_ = l_Lean_Meta_Context_config(v___y_2418_);
v_foApprox_2434_ = lean_ctor_get_uint8(v___x_2433_, 0);
v_ctxApprox_2435_ = lean_ctor_get_uint8(v___x_2433_, 1);
v_quasiPatternApprox_2436_ = lean_ctor_get_uint8(v___x_2433_, 2);
v_constApprox_2437_ = lean_ctor_get_uint8(v___x_2433_, 3);
v_isDefEqStuckEx_2438_ = lean_ctor_get_uint8(v___x_2433_, 4);
v_unificationHints_2439_ = lean_ctor_get_uint8(v___x_2433_, 5);
v_assignSyntheticOpaque_2440_ = lean_ctor_get_uint8(v___x_2433_, 7);
v_offsetCnstrs_2441_ = lean_ctor_get_uint8(v___x_2433_, 8);
v_transparency_2442_ = lean_ctor_get_uint8(v___x_2433_, 9);
v_etaStruct_2443_ = lean_ctor_get_uint8(v___x_2433_, 10);
v_univApprox_2444_ = lean_ctor_get_uint8(v___x_2433_, 11);
v_iota_2445_ = lean_ctor_get_uint8(v___x_2433_, 12);
v_beta_2446_ = lean_ctor_get_uint8(v___x_2433_, 13);
v_proj_2447_ = lean_ctor_get_uint8(v___x_2433_, 14);
v_zeta_2448_ = lean_ctor_get_uint8(v___x_2433_, 15);
v_zetaDelta_2449_ = lean_ctor_get_uint8(v___x_2433_, 16);
v_zetaUnused_2450_ = lean_ctor_get_uint8(v___x_2433_, 17);
v_zetaHave_2451_ = lean_ctor_get_uint8(v___x_2433_, 18);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2453_ = v___x_2433_;
v_isShared_2454_ = v_isSharedCheck_2514_;
goto v_resetjp_2452_;
}
else
{
lean_dec(v___x_2433_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2514_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
uint8_t v_trackZetaDelta_2455_; lean_object* v_zetaDeltaSet_2456_; lean_object* v_lctx_2457_; lean_object* v_localInstances_2458_; lean_object* v_defEqCtx_x3f_2459_; lean_object* v_synthPendingDepth_2460_; lean_object* v_canUnfold_x3f_2461_; uint8_t v_univApprox_2462_; uint8_t v_inTypeClassResolution_2463_; uint8_t v_cacheInferType_2464_; uint8_t v___x_2465_; lean_object* v___x_2467_; 
v_trackZetaDelta_2455_ = lean_ctor_get_uint8(v___y_2418_, sizeof(void*)*7);
v_zetaDeltaSet_2456_ = lean_ctor_get(v___y_2418_, 1);
v_lctx_2457_ = lean_ctor_get(v___y_2418_, 2);
v_localInstances_2458_ = lean_ctor_get(v___y_2418_, 3);
v_defEqCtx_x3f_2459_ = lean_ctor_get(v___y_2418_, 4);
v_synthPendingDepth_2460_ = lean_ctor_get(v___y_2418_, 5);
v_canUnfold_x3f_2461_ = lean_ctor_get(v___y_2418_, 6);
v_univApprox_2462_ = lean_ctor_get_uint8(v___y_2418_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2463_ = lean_ctor_get_uint8(v___y_2418_, sizeof(void*)*7 + 2);
v_cacheInferType_2464_ = lean_ctor_get_uint8(v___y_2418_, sizeof(void*)*7 + 3);
v___x_2465_ = 0;
if (v_isShared_2454_ == 0)
{
v___x_2467_ = v___x_2453_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 0, v_foApprox_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 1, v_ctxApprox_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 2, v_quasiPatternApprox_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 3, v_constApprox_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 4, v_isDefEqStuckEx_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 5, v_unificationHints_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 7, v_assignSyntheticOpaque_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 8, v_offsetCnstrs_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 9, v_transparency_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 10, v_etaStruct_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 11, v_univApprox_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 12, v_iota_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 13, v_beta_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 14, v_proj_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 15, v_zeta_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 16, v_zetaDelta_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 17, v_zetaUnused_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2513_, 18, v_zetaHave_2451_);
v___x_2467_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
uint64_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v_foApprox_2472_; uint8_t v_ctxApprox_2473_; uint8_t v_quasiPatternApprox_2474_; uint8_t v_constApprox_2475_; uint8_t v_isDefEqStuckEx_2476_; uint8_t v_unificationHints_2477_; uint8_t v_proofIrrelevance_2478_; uint8_t v_assignSyntheticOpaque_2479_; uint8_t v_offsetCnstrs_2480_; uint8_t v_etaStruct_2481_; uint8_t v_univApprox_2482_; uint8_t v_iota_2483_; uint8_t v_beta_2484_; uint8_t v_proj_2485_; uint8_t v_zeta_2486_; uint8_t v_zetaDelta_2487_; uint8_t v_zetaUnused_2488_; uint8_t v_zetaHave_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2512_; 
lean_ctor_set_uint8(v___x_2467_, 6, v___x_2465_);
v___x_2468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2467_);
v___x_2469_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set_uint64(v___x_2469_, sizeof(void*)*1, v___x_2468_);
lean_inc(v_canUnfold_x3f_2461_);
lean_inc(v_synthPendingDepth_2460_);
lean_inc(v_defEqCtx_x3f_2459_);
lean_inc_ref(v_localInstances_2458_);
lean_inc_ref(v_lctx_2457_);
lean_inc(v_zetaDeltaSet_2456_);
v___x_2470_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v_zetaDeltaSet_2456_);
lean_ctor_set(v___x_2470_, 2, v_lctx_2457_);
lean_ctor_set(v___x_2470_, 3, v_localInstances_2458_);
lean_ctor_set(v___x_2470_, 4, v_defEqCtx_x3f_2459_);
lean_ctor_set(v___x_2470_, 5, v_synthPendingDepth_2460_);
lean_ctor_set(v___x_2470_, 6, v_canUnfold_x3f_2461_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*7, v_trackZetaDelta_2455_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*7 + 1, v_univApprox_2462_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2463_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*7 + 3, v_cacheInferType_2464_);
v___x_2471_ = l_Lean_Meta_Context_config(v___x_2470_);
v_foApprox_2472_ = lean_ctor_get_uint8(v___x_2471_, 0);
v_ctxApprox_2473_ = lean_ctor_get_uint8(v___x_2471_, 1);
v_quasiPatternApprox_2474_ = lean_ctor_get_uint8(v___x_2471_, 2);
v_constApprox_2475_ = lean_ctor_get_uint8(v___x_2471_, 3);
v_isDefEqStuckEx_2476_ = lean_ctor_get_uint8(v___x_2471_, 4);
v_unificationHints_2477_ = lean_ctor_get_uint8(v___x_2471_, 5);
v_proofIrrelevance_2478_ = lean_ctor_get_uint8(v___x_2471_, 6);
v_assignSyntheticOpaque_2479_ = lean_ctor_get_uint8(v___x_2471_, 7);
v_offsetCnstrs_2480_ = lean_ctor_get_uint8(v___x_2471_, 8);
v_etaStruct_2481_ = lean_ctor_get_uint8(v___x_2471_, 10);
v_univApprox_2482_ = lean_ctor_get_uint8(v___x_2471_, 11);
v_iota_2483_ = lean_ctor_get_uint8(v___x_2471_, 12);
v_beta_2484_ = lean_ctor_get_uint8(v___x_2471_, 13);
v_proj_2485_ = lean_ctor_get_uint8(v___x_2471_, 14);
v_zeta_2486_ = lean_ctor_get_uint8(v___x_2471_, 15);
v_zetaDelta_2487_ = lean_ctor_get_uint8(v___x_2471_, 16);
v_zetaUnused_2488_ = lean_ctor_get_uint8(v___x_2471_, 17);
v_zetaHave_2489_ = lean_ctor_get_uint8(v___x_2471_, 18);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2491_ = v___x_2471_;
v_isShared_2492_ = v_isSharedCheck_2512_;
goto v_resetjp_2490_;
}
else
{
lean_dec(v___x_2471_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2512_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; uint8_t v___x_2494_; lean_object* v_config_2496_; 
v___x_2493_ = lean_array_fget_borrowed(v_params_2411_, v_a_2416_);
v___x_2494_ = 2;
if (v_isShared_2492_ == 0)
{
v_config_2496_ = v___x_2491_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 0, v_foApprox_2472_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 1, v_ctxApprox_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 2, v_quasiPatternApprox_2474_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 3, v_constApprox_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 4, v_isDefEqStuckEx_2476_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 5, v_unificationHints_2477_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 6, v_proofIrrelevance_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 7, v_assignSyntheticOpaque_2479_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 8, v_offsetCnstrs_2480_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 10, v_etaStruct_2481_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 11, v_univApprox_2482_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 12, v_iota_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 13, v_beta_2484_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 14, v_proj_2485_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 15, v_zeta_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 16, v_zetaDelta_2487_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 17, v_zetaUnused_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, 18, v_zetaHave_2489_);
v_config_2496_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
uint64_t v___x_2497_; uint64_t v___x_2498_; uint64_t v___x_2499_; uint64_t v___x_2500_; uint64_t v___x_2501_; uint64_t v_key_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_ctor_set_uint8(v_config_2496_, 9, v___x_2494_);
v___x_2497_ = l_Lean_Meta_Context_configKey(v___x_2470_);
lean_dec_ref_known(v___x_2470_, 7);
v___x_2498_ = 3ULL;
v___x_2499_ = lean_uint64_shift_right(v___x_2497_, v___x_2498_);
v___x_2500_ = lean_uint64_shift_left(v___x_2499_, v___x_2498_);
v___x_2501_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2502_ = lean_uint64_lor(v___x_2500_, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2503_, 0, v_config_2496_);
lean_ctor_set_uint64(v___x_2503_, sizeof(void*)*1, v_key_2502_);
lean_inc(v_canUnfold_x3f_2461_);
lean_inc(v_synthPendingDepth_2460_);
lean_inc(v_defEqCtx_x3f_2459_);
lean_inc_ref(v_localInstances_2458_);
lean_inc_ref(v_lctx_2457_);
lean_inc(v_zetaDeltaSet_2456_);
v___x_2504_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v_zetaDeltaSet_2456_);
lean_ctor_set(v___x_2504_, 2, v_lctx_2457_);
lean_ctor_set(v___x_2504_, 3, v_localInstances_2458_);
lean_ctor_set(v___x_2504_, 4, v_defEqCtx_x3f_2459_);
lean_ctor_set(v___x_2504_, 5, v_synthPendingDepth_2460_);
lean_ctor_set(v___x_2504_, 6, v_canUnfold_x3f_2461_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*7, v_trackZetaDelta_2455_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*7 + 1, v_univApprox_2462_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2463_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*7 + 3, v_cacheInferType_2464_);
lean_inc_ref(v___x_2412_);
lean_inc(v___x_2493_);
v___x_2505_ = l_Lean_Meta_isExprDefEq(v___x_2493_, v___x_2412_, v___x_2504_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec_ref_known(v___x_2504_, 7);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; uint8_t v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = lean_unbox(v_a_2506_);
lean_dec(v_a_2506_);
if (v___x_2507_ == 0)
{
v_a_2424_ = v_b_2417_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = lean_st_ref_take(v_val_2409_);
lean_inc(v_a_2416_);
lean_inc(v_next_2414_);
v___x_2509_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2413_, v_next_2414_, v_next_2410_, v_a_2416_, v___x_2508_);
v___x_2510_ = lean_st_ref_set(v_val_2409_, v___x_2509_);
v_a_2424_ = v___x_2415_;
goto v___jp_2423_;
}
}
else
{
lean_dec(v_a_2416_);
lean_dec(v_next_2414_);
lean_dec_ref(v___x_2412_);
return v___x_2505_;
}
}
}
}
}
}
}
v___jp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_nat_add(v_a_2416_, v___x_2425_);
lean_dec(v_a_2416_);
v_a_2416_ = v___x_2426_;
v_b_2417_ = v_a_2424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_upperBound_2515_, lean_object* v_val_2516_, lean_object* v_next_2517_, lean_object* v_params_2518_, lean_object* v___x_2519_, lean_object* v_val_2520_, lean_object* v_next_2521_, lean_object* v___x_2522_, lean_object* v_a_2523_, lean_object* v_b_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
uint8_t v___x_44713__boxed_2530_; uint8_t v_b_boxed_2531_; lean_object* v_res_2532_; 
v___x_44713__boxed_2530_ = lean_unbox(v___x_2522_);
v_b_boxed_2531_ = lean_unbox(v_b_2524_);
v_res_2532_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_2515_, v_val_2516_, v_next_2517_, v_params_2518_, v___x_2519_, v_val_2520_, v_next_2521_, v___x_44713__boxed_2530_, v_a_2523_, v_b_boxed_2531_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v_val_2520_);
lean_dec_ref(v_params_2518_);
lean_dec(v_next_2517_);
lean_dec(v_val_2516_);
lean_dec(v_upperBound_2515_);
return v_res_2532_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2544_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2545_ = l_Lean_Name_append(v___x_2544_, v___x_2543_);
return v___x_2545_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
return v___x_2548_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2550_ = l_Lean_stringToMessageData(v___x_2549_);
return v___x_2550_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2553_ = l_Lean_stringToMessageData(v___x_2552_);
return v___x_2553_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2556_ = l_Lean_stringToMessageData(v___x_2555_);
return v___x_2556_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2559_ = l_Lean_stringToMessageData(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2562_ = l_Lean_stringToMessageData(v___x_2561_);
return v___x_2562_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2565_ = l_Lean_stringToMessageData(v___x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2566_, lean_object* v_val_2567_, lean_object* v_upperBound_2568_, lean_object* v_args_2569_, lean_object* v_e_2570_, lean_object* v_next_2571_, lean_object* v_params_2572_, lean_object* v___x_2573_, uint8_t v___x_2574_, lean_object* v_a_2575_, lean_object* v_b_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_a_2583_; lean_object* v___y_2588_; uint8_t v___x_2607_; 
v___x_2607_ = lean_nat_dec_lt(v_a_2575_, v_upperBound_2568_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; 
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_b_2576_);
return v___x_2608_;
}
else
{
lean_object* v___x_2609_; 
v___x_2609_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2566_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v___x_2611_ = lean_box(0);
v___x_2612_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2567_, v_a_2575_, v_a_2610_);
lean_dec(v_a_2610_);
if (v___x_2612_ == 0)
{
v_a_2583_ = v___x_2611_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2613_ = lean_array_get_size(v_args_2569_);
v___x_2614_ = lean_nat_dec_lt(v_a_2575_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v_options_2615_; lean_object* v_inheritedTraceOptions_2616_; uint8_t v_hasTrace_2617_; 
v_options_2615_ = lean_ctor_get(v___y_2579_, 2);
v_inheritedTraceOptions_2616_ = lean_ctor_get(v___y_2579_, 13);
v_hasTrace_2617_ = lean_ctor_get_uint8(v_options_2615_, sizeof(void*)*1);
if (v_hasTrace_2617_ == 0)
{
goto v___jp_2618_;
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2620_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2621_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2622_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2616_, v_options_2615_, v___x_2621_);
if (v___x_2622_ == 0)
{
goto v___jp_2618_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2623_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2567_);
v___x_2624_ = l_Nat_reprFast(v_val_2567_);
v___x_2625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
v___x_2626_ = l_Lean_MessageData_ofFormat(v___x_2625_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2623_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
lean_inc(v_a_2575_);
v___x_2630_ = l_Nat_reprFast(v_a_2575_);
v___x_2631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v___x_2632_ = l_Lean_MessageData_ofFormat(v___x_2631_);
lean_inc_ref(v___x_2632_);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2629_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
lean_inc_ref(v_e_2570_);
v___x_2636_ = l_Lean_MessageData_ofExpr(v_e_2570_);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2637_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
lean_ctor_set(v___x_2640_, 1, v___x_2632_);
v___x_2641_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2620_, v___x_2640_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2643_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
lean_inc(v_a_2575_);
v___x_2643_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2566_, v_val_2567_, v_a_2575_, v___x_2611_, v_a_2642_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
v___y_2588_ = v___x_2643_;
goto v___jp_2587_;
}
else
{
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
return v___x_2641_;
}
}
}
v___jp_2618_:
{
lean_object* v___x_2619_; 
lean_inc(v_a_2575_);
v___x_2619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2566_, v_val_2567_, v_a_2575_, v___x_2611_, v___x_2611_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
v___y_2588_ = v___x_2619_;
goto v___jp_2587_;
}
}
else
{
lean_object* v___x_2644_; 
v___x_2644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2566_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = lean_array_fget_borrowed(v_args_2569_, v_a_2575_);
v___x_2647_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2567_, v_a_2575_, v_next_2571_, v_a_2645_);
lean_dec(v_a_2645_);
if (lean_obj_tag(v___x_2647_) == 1)
{
lean_object* v_val_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2776_; 
v_val_2648_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2776_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_val_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2776_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; uint8_t v_foApprox_2653_; uint8_t v_ctxApprox_2654_; uint8_t v_quasiPatternApprox_2655_; uint8_t v_constApprox_2656_; uint8_t v_isDefEqStuckEx_2657_; uint8_t v_unificationHints_2658_; uint8_t v_assignSyntheticOpaque_2659_; uint8_t v_offsetCnstrs_2660_; uint8_t v_transparency_2661_; uint8_t v_etaStruct_2662_; uint8_t v_univApprox_2663_; uint8_t v_iota_2664_; uint8_t v_beta_2665_; uint8_t v_proj_2666_; uint8_t v_zeta_2667_; uint8_t v_zetaDelta_2668_; uint8_t v_zetaUnused_2669_; uint8_t v_zetaHave_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2775_; 
v___x_2652_ = l_Lean_Meta_Context_config(v___y_2577_);
v_foApprox_2653_ = lean_ctor_get_uint8(v___x_2652_, 0);
v_ctxApprox_2654_ = lean_ctor_get_uint8(v___x_2652_, 1);
v_quasiPatternApprox_2655_ = lean_ctor_get_uint8(v___x_2652_, 2);
v_constApprox_2656_ = lean_ctor_get_uint8(v___x_2652_, 3);
v_isDefEqStuckEx_2657_ = lean_ctor_get_uint8(v___x_2652_, 4);
v_unificationHints_2658_ = lean_ctor_get_uint8(v___x_2652_, 5);
v_assignSyntheticOpaque_2659_ = lean_ctor_get_uint8(v___x_2652_, 7);
v_offsetCnstrs_2660_ = lean_ctor_get_uint8(v___x_2652_, 8);
v_transparency_2661_ = lean_ctor_get_uint8(v___x_2652_, 9);
v_etaStruct_2662_ = lean_ctor_get_uint8(v___x_2652_, 10);
v_univApprox_2663_ = lean_ctor_get_uint8(v___x_2652_, 11);
v_iota_2664_ = lean_ctor_get_uint8(v___x_2652_, 12);
v_beta_2665_ = lean_ctor_get_uint8(v___x_2652_, 13);
v_proj_2666_ = lean_ctor_get_uint8(v___x_2652_, 14);
v_zeta_2667_ = lean_ctor_get_uint8(v___x_2652_, 15);
v_zetaDelta_2668_ = lean_ctor_get_uint8(v___x_2652_, 16);
v_zetaUnused_2669_ = lean_ctor_get_uint8(v___x_2652_, 17);
v_zetaHave_2670_ = lean_ctor_get_uint8(v___x_2652_, 18);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2672_ = v___x_2652_;
v_isShared_2673_ = v_isSharedCheck_2775_;
goto v_resetjp_2671_;
}
else
{
lean_dec(v___x_2652_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2775_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
uint8_t v_trackZetaDelta_2674_; lean_object* v_zetaDeltaSet_2675_; lean_object* v_lctx_2676_; lean_object* v_localInstances_2677_; lean_object* v_defEqCtx_x3f_2678_; lean_object* v_synthPendingDepth_2679_; lean_object* v_canUnfold_x3f_2680_; uint8_t v_univApprox_2681_; uint8_t v_inTypeClassResolution_2682_; uint8_t v_cacheInferType_2683_; uint8_t v___x_2684_; lean_object* v___x_2686_; 
v_trackZetaDelta_2674_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*7);
v_zetaDeltaSet_2675_ = lean_ctor_get(v___y_2577_, 1);
v_lctx_2676_ = lean_ctor_get(v___y_2577_, 2);
v_localInstances_2677_ = lean_ctor_get(v___y_2577_, 3);
v_defEqCtx_x3f_2678_ = lean_ctor_get(v___y_2577_, 4);
v_synthPendingDepth_2679_ = lean_ctor_get(v___y_2577_, 5);
v_canUnfold_x3f_2680_ = lean_ctor_get(v___y_2577_, 6);
v_univApprox_2681_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2682_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*7 + 2);
v_cacheInferType_2683_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*7 + 3);
v___x_2684_ = 0;
if (v_isShared_2673_ == 0)
{
v___x_2686_ = v___x_2672_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 0, v_foApprox_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 1, v_ctxApprox_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 2, v_quasiPatternApprox_2655_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 3, v_constApprox_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 4, v_isDefEqStuckEx_2657_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 5, v_unificationHints_2658_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 7, v_assignSyntheticOpaque_2659_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 8, v_offsetCnstrs_2660_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 9, v_transparency_2661_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 10, v_etaStruct_2662_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 11, v_univApprox_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 12, v_iota_2664_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 13, v_beta_2665_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 14, v_proj_2666_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 15, v_zeta_2667_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 16, v_zetaDelta_2668_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 17, v_zetaUnused_2669_);
lean_ctor_set_uint8(v_reuseFailAlloc_2774_, 18, v_zetaHave_2670_);
v___x_2686_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
uint64_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v_foApprox_2691_; uint8_t v_ctxApprox_2692_; uint8_t v_quasiPatternApprox_2693_; uint8_t v_constApprox_2694_; uint8_t v_isDefEqStuckEx_2695_; uint8_t v_unificationHints_2696_; uint8_t v_proofIrrelevance_2697_; uint8_t v_assignSyntheticOpaque_2698_; uint8_t v_offsetCnstrs_2699_; uint8_t v_etaStruct_2700_; uint8_t v_univApprox_2701_; uint8_t v_iota_2702_; uint8_t v_beta_2703_; uint8_t v_proj_2704_; uint8_t v_zeta_2705_; uint8_t v_zetaDelta_2706_; uint8_t v_zetaUnused_2707_; uint8_t v_zetaHave_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2773_; 
lean_ctor_set_uint8(v___x_2686_, 6, v___x_2684_);
v___x_2687_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2686_);
v___x_2688_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2688_, 0, v___x_2686_);
lean_ctor_set_uint64(v___x_2688_, sizeof(void*)*1, v___x_2687_);
lean_inc(v_canUnfold_x3f_2680_);
lean_inc(v_synthPendingDepth_2679_);
lean_inc(v_defEqCtx_x3f_2678_);
lean_inc_ref(v_localInstances_2677_);
lean_inc_ref(v_lctx_2676_);
lean_inc(v_zetaDeltaSet_2675_);
v___x_2689_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
lean_ctor_set(v___x_2689_, 1, v_zetaDeltaSet_2675_);
lean_ctor_set(v___x_2689_, 2, v_lctx_2676_);
lean_ctor_set(v___x_2689_, 3, v_localInstances_2677_);
lean_ctor_set(v___x_2689_, 4, v_defEqCtx_x3f_2678_);
lean_ctor_set(v___x_2689_, 5, v_synthPendingDepth_2679_);
lean_ctor_set(v___x_2689_, 6, v_canUnfold_x3f_2680_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7, v_trackZetaDelta_2674_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7 + 1, v_univApprox_2681_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2682_);
lean_ctor_set_uint8(v___x_2689_, sizeof(void*)*7 + 3, v_cacheInferType_2683_);
v___x_2690_ = l_Lean_Meta_Context_config(v___x_2689_);
v_foApprox_2691_ = lean_ctor_get_uint8(v___x_2690_, 0);
v_ctxApprox_2692_ = lean_ctor_get_uint8(v___x_2690_, 1);
v_quasiPatternApprox_2693_ = lean_ctor_get_uint8(v___x_2690_, 2);
v_constApprox_2694_ = lean_ctor_get_uint8(v___x_2690_, 3);
v_isDefEqStuckEx_2695_ = lean_ctor_get_uint8(v___x_2690_, 4);
v_unificationHints_2696_ = lean_ctor_get_uint8(v___x_2690_, 5);
v_proofIrrelevance_2697_ = lean_ctor_get_uint8(v___x_2690_, 6);
v_assignSyntheticOpaque_2698_ = lean_ctor_get_uint8(v___x_2690_, 7);
v_offsetCnstrs_2699_ = lean_ctor_get_uint8(v___x_2690_, 8);
v_etaStruct_2700_ = lean_ctor_get_uint8(v___x_2690_, 10);
v_univApprox_2701_ = lean_ctor_get_uint8(v___x_2690_, 11);
v_iota_2702_ = lean_ctor_get_uint8(v___x_2690_, 12);
v_beta_2703_ = lean_ctor_get_uint8(v___x_2690_, 13);
v_proj_2704_ = lean_ctor_get_uint8(v___x_2690_, 14);
v_zeta_2705_ = lean_ctor_get_uint8(v___x_2690_, 15);
v_zetaDelta_2706_ = lean_ctor_get_uint8(v___x_2690_, 16);
v_zetaUnused_2707_ = lean_ctor_get_uint8(v___x_2690_, 17);
v_zetaHave_2708_ = lean_ctor_get_uint8(v___x_2690_, 18);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2710_ = v___x_2690_;
v_isShared_2711_ = v_isSharedCheck_2773_;
goto v_resetjp_2709_;
}
else
{
lean_dec(v___x_2690_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2773_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v_config_2716_; 
v___x_2712_ = l_Lean_instInhabitedExpr;
v___x_2713_ = lean_array_get_borrowed(v___x_2712_, v_params_2572_, v_val_2648_);
lean_dec(v_val_2648_);
v___x_2714_ = 2;
if (v_isShared_2711_ == 0)
{
v_config_2716_ = v___x_2710_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 0, v_foApprox_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 1, v_ctxApprox_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 2, v_quasiPatternApprox_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 3, v_constApprox_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 4, v_isDefEqStuckEx_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 5, v_unificationHints_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 6, v_proofIrrelevance_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 7, v_assignSyntheticOpaque_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 8, v_offsetCnstrs_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 10, v_etaStruct_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 11, v_univApprox_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 12, v_iota_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 13, v_beta_2703_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 14, v_proj_2704_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 15, v_zeta_2705_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 16, v_zetaDelta_2706_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 17, v_zetaUnused_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2772_, 18, v_zetaHave_2708_);
v_config_2716_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
uint64_t v___x_2717_; uint64_t v___x_2718_; uint64_t v___x_2719_; uint64_t v___x_2720_; uint64_t v___x_2721_; uint64_t v_key_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_ctor_set_uint8(v_config_2716_, 9, v___x_2714_);
v___x_2717_ = l_Lean_Meta_Context_configKey(v___x_2689_);
lean_dec_ref_known(v___x_2689_, 7);
v___x_2718_ = 3ULL;
v___x_2719_ = lean_uint64_shift_right(v___x_2717_, v___x_2718_);
v___x_2720_ = lean_uint64_shift_left(v___x_2719_, v___x_2718_);
v___x_2721_ = lean_uint64_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___closed__0);
v_key_2722_ = lean_uint64_lor(v___x_2720_, v___x_2721_);
v___x_2723_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2723_, 0, v_config_2716_);
lean_ctor_set_uint64(v___x_2723_, sizeof(void*)*1, v_key_2722_);
lean_inc(v_canUnfold_x3f_2680_);
lean_inc(v_synthPendingDepth_2679_);
lean_inc(v_defEqCtx_x3f_2678_);
lean_inc_ref(v_localInstances_2677_);
lean_inc_ref(v_lctx_2676_);
lean_inc(v_zetaDeltaSet_2675_);
v___x_2724_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v_zetaDeltaSet_2675_);
lean_ctor_set(v___x_2724_, 2, v_lctx_2676_);
lean_ctor_set(v___x_2724_, 3, v_localInstances_2677_);
lean_ctor_set(v___x_2724_, 4, v_defEqCtx_x3f_2678_);
lean_ctor_set(v___x_2724_, 5, v_synthPendingDepth_2679_);
lean_ctor_set(v___x_2724_, 6, v_canUnfold_x3f_2680_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7, v_trackZetaDelta_2674_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 1, v_univApprox_2681_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2682_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 3, v_cacheInferType_2683_);
lean_inc(v___x_2646_);
lean_inc(v___x_2713_);
v___x_2725_ = l_Lean_Meta_isExprDefEq(v___x_2713_, v___x_2646_, v___x_2724_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec_ref_known(v___x_2724_, 7);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; uint8_t v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = lean_unbox(v_a_2726_);
lean_dec(v_a_2726_);
if (v___x_2727_ == 0)
{
lean_object* v_options_2728_; lean_object* v_inheritedTraceOptions_2729_; uint8_t v_hasTrace_2730_; 
v_options_2728_ = lean_ctor_get(v___y_2579_, 2);
v_inheritedTraceOptions_2729_ = lean_ctor_get(v___y_2579_, 13);
v_hasTrace_2730_ = lean_ctor_get_uint8(v_options_2728_, sizeof(void*)*1);
if (v_hasTrace_2730_ == 0)
{
lean_del_object(v___x_2650_);
goto v___jp_2731_;
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2733_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2729_, v_options_2728_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_del_object(v___x_2650_);
goto v___jp_2731_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2736_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2567_);
v___x_2737_ = l_Nat_reprFast(v_val_2567_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 3);
lean_ctor_set(v___x_2650_, 0, v___x_2737_);
v___x_2739_ = v___x_2650_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2740_ = l_Lean_MessageData_ofFormat(v___x_2739_);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2736_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
lean_inc(v_a_2575_);
v___x_2744_ = l_Nat_reprFast(v_a_2575_);
v___x_2745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
v___x_2746_ = l_Lean_MessageData_ofFormat(v___x_2745_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2743_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
lean_inc_ref(v_e_2570_);
v___x_2750_ = l_Lean_MessageData_ofExpr(v_e_2570_);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
lean_inc(v___x_2713_);
v___x_2754_ = l_Lean_MessageData_ofExpr(v___x_2713_);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
lean_inc(v___x_2646_);
v___x_2758_ = l_Lean_MessageData_ofExpr(v___x_2646_);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2733_, v___x_2759_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2762_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
lean_inc(v_a_2575_);
v___x_2762_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2566_, v_val_2567_, v_a_2575_, v___x_2611_, v_a_2761_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
v___y_2588_ = v___x_2762_;
goto v___jp_2587_;
}
else
{
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
return v___x_2760_;
}
}
}
}
v___jp_2731_:
{
lean_object* v___x_2732_; 
lean_inc(v_a_2575_);
v___x_2732_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2566_, v_val_2567_, v_a_2575_, v___x_2611_, v___x_2611_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
v___y_2588_ = v___x_2732_;
goto v___jp_2587_;
}
}
else
{
lean_del_object(v___x_2650_);
v_a_2583_ = v___x_2611_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_del_object(v___x_2650_);
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
v_a_2764_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2725_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2725_);
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
lean_dec(v___x_2647_);
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = 0;
lean_inc(v_a_2575_);
lean_inc(v___x_2646_);
v___x_2779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v___x_2573_, v_val_2566_, v_next_2571_, v_params_2572_, v___x_2646_, v_val_2567_, v_a_2575_, v___x_2574_, v___x_2777_, v___x_2778_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; uint8_t v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2781_ = lean_unbox(v_a_2780_);
lean_dec(v_a_2780_);
if (v___x_2781_ == 0)
{
lean_object* v_options_2782_; lean_object* v_inheritedTraceOptions_2783_; uint8_t v_hasTrace_2784_; 
v_options_2782_ = lean_ctor_get(v___y_2579_, 2);
v_inheritedTraceOptions_2783_ = lean_ctor_get(v___y_2579_, 13);
v_hasTrace_2784_ = lean_ctor_get_uint8(v_options_2782_, sizeof(void*)*1);
if (v_hasTrace_2784_ == 0)
{
goto v___jp_2785_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2787_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2788_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2783_, v_options_2782_, v___x_2788_);
if (v___x_2789_ == 0)
{
goto v___jp_2785_;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2790_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2567_);
v___x_2791_ = l_Nat_reprFast(v_val_2567_);
v___x_2792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
v___x_2793_ = l_Lean_MessageData_ofFormat(v___x_2792_);
v___x_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2790_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2794_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
lean_inc(v_a_2575_);
v___x_2797_ = l_Nat_reprFast(v_a_2575_);
v___x_2798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
v___x_2799_ = l_Lean_MessageData_ofFormat(v___x_2798_);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2796_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
lean_inc_ref(v_e_2570_);
v___x_2803_ = l_Lean_MessageData_ofExpr(v_e_2570_);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
lean_inc(v___x_2646_);
v___x_2807_ = l_Lean_MessageData_ofExpr(v___x_2646_);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2787_, v___x_2810_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
lean_inc(v_a_2575_);
v___x_2813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2566_, v_val_2567_, v_a_2575_, v___x_2611_, v_a_2812_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
v___y_2588_ = v___x_2813_;
goto v___jp_2587_;
}
else
{
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
return v___x_2811_;
}
}
}
v___jp_2785_:
{
lean_object* v___x_2786_; 
lean_inc(v_a_2575_);
v___x_2786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2566_, v_val_2567_, v_a_2575_, v___x_2611_, v___x_2611_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
v___y_2588_ = v___x_2786_;
goto v___jp_2587_;
}
}
else
{
v_a_2583_ = v___x_2611_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
v_a_2814_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2779_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2779_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
v_a_2822_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2644_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2644_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
v_a_2830_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2609_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2609_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
v___jp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = lean_nat_add(v_a_2575_, v___x_2584_);
lean_dec(v_a_2575_);
v_a_2575_ = v___x_2585_;
v_b_2576_ = v_a_2583_;
goto _start;
}
v___jp_2587_:
{
if (lean_obj_tag(v___y_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2598_; 
v_a_2589_ = lean_ctor_get(v___y_2588_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___y_2588_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2591_ = v___y_2588_;
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___y_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
if (lean_obj_tag(v_a_2589_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; 
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
v_a_2593_ = lean_ctor_get(v_a_2589_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v_a_2589_, 1);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v_a_2593_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
else
{
lean_object* v_a_2597_; 
lean_del_object(v___x_2591_);
v_a_2597_ = lean_ctor_get(v_a_2589_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v_a_2589_, 1);
v_a_2583_ = v_a_2597_;
goto v___jp_2582_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_a_2575_);
lean_dec_ref(v_e_2570_);
lean_dec(v_val_2567_);
v_a_2599_ = lean_ctor_get(v___y_2588_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___y_2588_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___y_2588_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___y_2588_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2838_, lean_object* v_val_2839_, lean_object* v_upperBound_2840_, lean_object* v_args_2841_, lean_object* v_e_2842_, lean_object* v_next_2843_, lean_object* v_params_2844_, lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v_a_2847_, lean_object* v_b_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
uint8_t v___x_44950__boxed_2854_; lean_object* v_res_2855_; 
v___x_44950__boxed_2854_ = lean_unbox(v___x_2846_);
v_res_2855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2838_, v_val_2839_, v_upperBound_2840_, v_args_2841_, v_e_2842_, v_next_2843_, v_params_2844_, v___x_2845_, v___x_44950__boxed_2854_, v_a_2847_, v_b_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___x_2845_);
lean_dec_ref(v_params_2844_);
lean_dec(v_next_2843_);
lean_dec_ref(v_args_2841_);
lean_dec(v_upperBound_2840_);
lean_dec(v_val_2838_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2858_, lean_object* v___x_2859_, lean_object* v_val_2860_, lean_object* v_e_2861_, lean_object* v_next_2862_, lean_object* v_params_2863_, lean_object* v___x_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_, lean_object* v_x_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
if (lean_obj_tag(v_x_2865_) == 5)
{
lean_object* v_fn_2873_; lean_object* v_arg_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_fn_2873_ = lean_ctor_get(v_x_2865_, 0);
lean_inc_ref(v_fn_2873_);
v_arg_2874_ = lean_ctor_get(v_x_2865_, 1);
lean_inc_ref(v_arg_2874_);
lean_dec_ref_known(v_x_2865_, 2);
v___x_2875_ = lean_array_set(v_x_2866_, v_x_2867_, v_arg_2874_);
v___x_2876_ = lean_unsigned_to_nat(1u);
v___x_2877_ = lean_nat_sub(v_x_2867_, v___x_2876_);
lean_dec(v_x_2867_);
v_x_2865_ = v_fn_2873_;
v_x_2866_ = v___x_2875_;
v_x_2867_ = v___x_2877_;
goto _start;
}
else
{
uint8_t v___x_2879_; 
lean_dec(v_x_2867_);
v___x_2879_ = l_Lean_Expr_isConst(v_x_2865_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec_ref(v_x_2866_);
lean_dec_ref(v_x_2865_);
lean_dec_ref(v_e_2861_);
v___x_2880_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = l_Lean_Expr_constName_x21(v_x_2865_);
lean_dec_ref(v_x_2865_);
v___x_2883_ = lean_unsigned_to_nat(0u);
v___x_2884_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2882_, v_preDefs_2858_, v___x_2883_);
lean_dec(v___x_2882_);
if (lean_obj_tag(v___x_2884_) == 1)
{
lean_object* v_val_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v_val_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_val_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_array_get_borrowed(v___x_2883_, v___x_2859_, v_val_2885_);
v___x_2888_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2860_, v_val_2885_, v___x_2887_, v_x_2866_, v_e_2861_, v_next_2862_, v_params_2863_, v___x_2864_, v___x_2879_, v___x_2883_, v___x_2886_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec_ref(v_x_2866_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2896_; 
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; 
v_unused_2897_ = lean_ctor_get(v___x_2888_, 0);
lean_dec(v_unused_2897_);
v___x_2890_ = v___x_2888_;
v_isShared_2891_ = v_isSharedCheck_2896_;
goto v_resetjp_2889_;
}
else
{
lean_dec(v___x_2888_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2896_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2892_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2892_);
v___x_2894_ = v___x_2890_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
v_a_2898_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2888_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2888_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec(v___x_2884_);
lean_dec_ref(v_x_2866_);
lean_dec_ref(v_e_2861_);
v___x_2906_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2908_, lean_object* v___x_2909_, lean_object* v_val_2910_, lean_object* v_e_2911_, lean_object* v_next_2912_, lean_object* v_params_2913_, lean_object* v___x_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_, lean_object* v_x_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2908_, v___x_2909_, v_val_2910_, v_e_2911_, v_next_2912_, v_params_2913_, v___x_2914_, v_x_2915_, v_x_2916_, v_x_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___x_2914_);
lean_dec_ref(v_params_2913_);
lean_dec(v_next_2912_);
lean_dec(v_val_2910_);
lean_dec_ref(v___x_2909_);
lean_dec_ref(v_preDefs_2908_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2924_, lean_object* v___x_2925_, lean_object* v_val_2926_, lean_object* v_a_2927_, lean_object* v_params_2928_, lean_object* v___x_2929_, lean_object* v_e_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_dummy_2936_; lean_object* v_nargs_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v_dummy_2936_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2937_ = l_Lean_Expr_getAppNumArgs(v_e_2930_);
lean_inc(v_nargs_2937_);
v___x_2938_ = lean_mk_array(v_nargs_2937_, v_dummy_2936_);
v___x_2939_ = lean_unsigned_to_nat(1u);
v___x_2940_ = lean_nat_sub(v_nargs_2937_, v___x_2939_);
lean_dec(v_nargs_2937_);
lean_inc_ref(v_e_2930_);
v___x_2941_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2924_, v___x_2925_, v_val_2926_, v_e_2930_, v_a_2927_, v_params_2928_, v___x_2929_, v_e_2930_, v___x_2938_, v___x_2940_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2942_, lean_object* v___x_2943_, lean_object* v_val_2944_, lean_object* v_a_2945_, lean_object* v_params_2946_, lean_object* v___x_2947_, lean_object* v_e_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2942_, v___x_2943_, v_val_2944_, v_a_2945_, v_params_2946_, v___x_2947_, v_e_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___x_2947_);
lean_dec_ref(v_params_2946_);
lean_dec(v_a_2945_);
lean_dec(v_val_2944_);
lean_dec_ref(v___x_2943_);
lean_dec_ref(v_preDefs_2942_);
return v_res_2954_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2959_ = lean_unsigned_to_nat(6u);
v___x_2960_ = lean_unsigned_to_nat(201u);
v___x_2961_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2962_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2963_ = l_mkPanicMessageWithDecl(v___x_2962_, v___x_2961_, v___x_2960_, v___x_2959_, v___x_2958_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2964_, lean_object* v___x_2965_, lean_object* v_a_2966_, lean_object* v_preDefs_2967_, lean_object* v_val_2968_, lean_object* v___f_2969_, lean_object* v___x_2970_, lean_object* v_params_2971_, lean_object* v_body_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2978_ = lean_array_get_size(v_params_2971_);
v___x_2979_ = lean_array_get_borrowed(v___x_2964_, v___x_2965_, v_a_2966_);
v___x_2980_ = lean_nat_dec_eq(v___x_2978_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec_ref(v_body_2972_);
lean_dec_ref(v_params_2971_);
lean_dec_ref(v___f_2969_);
lean_dec(v_val_2968_);
lean_dec_ref(v_preDefs_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v___x_2965_);
v___x_2981_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2982_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2981_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
return v___x_2982_;
}
else
{
lean_object* v___f_2983_; uint8_t v___x_2984_; lean_object* v___x_2985_; 
v___f_2983_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_2983_, 0, v_preDefs_2967_);
lean_closure_set(v___f_2983_, 1, v___x_2965_);
lean_closure_set(v___f_2983_, 2, v_val_2968_);
lean_closure_set(v___f_2983_, 3, v_a_2966_);
lean_closure_set(v___f_2983_, 4, v_params_2971_);
lean_closure_set(v___f_2983_, 5, v___x_2978_);
v___x_2984_ = 0;
v___x_2985_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2972_, v___f_2983_, v___f_2969_, v___x_2984_, v___x_2980_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v___x_2985_, 0);
lean_dec(v_unused_2993_);
v___x_2987_ = v___x_2985_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_dec(v___x_2985_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_2970_);
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2970_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_a_2994_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2985_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2985_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_3002_, lean_object* v___x_3003_, lean_object* v_a_3004_, lean_object* v_preDefs_3005_, lean_object* v_val_3006_, lean_object* v___f_3007_, lean_object* v___x_3008_, lean_object* v_params_3009_, lean_object* v_body_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_3002_, v___x_3003_, v_a_3004_, v_preDefs_3005_, v_val_3006_, v___f_3007_, v___x_3008_, v_params_3009_, v_body_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___x_3002_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_e_3017_);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v_preDefs_3033_, lean_object* v___x_3034_, lean_object* v_val_3035_, lean_object* v_upperBound_3036_, lean_object* v_a_3037_, lean_object* v_b_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
uint8_t v___x_3044_; 
v___x_3044_ = lean_nat_dec_lt(v_a_3037_, v_upperBound_3036_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
lean_dec(v_a_3037_);
lean_dec(v_val_3035_);
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_preDefs_3033_);
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v_b_3038_);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; lean_object* v_value_3047_; lean_object* v___f_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___f_3051_; uint8_t v___x_3052_; lean_object* v___x_3053_; 
v___x_3046_ = lean_array_fget_borrowed(v_preDefs_3033_, v_a_3037_);
v_value_3047_ = lean_ctor_get(v___x_3046_, 7);
v___f_3048_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3049_ = lean_unsigned_to_nat(0u);
v___x_3050_ = lean_box(0);
lean_inc(v_val_3035_);
lean_inc_ref(v_preDefs_3033_);
lean_inc(v_a_3037_);
lean_inc_ref(v___x_3034_);
v___f_3051_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3051_, 0, v___x_3049_);
lean_closure_set(v___f_3051_, 1, v___x_3034_);
lean_closure_set(v___f_3051_, 2, v_a_3037_);
lean_closure_set(v___f_3051_, 3, v_preDefs_3033_);
lean_closure_set(v___f_3051_, 4, v_val_3035_);
lean_closure_set(v___f_3051_, 5, v___f_3048_);
lean_closure_set(v___f_3051_, 6, v___x_3050_);
v___x_3052_ = 0;
lean_inc_ref(v_value_3047_);
v___x_3053_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3047_, v___f_3051_, v___x_3052_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec_ref_known(v___x_3053_, 1);
v___x_3054_ = lean_unsigned_to_nat(1u);
v___x_3055_ = lean_nat_add(v_a_3037_, v___x_3054_);
lean_dec(v_a_3037_);
v_a_3037_ = v___x_3055_;
v_b_3038_ = v___x_3050_;
goto _start;
}
else
{
lean_dec(v_a_3037_);
lean_dec(v_val_3035_);
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_preDefs_3033_);
return v___x_3053_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v_preDefs_3057_, lean_object* v___x_3058_, lean_object* v_val_3059_, lean_object* v_upperBound_3060_, lean_object* v_a_3061_, lean_object* v_b_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3057_, v___x_3058_, v_val_3059_, v_upperBound_3060_, v_a_3061_, v_b_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v_upperBound_3060_);
return v_res_3068_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3071_ = l_Lean_stringToMessageData(v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
size_t v_sz_3078_; size_t v___x_3079_; lean_object* v___x_3080_; 
v_sz_3078_ = lean_array_size(v_preDefs_3072_);
v___x_3079_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3072_);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3078_, v___x_3079_, v_preDefs_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; size_t v_sz_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc_n(v_a_3081_, 2);
lean_dec_ref_known(v___x_3080_, 1);
v_sz_3082_ = lean_array_size(v_a_3081_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3082_, v___x_3079_, v_a_3081_);
v___x_3084_ = l_Lean_Elab_FixedParams_Info_init(v_a_3081_);
v___x_3085_ = lean_st_mk_ref(v___x_3084_);
v___x_3086_ = lean_st_ref_take(v___x_3085_);
v___x_3087_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3086_);
v___x_3088_ = lean_st_ref_set(v___x_3085_, v___x_3087_);
v___x_3089_ = lean_array_get_size(v_preDefs_3072_);
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = lean_box(0);
lean_inc(v___x_3085_);
v___x_3092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3072_, v___x_3083_, v___x_3085_, v___x_3089_, v___x_3090_, v___x_3091_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3131_; 
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v___x_3092_, 0);
lean_dec(v_unused_3132_);
v___x_3094_ = v___x_3092_;
v_isShared_3095_ = v_isSharedCheck_3131_;
goto v_resetjp_3093_;
}
else
{
lean_dec(v___x_3092_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3131_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v_options_3097_; uint8_t v_hasTrace_3098_; 
v___x_3096_ = lean_st_ref_get(v___x_3085_);
lean_dec(v___x_3085_);
v_options_3097_ = lean_ctor_get(v_a_3075_, 2);
v_hasTrace_3098_ = lean_ctor_get_uint8(v_options_3097_, sizeof(void*)*1);
if (v_hasTrace_3098_ == 0)
{
lean_object* v___x_3100_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3096_);
v___x_3100_ = v___x_3094_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3096_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v_inheritedTraceOptions_3102_ = lean_ctor_get(v_a_3075_, 13);
v___x_3103_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3104_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3102_, v_options_3097_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3107_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3096_);
v___x_3107_ = v___x_3094_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3096_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_del_object(v___x_3094_);
v___x_3109_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3096_);
v___x_3110_ = l_Lean_Elab_FixedParams_Info_format(v___x_3096_);
v___x_3111_ = l_Std_Format_indentD(v___x_3110_);
v___x_3112_ = l_Lean_MessageData_ofFormat(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3109_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3103_, v___x_3113_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v___x_3114_, 0);
lean_dec(v_unused_3122_);
v___x_3116_ = v___x_3114_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_dec(v___x_3114_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3096_);
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3096_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v___x_3096_);
v_a_3123_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3114_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3114_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v___x_3085_);
v_a_3133_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3092_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3092_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_preDefs_3072_);
v_a_3141_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3080_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3080_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_upperBound_3156_, lean_object* v_val_3157_, lean_object* v_next_3158_, lean_object* v_params_3159_, lean_object* v___x_3160_, lean_object* v_val_3161_, lean_object* v_next_3162_, uint8_t v___x_3163_, lean_object* v_inst_3164_, lean_object* v_R_3165_, lean_object* v_a_3166_, uint8_t v_b_3167_, lean_object* v_c_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_3156_, v_val_3157_, v_next_3158_, v_params_3159_, v___x_3160_, v_val_3161_, v_next_3162_, v___x_3163_, v_a_3166_, v_b_3167_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3175_ = _args[0];
lean_object* v_val_3176_ = _args[1];
lean_object* v_next_3177_ = _args[2];
lean_object* v_params_3178_ = _args[3];
lean_object* v___x_3179_ = _args[4];
lean_object* v_val_3180_ = _args[5];
lean_object* v_next_3181_ = _args[6];
lean_object* v___x_3182_ = _args[7];
lean_object* v_inst_3183_ = _args[8];
lean_object* v_R_3184_ = _args[9];
lean_object* v_a_3185_ = _args[10];
lean_object* v_b_3186_ = _args[11];
lean_object* v_c_3187_ = _args[12];
lean_object* v___y_3188_ = _args[13];
lean_object* v___y_3189_ = _args[14];
lean_object* v___y_3190_ = _args[15];
lean_object* v___y_3191_ = _args[16];
lean_object* v___y_3192_ = _args[17];
_start:
{
uint8_t v___x_45899__boxed_3193_; uint8_t v_b_boxed_3194_; lean_object* v_res_3195_; 
v___x_45899__boxed_3193_ = lean_unbox(v___x_3182_);
v_b_boxed_3194_ = lean_unbox(v_b_3186_);
v_res_3195_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_upperBound_3175_, v_val_3176_, v_next_3177_, v_params_3178_, v___x_3179_, v_val_3180_, v_next_3181_, v___x_45899__boxed_3193_, v_inst_3183_, v_R_3184_, v_a_3185_, v_b_boxed_3194_, v_c_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v_val_3180_);
lean_dec_ref(v_params_3178_);
lean_dec(v_next_3177_);
lean_dec(v_val_3176_);
lean_dec(v_upperBound_3175_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3196_, lean_object* v_val_3197_, lean_object* v_upperBound_3198_, lean_object* v_args_3199_, lean_object* v_e_3200_, lean_object* v_next_3201_, lean_object* v_params_3202_, lean_object* v___x_3203_, uint8_t v___x_3204_, lean_object* v_inst_3205_, lean_object* v_R_3206_, lean_object* v_a_3207_, lean_object* v_b_3208_, lean_object* v_c_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3196_, v_val_3197_, v_upperBound_3198_, v_args_3199_, v_e_3200_, v_next_3201_, v_params_3202_, v___x_3203_, v___x_3204_, v_a_3207_, v_b_3208_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3216_ = _args[0];
lean_object* v_val_3217_ = _args[1];
lean_object* v_upperBound_3218_ = _args[2];
lean_object* v_args_3219_ = _args[3];
lean_object* v_e_3220_ = _args[4];
lean_object* v_next_3221_ = _args[5];
lean_object* v_params_3222_ = _args[6];
lean_object* v___x_3223_ = _args[7];
lean_object* v___x_3224_ = _args[8];
lean_object* v_inst_3225_ = _args[9];
lean_object* v_R_3226_ = _args[10];
lean_object* v_a_3227_ = _args[11];
lean_object* v_b_3228_ = _args[12];
lean_object* v_c_3229_ = _args[13];
lean_object* v___y_3230_ = _args[14];
lean_object* v___y_3231_ = _args[15];
lean_object* v___y_3232_ = _args[16];
lean_object* v___y_3233_ = _args[17];
lean_object* v___y_3234_ = _args[18];
_start:
{
uint8_t v___x_45934__boxed_3235_; lean_object* v_res_3236_; 
v___x_45934__boxed_3235_ = lean_unbox(v___x_3224_);
v_res_3236_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3216_, v_val_3217_, v_upperBound_3218_, v_args_3219_, v_e_3220_, v_next_3221_, v_params_3222_, v___x_3223_, v___x_45934__boxed_3235_, v_inst_3225_, v_R_3226_, v_a_3227_, v_b_3228_, v_c_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___x_3223_);
lean_dec_ref(v_params_3222_);
lean_dec(v_next_3221_);
lean_dec_ref(v_args_3219_);
lean_dec(v_upperBound_3218_);
lean_dec(v_val_3216_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v_preDefs_3237_, lean_object* v___x_3238_, lean_object* v_val_3239_, lean_object* v_upperBound_3240_, lean_object* v_inst_3241_, lean_object* v_R_3242_, lean_object* v_a_3243_, lean_object* v_b_3244_, lean_object* v_c_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3237_, v___x_3238_, v_val_3239_, v_upperBound_3240_, v_a_3243_, v_b_3244_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v_preDefs_3252_, lean_object* v___x_3253_, lean_object* v_val_3254_, lean_object* v_upperBound_3255_, lean_object* v_inst_3256_, lean_object* v_R_3257_, lean_object* v_a_3258_, lean_object* v_b_3259_, lean_object* v_c_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v_preDefs_3252_, v___x_3253_, v_val_3254_, v_upperBound_3255_, v_inst_3256_, v_R_3257_, v_a_3258_, v_b_3259_, v_c_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v_upperBound_3255_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3267_, lean_object* v___x_3268_, lean_object* v_pre_3269_, lean_object* v_post_3270_, uint8_t v_usedLetOnly_3271_, uint8_t v_skipConstInApp_3272_, uint8_t v_skipInstances_3273_, lean_object* v___x_3274_, lean_object* v_inst_3275_, lean_object* v_R_3276_, lean_object* v_a_3277_, lean_object* v_b_3278_, lean_object* v_c_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3267_, v___x_3268_, v_pre_3269_, v_post_3270_, v_usedLetOnly_3271_, v_skipConstInApp_3272_, v_skipInstances_3273_, v_a_3277_, v_b_3278_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3287_ = _args[0];
lean_object* v___x_3288_ = _args[1];
lean_object* v_pre_3289_ = _args[2];
lean_object* v_post_3290_ = _args[3];
lean_object* v_usedLetOnly_3291_ = _args[4];
lean_object* v_skipConstInApp_3292_ = _args[5];
lean_object* v_skipInstances_3293_ = _args[6];
lean_object* v___x_3294_ = _args[7];
lean_object* v_inst_3295_ = _args[8];
lean_object* v_R_3296_ = _args[9];
lean_object* v_a_3297_ = _args[10];
lean_object* v_b_3298_ = _args[11];
lean_object* v_c_3299_ = _args[12];
lean_object* v___y_3300_ = _args[13];
lean_object* v___y_3301_ = _args[14];
lean_object* v___y_3302_ = _args[15];
lean_object* v___y_3303_ = _args[16];
lean_object* v___y_3304_ = _args[17];
lean_object* v___y_3305_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3306_; uint8_t v_skipConstInApp_boxed_3307_; uint8_t v_skipInstances_boxed_3308_; lean_object* v_res_3309_; 
v_usedLetOnly_boxed_3306_ = lean_unbox(v_usedLetOnly_3291_);
v_skipConstInApp_boxed_3307_ = lean_unbox(v_skipConstInApp_3292_);
v_skipInstances_boxed_3308_ = lean_unbox(v_skipInstances_3293_);
v_res_3309_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3287_, v___x_3288_, v_pre_3289_, v_post_3290_, v_usedLetOnly_boxed_3306_, v_skipConstInApp_boxed_3307_, v_skipInstances_boxed_3308_, v___x_3294_, v_inst_3295_, v_R_3296_, v_a_3297_, v_b_3298_, v_c_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec(v___x_3294_);
lean_dec_ref(v___x_3288_);
lean_dec(v_upperBound_3287_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3310_, lean_object* v_m_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3311_, v_a_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3314_, lean_object* v_m_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3314_, v_m_3315_, v_a_3316_);
lean_dec_ref(v_a_3316_);
lean_dec_ref(v_m_3315_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3318_, lean_object* v_name_3319_, uint8_t v_bi_3320_, lean_object* v_type_3321_, lean_object* v_k_3322_, uint8_t v_kind_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3319_, v_bi_3320_, v_type_3321_, v_k_3322_, v_kind_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3331_, lean_object* v_name_3332_, lean_object* v_bi_3333_, lean_object* v_type_3334_, lean_object* v_k_3335_, lean_object* v_kind_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
uint8_t v_bi_boxed_3343_; uint8_t v_kind_boxed_3344_; lean_object* v_res_3345_; 
v_bi_boxed_3343_ = lean_unbox(v_bi_3333_);
v_kind_boxed_3344_ = lean_unbox(v_kind_3336_);
v_res_3345_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3331_, v_name_3332_, v_bi_boxed_3343_, v_type_3334_, v_k_3335_, v_kind_boxed_3344_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3346_, lean_object* v_name_3347_, lean_object* v_type_3348_, lean_object* v_val_3349_, lean_object* v_k_3350_, uint8_t v_nondep_3351_, uint8_t v_kind_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3347_, v_type_3348_, v_val_3349_, v_k_3350_, v_nondep_3351_, v_kind_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3360_, lean_object* v_name_3361_, lean_object* v_type_3362_, lean_object* v_val_3363_, lean_object* v_k_3364_, lean_object* v_nondep_3365_, lean_object* v_kind_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v_nondep_boxed_3373_; uint8_t v_kind_boxed_3374_; lean_object* v_res_3375_; 
v_nondep_boxed_3373_ = lean_unbox(v_nondep_3365_);
v_kind_boxed_3374_ = lean_unbox(v_kind_3366_);
v_res_3375_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3360_, v_name_3361_, v_type_3362_, v_val_3363_, v_k_3364_, v_nondep_boxed_3373_, v_kind_boxed_3374_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3376_, lean_object* v_ref_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3377_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3384_, lean_object* v_ref_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3384_, v_ref_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3392_, lean_object* v_x_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3401_, lean_object* v_x_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3401_, v_x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3410_, lean_object* v_m_3411_, lean_object* v_a_3412_, lean_object* v_b_3413_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3411_, v_a_3412_, v_b_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3415_, lean_object* v_a_3416_, lean_object* v_x_3417_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3416_, v_x_3417_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3419_, lean_object* v_a_3420_, lean_object* v_x_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3419_, v_a_3420_, v_x_3421_);
lean_dec(v_x_3421_);
lean_dec_ref(v_a_3420_);
return v_res_3422_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3423_, lean_object* v_a_3424_, lean_object* v_x_3425_){
_start:
{
uint8_t v___x_3426_; 
v___x_3426_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3424_, v_x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3427_, lean_object* v_a_3428_, lean_object* v_x_3429_){
_start:
{
uint8_t v_res_3430_; lean_object* v_r_3431_; 
v_res_3430_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3427_, v_a_3428_, v_x_3429_);
lean_dec(v_x_3429_);
lean_dec_ref(v_a_3428_);
v_r_3431_ = lean_box(v_res_3430_);
return v_r_3431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3432_, lean_object* v_data_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3435_, lean_object* v_a_3436_, lean_object* v_b_3437_, lean_object* v_x_3438_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3436_, v_b_3437_, v_x_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3440_, lean_object* v_i_3441_, lean_object* v_source_3442_, lean_object* v_target_3443_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3441_, v_source_3442_, v_target_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3445_, lean_object* v_x_3446_, lean_object* v_x_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3446_, v_x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3462_, lean_object* v_x_3463_){
_start:
{
if (lean_obj_tag(v_x_3462_) == 0)
{
lean_object* v___x_3464_; 
v___x_3464_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3464_;
}
else
{
lean_object* v_val_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3476_; 
v_val_3465_ = lean_ctor_get(v_x_3462_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_x_3462_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3467_ = v_x_3462_;
v_isShared_3468_ = v_isSharedCheck_3476_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_val_3465_);
lean_dec(v_x_3462_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3476_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3469_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3470_ = l_Nat_reprFast(v_val_3465_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set_tag(v___x_3467_, 3);
lean_ctor_set(v___x_3467_, 0, v___x_3470_);
v___x_3472_ = v___x_3467_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3469_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Repr_addAppParen(v___x_3473_, v_x_3463_);
return v___x_3474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3477_, lean_object* v_x_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3477_, v_x_3478_);
lean_dec(v_x_3478_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3480_, lean_object* v_x_3481_, lean_object* v_x_3482_){
_start:
{
if (lean_obj_tag(v_x_3482_) == 0)
{
lean_dec(v_x_3480_);
return v_x_3481_;
}
else
{
lean_object* v_head_3483_; lean_object* v_tail_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3495_; 
v_head_3483_ = lean_ctor_get(v_x_3482_, 0);
v_tail_3484_ = lean_ctor_get(v_x_3482_, 1);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_x_3482_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3486_ = v_x_3482_;
v_isShared_3487_ = v_isSharedCheck_3495_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_tail_3484_);
lean_inc(v_head_3483_);
lean_dec(v_x_3482_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3495_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
lean_inc(v_x_3480_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set_tag(v___x_3486_, 5);
lean_ctor_set(v___x_3486_, 1, v_x_3480_);
lean_ctor_set(v___x_3486_, 0, v_x_3481_);
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_x_3481_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_x_3480_);
v___x_3489_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3490_ = lean_unsigned_to_nat(0u);
v___x_3491_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3483_, v___x_3490_);
v___x_3492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3489_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v_x_3481_ = v___x_3492_;
v_x_3482_ = v_tail_3484_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3496_, lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
if (lean_obj_tag(v_x_3498_) == 0)
{
lean_dec(v_x_3496_);
return v_x_3497_;
}
else
{
lean_object* v_head_3499_; lean_object* v_tail_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3511_; 
v_head_3499_ = lean_ctor_get(v_x_3498_, 0);
v_tail_3500_ = lean_ctor_get(v_x_3498_, 1);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_x_3498_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3502_ = v_x_3498_;
v_isShared_3503_ = v_isSharedCheck_3511_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_tail_3500_);
lean_inc(v_head_3499_);
lean_dec(v_x_3498_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3511_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
lean_inc(v_x_3496_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set_tag(v___x_3502_, 5);
lean_ctor_set(v___x_3502_, 1, v_x_3496_);
lean_ctor_set(v___x_3502_, 0, v_x_3497_);
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_x_3497_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_x_3496_);
v___x_3505_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3506_ = lean_unsigned_to_nat(0u);
v___x_3507_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3499_, v___x_3506_);
v___x_3508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3505_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v___x_3509_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3496_, v___x_3508_, v_tail_3500_);
return v___x_3509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3512_){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3512_, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3515_, lean_object* v_x_3516_){
_start:
{
if (lean_obj_tag(v_x_3515_) == 0)
{
lean_object* v___x_3517_; 
lean_dec(v_x_3516_);
v___x_3517_ = lean_box(0);
return v___x_3517_;
}
else
{
lean_object* v_tail_3518_; 
v_tail_3518_ = lean_ctor_get(v_x_3515_, 1);
if (lean_obj_tag(v_tail_3518_) == 0)
{
lean_object* v_head_3519_; lean_object* v___x_3520_; 
lean_dec(v_x_3516_);
v_head_3519_ = lean_ctor_get(v_x_3515_, 0);
lean_inc(v_head_3519_);
lean_dec_ref_known(v_x_3515_, 2);
v___x_3520_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3519_);
return v___x_3520_;
}
else
{
lean_object* v_head_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_inc(v_tail_3518_);
v_head_3521_ = lean_ctor_get(v_x_3515_, 0);
lean_inc(v_head_3521_);
lean_dec_ref_known(v_x_3515_, 2);
v___x_3522_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3521_);
v___x_3523_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3516_, v___x_3522_, v_tail_3518_);
return v___x_3523_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3532_ = lean_string_length(v___x_3531_);
return v___x_3532_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3534_ = lean_nat_to_int(v___x_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3540_){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3541_ = lean_array_get_size(v_xs_3540_);
v___x_3542_ = lean_unsigned_to_nat(0u);
v___x_3543_ = lean_nat_dec_eq(v___x_3541_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3544_ = lean_array_to_list(v_xs_3540_);
v___x_3545_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3546_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3544_, v___x_3545_);
v___x_3547_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3548_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___x_3546_);
v___x_3550_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3547_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_Std_Format_fill(v___x_3552_);
return v___x_3553_;
}
else
{
lean_object* v___x_3554_; 
lean_dec_ref(v_xs_3540_);
v___x_3554_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3554_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_){
_start:
{
if (lean_obj_tag(v_x_3557_) == 0)
{
lean_dec(v_x_3555_);
return v_x_3556_;
}
else
{
lean_object* v_head_3558_; lean_object* v_tail_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3569_; 
v_head_3558_ = lean_ctor_get(v_x_3557_, 0);
v_tail_3559_ = lean_ctor_get(v_x_3557_, 1);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_x_3557_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3561_ = v_x_3557_;
v_isShared_3562_ = v_isSharedCheck_3569_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_tail_3559_);
lean_inc(v_head_3558_);
lean_dec(v_x_3557_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3569_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
lean_inc(v_x_3555_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 5);
lean_ctor_set(v___x_3561_, 1, v_x_3555_);
lean_ctor_set(v___x_3561_, 0, v_x_3556_);
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_x_3556_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_x_3555_);
v___x_3564_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3558_);
v___x_3566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v_x_3556_ = v___x_3566_;
v_x_3557_ = v_tail_3559_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3570_, lean_object* v_x_3571_){
_start:
{
if (lean_obj_tag(v_x_3570_) == 0)
{
lean_object* v___x_3572_; 
lean_dec(v_x_3571_);
v___x_3572_ = lean_box(0);
return v___x_3572_;
}
else
{
lean_object* v_tail_3573_; 
v_tail_3573_ = lean_ctor_get(v_x_3570_, 1);
if (lean_obj_tag(v_tail_3573_) == 0)
{
lean_object* v_head_3574_; lean_object* v___x_3575_; 
lean_dec(v_x_3571_);
v_head_3574_ = lean_ctor_get(v_x_3570_, 0);
lean_inc(v_head_3574_);
lean_dec_ref_known(v_x_3570_, 2);
v___x_3575_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3574_);
return v___x_3575_;
}
else
{
lean_object* v_head_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_inc(v_tail_3573_);
v_head_3576_ = lean_ctor_get(v_x_3570_, 0);
lean_inc(v_head_3576_);
lean_dec_ref_known(v_x_3570_, 2);
v___x_3577_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3576_);
v___x_3578_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3571_, v___x_3577_, v_tail_3573_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3579_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3580_ = lean_array_get_size(v_xs_3579_);
v___x_3581_ = lean_unsigned_to_nat(0u);
v___x_3582_ = lean_nat_dec_eq(v___x_3580_, v___x_3581_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3583_ = lean_array_to_list(v_xs_3579_);
v___x_3584_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3585_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3583_, v___x_3584_);
v___x_3586_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3587_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
lean_ctor_set(v___x_3588_, 1, v___x_3585_);
v___x_3589_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3588_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
v___x_3591_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3586_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = l_Std_Format_fill(v___x_3591_);
return v___x_3592_;
}
else
{
lean_object* v___x_3593_; 
lean_dec_ref(v_xs_3579_);
v___x_3593_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3593_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3594_, lean_object* v_x_3595_, lean_object* v_x_3596_){
_start:
{
if (lean_obj_tag(v_x_3596_) == 0)
{
lean_dec(v_x_3594_);
return v_x_3595_;
}
else
{
lean_object* v_head_3597_; lean_object* v_tail_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3609_; 
v_head_3597_ = lean_ctor_get(v_x_3596_, 0);
v_tail_3598_ = lean_ctor_get(v_x_3596_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_x_3596_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3600_ = v_x_3596_;
v_isShared_3601_ = v_isSharedCheck_3609_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_tail_3598_);
lean_inc(v_head_3597_);
lean_dec(v_x_3596_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3609_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
lean_inc(v_x_3594_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set_tag(v___x_3600_, 5);
lean_ctor_set(v___x_3600_, 1, v_x_3594_);
lean_ctor_set(v___x_3600_, 0, v_x_3595_);
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_x_3595_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_x_3594_);
v___x_3603_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3604_ = l_Nat_reprFast(v_head_3597_);
v___x_3605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
v___x_3606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3603_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v_x_3595_ = v___x_3606_;
v_x_3596_ = v_tail_3598_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_){
_start:
{
if (lean_obj_tag(v_x_3612_) == 0)
{
lean_dec(v_x_3610_);
return v_x_3611_;
}
else
{
lean_object* v_head_3613_; lean_object* v_tail_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3625_; 
v_head_3613_ = lean_ctor_get(v_x_3612_, 0);
v_tail_3614_ = lean_ctor_get(v_x_3612_, 1);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_x_3612_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3616_ = v_x_3612_;
v_isShared_3617_ = v_isSharedCheck_3625_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_tail_3614_);
lean_inc(v_head_3613_);
lean_dec(v_x_3612_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3625_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
lean_inc(v_x_3610_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 5);
lean_ctor_set(v___x_3616_, 1, v_x_3610_);
lean_ctor_set(v___x_3616_, 0, v_x_3611_);
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_x_3611_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_x_3610_);
v___x_3619_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3620_ = l_Nat_reprFast(v_head_3613_);
v___x_3621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
v___x_3622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3619_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3610_, v___x_3622_, v_tail_3614_);
return v___x_3623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = l_Nat_reprFast(v___y_3626_);
v___x_3628_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3629_, lean_object* v_x_3630_){
_start:
{
if (lean_obj_tag(v_x_3629_) == 0)
{
lean_object* v___x_3631_; 
lean_dec(v_x_3630_);
v___x_3631_ = lean_box(0);
return v___x_3631_;
}
else
{
lean_object* v_tail_3632_; 
v_tail_3632_ = lean_ctor_get(v_x_3629_, 1);
if (lean_obj_tag(v_tail_3632_) == 0)
{
lean_object* v_head_3633_; lean_object* v___x_3634_; 
lean_dec(v_x_3630_);
v_head_3633_ = lean_ctor_get(v_x_3629_, 0);
lean_inc(v_head_3633_);
lean_dec_ref_known(v_x_3629_, 2);
v___x_3634_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3633_);
return v___x_3634_;
}
else
{
lean_object* v_head_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
lean_inc(v_tail_3632_);
v_head_3635_ = lean_ctor_get(v_x_3629_, 0);
lean_inc(v_head_3635_);
lean_dec_ref_known(v_x_3629_, 2);
v___x_3636_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3635_);
v___x_3637_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3630_, v___x_3636_, v_tail_3632_);
return v___x_3637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3638_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3639_ = lean_array_get_size(v_xs_3638_);
v___x_3640_ = lean_unsigned_to_nat(0u);
v___x_3641_ = lean_nat_dec_eq(v___x_3639_, v___x_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3642_ = lean_array_to_list(v_xs_3638_);
v___x_3643_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3644_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3642_, v___x_3643_);
v___x_3645_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3646_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
lean_ctor_set(v___x_3647_, 1, v___x_3644_);
v___x_3648_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3645_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = l_Std_Format_fill(v___x_3650_);
return v___x_3651_;
}
else
{
lean_object* v___x_3652_; 
lean_dec_ref(v_xs_3638_);
v___x_3652_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3653_, lean_object* v_x_3654_, lean_object* v_x_3655_){
_start:
{
if (lean_obj_tag(v_x_3655_) == 0)
{
lean_dec(v_x_3653_);
return v_x_3654_;
}
else
{
lean_object* v_head_3656_; lean_object* v_tail_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3667_; 
v_head_3656_ = lean_ctor_get(v_x_3655_, 0);
v_tail_3657_ = lean_ctor_get(v_x_3655_, 1);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_x_3655_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3659_ = v_x_3655_;
v_isShared_3660_ = v_isSharedCheck_3667_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_tail_3657_);
lean_inc(v_head_3656_);
lean_dec(v_x_3655_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3667_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
lean_inc(v_x_3653_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set_tag(v___x_3659_, 5);
lean_ctor_set(v___x_3659_, 1, v_x_3653_);
lean_ctor_set(v___x_3659_, 0, v_x_3654_);
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_x_3654_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_x_3653_);
v___x_3662_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3656_);
v___x_3664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v_x_3654_ = v___x_3664_;
v_x_3655_ = v_tail_3657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3668_, lean_object* v_x_3669_){
_start:
{
if (lean_obj_tag(v_x_3668_) == 0)
{
lean_object* v___x_3670_; 
lean_dec(v_x_3669_);
v___x_3670_ = lean_box(0);
return v___x_3670_;
}
else
{
lean_object* v_tail_3671_; 
v_tail_3671_ = lean_ctor_get(v_x_3668_, 1);
if (lean_obj_tag(v_tail_3671_) == 0)
{
lean_object* v_head_3672_; lean_object* v___x_3673_; 
lean_dec(v_x_3669_);
v_head_3672_ = lean_ctor_get(v_x_3668_, 0);
lean_inc(v_head_3672_);
lean_dec_ref_known(v_x_3668_, 2);
v___x_3673_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3672_);
return v___x_3673_;
}
else
{
lean_object* v_head_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_inc(v_tail_3671_);
v_head_3674_ = lean_ctor_get(v_x_3668_, 0);
lean_inc(v_head_3674_);
lean_dec_ref_known(v_x_3668_, 2);
v___x_3675_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3674_);
v___x_3676_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3669_, v___x_3675_, v_tail_3671_);
return v___x_3676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3677_){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
v___x_3678_ = lean_array_get_size(v_xs_3677_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v___x_3680_ = lean_nat_dec_eq(v___x_3678_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3681_ = lean_array_to_list(v_xs_3677_);
v___x_3682_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3683_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3681_, v___x_3682_);
v___x_3684_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3685_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v___x_3683_);
v___x_3687_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3684_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = l_Std_Format_fill(v___x_3689_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; 
lean_dec_ref(v_xs_3677_);
v___x_3691_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3691_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_){
_start:
{
if (lean_obj_tag(v_x_3694_) == 0)
{
lean_dec(v_x_3692_);
return v_x_3693_;
}
else
{
lean_object* v_head_3695_; lean_object* v_tail_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3706_; 
v_head_3695_ = lean_ctor_get(v_x_3694_, 0);
v_tail_3696_ = lean_ctor_get(v_x_3694_, 1);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_x_3694_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3698_ = v_x_3694_;
v_isShared_3699_ = v_isSharedCheck_3706_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_tail_3696_);
lean_inc(v_head_3695_);
lean_dec(v_x_3694_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3706_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
lean_inc(v_x_3692_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set_tag(v___x_3698_, 5);
lean_ctor_set(v___x_3698_, 1, v_x_3692_);
lean_ctor_set(v___x_3698_, 0, v_x_3693_);
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_x_3693_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_x_3692_);
v___x_3701_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3695_);
v___x_3703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v_x_3693_ = v___x_3703_;
v_x_3694_ = v_tail_3696_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3707_, lean_object* v_x_3708_){
_start:
{
if (lean_obj_tag(v_x_3707_) == 0)
{
lean_object* v___x_3709_; 
lean_dec(v_x_3708_);
v___x_3709_ = lean_box(0);
return v___x_3709_;
}
else
{
lean_object* v_tail_3710_; 
v_tail_3710_ = lean_ctor_get(v_x_3707_, 1);
if (lean_obj_tag(v_tail_3710_) == 0)
{
lean_object* v_head_3711_; lean_object* v___x_3712_; 
lean_dec(v_x_3708_);
v_head_3711_ = lean_ctor_get(v_x_3707_, 0);
lean_inc(v_head_3711_);
lean_dec_ref_known(v_x_3707_, 2);
v___x_3712_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3711_);
return v___x_3712_;
}
else
{
lean_object* v_head_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
lean_inc(v_tail_3710_);
v_head_3713_ = lean_ctor_get(v_x_3707_, 0);
lean_inc(v_head_3713_);
lean_dec_ref_known(v_x_3707_, 2);
v___x_3714_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3713_);
v___x_3715_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3708_, v___x_3714_, v_tail_3710_);
return v___x_3715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3716_){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3717_ = lean_array_get_size(v_xs_3716_);
v___x_3718_ = lean_unsigned_to_nat(0u);
v___x_3719_ = lean_nat_dec_eq(v___x_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3720_ = lean_array_to_list(v_xs_3716_);
v___x_3721_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3722_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3720_, v___x_3721_);
v___x_3723_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3724_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
lean_ctor_set(v___x_3725_, 1, v___x_3722_);
v___x_3726_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3723_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = l_Std_Format_fill(v___x_3728_);
return v___x_3729_;
}
else
{
lean_object* v___x_3730_; 
lean_dec_ref(v_xs_3716_);
v___x_3730_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3730_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = lean_unsigned_to_nat(12u);
v___x_3745_ = lean_nat_to_int(v___x_3744_);
return v___x_3745_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = lean_unsigned_to_nat(9u);
v___x_3750_ = lean_nat_to_int(v___x_3749_);
return v___x_3750_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = lean_unsigned_to_nat(11u);
v___x_3755_ = lean_nat_to_int(v___x_3754_);
return v___x_3755_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3758_ = lean_string_length(v___x_3757_);
return v___x_3758_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3760_ = lean_nat_to_int(v___x_3759_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3765_){
_start:
{
lean_object* v_numFixed_3766_; lean_object* v_perms_3767_; lean_object* v_revDeps_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v_numFixed_3766_ = lean_ctor_get(v_x_3765_, 0);
lean_inc(v_numFixed_3766_);
v_perms_3767_ = lean_ctor_get(v_x_3765_, 1);
lean_inc_ref(v_perms_3767_);
v_revDeps_3768_ = lean_ctor_get(v_x_3765_, 2);
lean_inc_ref(v_revDeps_3768_);
lean_dec_ref(v_x_3765_);
v___x_3769_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3770_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3771_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3772_ = l_Nat_reprFast(v_numFixed_3766_);
v___x_3773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
v___x_3774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3771_);
lean_ctor_set(v___x_3774_, 1, v___x_3773_);
v___x_3775_ = 0;
v___x_3776_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3776_, 0, v___x_3774_);
lean_ctor_set_uint8(v___x_3776_, sizeof(void*)*1, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3770_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = lean_box(1);
v___x_3781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3779_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set(v___x_3784_, 1, v___x_3769_);
v___x_3785_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3786_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3767_);
v___x_3787_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
lean_ctor_set_uint8(v___x_3788_, sizeof(void*)*1, v___x_3775_);
v___x_3789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3784_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
lean_ctor_set(v___x_3790_, 1, v___x_3778_);
v___x_3791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
lean_ctor_set(v___x_3791_, 1, v___x_3780_);
v___x_3792_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set(v___x_3794_, 1, v___x_3769_);
v___x_3795_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3796_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3768_);
v___x_3797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set_uint8(v___x_3798_, sizeof(void*)*1, v___x_3775_);
v___x_3799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3794_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3801_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v___x_3799_);
v___x_3803_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3802_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3800_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*1, v___x_3775_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3807_, lean_object* v_prec_3808_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3810_, lean_object* v_prec_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3810_, v_prec_3811_);
lean_dec(v_prec_3811_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___f_3821_; lean_object* v___x_5797__overap_3822_; lean_object* v___x_3823_; 
v___f_3821_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5797__overap_3822_ = lean_panic_fn_borrowed(v___f_3821_, v_msg_3815_);
lean_inc(v___y_3819_);
lean_inc_ref(v___y_3818_);
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
v___x_3823_ = lean_apply_5(v___x_5797__overap_3822_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, lean_box(0));
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v___f_3837_; lean_object* v___x_5807__overap_3838_; lean_object* v___x_3839_; 
v___f_3837_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5807__overap_3838_ = lean_panic_fn_borrowed(v___f_3837_, v_msg_3831_);
lean_inc(v___y_3835_);
lean_inc_ref(v___y_3834_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
v___x_3839_ = lean_apply_5(v___x_5807__overap_3838_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, lean_box(0));
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v___f_3853_; lean_object* v___x_5817__overap_3854_; lean_object* v___x_3855_; 
v___f_3853_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5817__overap_3854_ = lean_panic_fn_borrowed(v___f_3853_, v_msg_3847_);
lean_inc(v___y_3851_);
lean_inc_ref(v___y_3850_);
lean_inc(v___y_3849_);
lean_inc_ref(v___y_3848_);
v___x_3855_ = lean_apply_5(v___x_5817__overap_3854_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, lean_box(0));
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
return v_res_3862_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3866_ = lean_unsigned_to_nat(12u);
v___x_3867_ = lean_unsigned_to_nat(294u);
v___x_3868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3869_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3870_ = l_mkPanicMessageWithDecl(v___x_3869_, v___x_3868_, v___x_3867_, v___x_3866_, v___x_3865_);
return v___x_3870_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3873_ = lean_unsigned_to_nat(12u);
v___x_3874_ = lean_unsigned_to_nat(297u);
v___x_3875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3876_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3877_ = l_mkPanicMessageWithDecl(v___x_3876_, v___x_3875_, v___x_3874_, v___x_3873_, v___x_3872_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3878_, lean_object* v_as_3879_, size_t v_sz_3880_, size_t v_i_3881_, lean_object* v_b_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v_a_3889_; uint8_t v___x_3893_; 
v___x_3893_ = lean_usize_dec_lt(v_i_3881_, v_sz_3880_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v_b_3882_);
return v___x_3894_;
}
else
{
lean_object* v_a_3895_; 
v_a_3895_ = lean_array_uget_borrowed(v_as_3879_, v_i_3881_);
if (lean_obj_tag(v_a_3895_) == 1)
{
lean_object* v_val_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_val_3896_ = lean_ctor_get(v_a_3895_, 0);
v___x_3897_ = lean_unsigned_to_nat(0u);
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_array_get_borrowed(v___x_3898_, v_val_3896_, v___x_3897_);
if (lean_obj_tag(v___x_3899_) == 1)
{
lean_object* v_val_3900_; lean_object* v___x_3901_; 
v_val_3900_ = lean_ctor_get(v___x_3899_, 0);
v___x_3901_ = lean_array_get_borrowed(v___x_3898_, v___x_3878_, v_val_3900_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_dec_ref(v_b_3882_);
v___x_3902_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3903_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3902_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3913_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3913_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3913_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
if (lean_obj_tag(v_a_3904_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; 
v_a_3908_ = lean_ctor_get(v_a_3904_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v_a_3904_, 1);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v_a_3908_);
v___x_3910_ = v___x_3906_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
else
{
lean_object* v_a_3912_; 
lean_del_object(v___x_3906_);
v_a_3912_ = lean_ctor_get(v_a_3904_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v_a_3904_, 1);
v_a_3889_ = v_a_3912_;
goto v___jp_3888_;
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
v_a_3914_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3903_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3903_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_object* v___x_3922_; 
lean_inc_ref(v___x_3901_);
v___x_3922_ = lean_array_push(v_b_3882_, v___x_3901_);
v_a_3889_ = v___x_3922_;
goto v___jp_3888_;
}
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3924_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3923_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_dec_ref_known(v___x_3924_, 1);
v_a_3889_ = v_b_3882_;
goto v___jp_3888_;
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v_b_3882_);
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3924_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3924_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_box(0);
v___x_3934_ = lean_array_push(v_b_3882_, v___x_3933_);
v_a_3889_ = v___x_3934_;
goto v___jp_3888_;
}
}
v___jp_3888_:
{
size_t v___x_3890_; size_t v___x_3891_; 
v___x_3890_ = ((size_t)1ULL);
v___x_3891_ = lean_usize_add(v_i_3881_, v___x_3890_);
v_i_3881_ = v___x_3891_;
v_b_3882_ = v_a_3889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3935_, lean_object* v_as_3936_, lean_object* v_sz_3937_, lean_object* v_i_3938_, lean_object* v_b_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
size_t v_sz_boxed_3945_; size_t v_i_boxed_3946_; lean_object* v_res_3947_; 
v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3937_);
lean_dec(v_sz_3937_);
v_i_boxed_3946_ = lean_unbox_usize(v_i_3938_);
lean_dec(v_i_3938_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3935_, v_as_3936_, v_sz_boxed_3945_, v_i_boxed_3946_, v_b_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec_ref(v_as_3936_);
lean_dec_ref(v___x_3935_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3950_, lean_object* v___x_3951_, lean_object* v___x_3952_, lean_object* v_a_3953_, lean_object* v_b_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
uint8_t v___x_3960_; 
v___x_3960_ = lean_nat_dec_lt(v_a_3953_, v_upperBound_3950_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; 
lean_dec(v_a_3953_);
v___x_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3961_, 0, v_b_3954_);
return v___x_3961_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; size_t v_sz_3964_; size_t v___x_3965_; lean_object* v___x_3966_; 
v___x_3962_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3963_ = lean_array_fget_borrowed(v___x_3951_, v_a_3953_);
v_sz_3964_ = lean_array_size(v___x_3963_);
v___x_3965_ = ((size_t)0ULL);
v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3952_, v___x_3963_, v_sz_3964_, v___x_3965_, v___x_3962_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = lean_array_push(v_b_3954_, v_a_3967_);
v___x_3969_ = lean_unsigned_to_nat(1u);
v___x_3970_ = lean_nat_add(v_a_3953_, v___x_3969_);
lean_dec(v_a_3953_);
v_a_3953_ = v___x_3970_;
v_b_3954_ = v___x_3968_;
goto _start;
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec_ref(v_b_3954_);
lean_dec(v_a_3953_);
v_a_3972_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3966_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3966_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3980_, lean_object* v___x_3981_, lean_object* v___x_3982_, lean_object* v_a_3983_, lean_object* v_b_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3980_, v___x_3981_, v___x_3982_, v_a_3983_, v_b_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec_ref(v___x_3982_);
lean_dec_ref(v___x_3981_);
lean_dec(v_upperBound_3980_);
return v_res_3990_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3992_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3993_ = lean_unsigned_to_nat(8u);
v___x_3994_ = lean_unsigned_to_nat(281u);
v___x_3995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3996_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3997_ = l_mkPanicMessageWithDecl(v___x_3996_, v___x_3995_, v___x_3994_, v___x_3993_, v___x_3992_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3998_, lean_object* v_a_3999_, lean_object* v_b_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_a_4007_; uint8_t v___x_4011_; 
v___x_4011_ = lean_nat_dec_lt(v_a_3999_, v_upperBound_3998_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
lean_dec(v_a_3999_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_b_4000_);
return v___x_4012_;
}
else
{
lean_object* v_snd_4013_; lean_object* v_snd_4014_; lean_object* v_snd_4015_; lean_object* v_fst_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4140_; 
v_snd_4013_ = lean_ctor_get(v_b_4000_, 1);
lean_inc(v_snd_4013_);
v_snd_4014_ = lean_ctor_get(v_snd_4013_, 1);
lean_inc(v_snd_4014_);
v_snd_4015_ = lean_ctor_get(v_snd_4014_, 1);
lean_inc(v_snd_4015_);
v_fst_4016_ = lean_ctor_get(v_b_4000_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_b_4000_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; 
v_unused_4141_ = lean_ctor_get(v_b_4000_, 1);
lean_dec(v_unused_4141_);
v___x_4018_ = v_b_4000_;
v_isShared_4019_ = v_isSharedCheck_4140_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_fst_4016_);
lean_dec(v_b_4000_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4140_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v_fst_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4138_; 
v_fst_4020_ = lean_ctor_get(v_snd_4013_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_snd_4013_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v_snd_4013_, 1);
lean_dec(v_unused_4139_);
v___x_4022_ = v_snd_4013_;
v_isShared_4023_ = v_isSharedCheck_4138_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_fst_4020_);
lean_dec(v_snd_4013_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4138_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v_fst_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4136_; 
v_fst_4024_ = lean_ctor_get(v_snd_4014_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_snd_4014_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; 
v_unused_4137_ = lean_ctor_get(v_snd_4014_, 1);
lean_dec(v_unused_4137_);
v___x_4026_ = v_snd_4014_;
v_isShared_4027_ = v_isSharedCheck_4136_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_fst_4024_);
lean_dec(v_snd_4014_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4136_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v_array_4028_; lean_object* v_start_4029_; lean_object* v_stop_4030_; uint8_t v___x_4031_; 
v_array_4028_ = lean_ctor_get(v_snd_4015_, 0);
v_start_4029_ = lean_ctor_get(v_snd_4015_, 1);
v_stop_4030_ = lean_ctor_get(v_snd_4015_, 2);
v___x_4031_ = lean_nat_dec_lt(v_start_4029_, v_stop_4030_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4033_; 
lean_dec(v_a_3999_);
if (v_isShared_4027_ == 0)
{
v___x_4033_ = v___x_4026_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_fst_4024_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v_snd_4015_);
v___x_4033_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4035_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4033_);
v___x_4035_ = v___x_4022_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_fst_4020_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v___x_4033_);
v___x_4035_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4037_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4035_);
v___x_4037_ = v___x_4018_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_fst_4016_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v___x_4035_);
v___x_4037_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; 
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
return v___x_4038_;
}
}
}
}
else
{
lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4132_; 
lean_inc(v_stop_4030_);
lean_inc(v_start_4029_);
lean_inc_ref(v_array_4028_);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_snd_4015_);
if (v_isSharedCheck_4132_ == 0)
{
lean_object* v_unused_4133_; lean_object* v_unused_4134_; lean_object* v_unused_4135_; 
v_unused_4133_ = lean_ctor_get(v_snd_4015_, 2);
lean_dec(v_unused_4133_);
v_unused_4134_ = lean_ctor_get(v_snd_4015_, 1);
lean_dec(v_unused_4134_);
v_unused_4135_ = lean_ctor_get(v_snd_4015_, 0);
lean_dec(v_unused_4135_);
v___x_4043_ = v_snd_4015_;
v_isShared_4044_ = v_isSharedCheck_4132_;
goto v_resetjp_4042_;
}
else
{
lean_dec(v_snd_4015_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4132_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v_array_4045_; lean_object* v_start_4046_; lean_object* v_stop_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
v_array_4045_ = lean_ctor_get(v_fst_4024_, 0);
v_start_4046_ = lean_ctor_get(v_fst_4024_, 1);
v_stop_4047_ = lean_ctor_get(v_fst_4024_, 2);
v___x_4048_ = lean_array_fget(v_array_4028_, v_start_4029_);
v___x_4049_ = lean_unsigned_to_nat(1u);
v___x_4050_ = lean_nat_add(v_start_4029_, v___x_4049_);
lean_dec(v_start_4029_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 1, v___x_4050_);
v___x_4052_ = v___x_4043_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_array_4028_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4131_, 2, v_stop_4030_);
v___x_4052_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
uint8_t v___x_4053_; 
v___x_4053_ = lean_nat_dec_lt(v_start_4046_, v_stop_4047_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4055_; 
lean_dec(v___x_4048_);
lean_dec(v_a_3999_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4052_);
v___x_4055_ = v___x_4026_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_fst_4024_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___x_4052_);
v___x_4055_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4057_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4055_);
v___x_4057_ = v___x_4022_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_fst_4020_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4059_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4057_);
v___x_4059_ = v___x_4018_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_fst_4016_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
return v___x_4060_;
}
}
}
}
else
{
lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4127_; 
lean_inc(v_stop_4047_);
lean_inc(v_start_4046_);
lean_inc_ref(v_array_4045_);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_fst_4024_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; lean_object* v_unused_4129_; lean_object* v_unused_4130_; 
v_unused_4128_ = lean_ctor_get(v_fst_4024_, 2);
lean_dec(v_unused_4128_);
v_unused_4129_ = lean_ctor_get(v_fst_4024_, 1);
lean_dec(v_unused_4129_);
v_unused_4130_ = lean_ctor_get(v_fst_4024_, 0);
lean_dec(v_unused_4130_);
v___x_4065_ = v_fst_4024_;
v_isShared_4066_ = v_isSharedCheck_4127_;
goto v_resetjp_4064_;
}
else
{
lean_dec(v_fst_4024_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4127_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4067_ = lean_nat_add(v_start_4046_, v___x_4049_);
lean_dec(v_start_4046_);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 1, v___x_4067_);
v___x_4069_ = v___x_4065_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_array_4045_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4126_, 2, v_stop_4047_);
v___x_4069_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
if (lean_obj_tag(v___x_4048_) == 1)
{
lean_object* v_val_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4114_; 
v_val_4070_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4072_ = v___x_4048_;
v_isShared_4073_ = v_isSharedCheck_4114_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_val_4070_);
lean_dec(v___x_4048_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4114_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4074_ = lean_unsigned_to_nat(0u);
v___x_4075_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4076_ = lean_box(0);
v___x_4077_ = lean_array_get(v___x_4076_, v_val_4070_, v___x_4074_);
lean_dec(v_val_4070_);
lean_inc(v_a_3999_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 0, v_a_3999_);
v___x_4079_ = v___x_4072_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_3999_);
v___x_4079_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
uint8_t v___x_4080_; 
v___x_4080_ = l_Option_instDecidableEq___redArg(v___x_4075_, v___x_4077_, v___x_4079_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
lean_dec_ref(v___x_4069_);
lean_dec_ref(v___x_4052_);
lean_del_object(v___x_4026_);
lean_del_object(v___x_4022_);
lean_dec(v_fst_4020_);
lean_del_object(v___x_4018_);
lean_dec(v_fst_4016_);
v___x_4081_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4082_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4081_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4092_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4085_ = v___x_4082_;
v_isShared_4086_ = v_isSharedCheck_4092_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4082_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4092_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
if (lean_obj_tag(v_a_4083_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; 
lean_dec(v_a_3999_);
v_a_4087_ = lean_ctor_get(v_a_4083_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v_a_4083_, 1);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v_a_4087_);
v___x_4089_ = v___x_4085_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4087_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
else
{
lean_object* v_a_4091_; 
lean_del_object(v___x_4085_);
v_a_4091_ = lean_ctor_get(v_a_4083_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v_a_4083_, 1);
v_a_4007_ = v_a_4091_;
goto v___jp_4006_;
}
}
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec(v_a_3999_);
v_a_4093_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4082_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4082_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
else
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
lean_inc(v_fst_4020_);
v___x_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4101_, 0, v_fst_4020_);
v___x_4102_ = lean_array_push(v_fst_4016_, v___x_4101_);
v___x_4103_ = lean_nat_add(v_fst_4020_, v___x_4049_);
lean_dec(v_fst_4020_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4052_);
lean_ctor_set(v___x_4026_, 0, v___x_4069_);
v___x_4105_ = v___x_4026_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v___x_4052_);
v___x_4105_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4107_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4105_);
lean_ctor_set(v___x_4022_, 0, v___x_4103_);
v___x_4107_ = v___x_4022_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4103_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
lean_object* v___x_4109_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4107_);
lean_ctor_set(v___x_4018_, 0, v___x_4102_);
v___x_4109_ = v___x_4018_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4110_, 1, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
v_a_4007_ = v___x_4109_;
goto v___jp_4006_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4118_; 
lean_dec(v___x_4048_);
v___x_4115_ = lean_box(0);
v___x_4116_ = lean_array_push(v_fst_4016_, v___x_4115_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4052_);
lean_ctor_set(v___x_4026_, 0, v___x_4069_);
v___x_4118_ = v___x_4026_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4125_, 1, v___x_4052_);
v___x_4118_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4120_; 
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4118_);
v___x_4120_ = v___x_4022_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_fst_4020_);
lean_ctor_set(v_reuseFailAlloc_4124_, 1, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4122_; 
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4120_);
lean_ctor_set(v___x_4018_, 0, v___x_4116_);
v___x_4122_ = v___x_4018_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4116_);
lean_ctor_set(v_reuseFailAlloc_4123_, 1, v___x_4120_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
v_a_4007_ = v___x_4122_;
goto v___jp_4006_;
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
v___jp_4006_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_unsigned_to_nat(1u);
v___x_4009_ = lean_nat_add(v_a_3999_, v___x_4008_);
lean_dec(v_a_3999_);
v_a_3999_ = v___x_4009_;
v_b_4000_ = v_a_4007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4142_, lean_object* v_a_4143_, lean_object* v_b_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4142_, v_a_4143_, v_b_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v_upperBound_4142_);
return v_res_4150_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4152_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4153_ = lean_unsigned_to_nat(4u);
v___x_4154_ = lean_unsigned_to_nat(275u);
v___x_4155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4156_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4157_ = l_mkPanicMessageWithDecl(v___x_4156_, v___x_4155_, v___x_4154_, v___x_4153_, v___x_4152_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4158_, lean_object* v___x_4159_, lean_object* v___x_4160_, lean_object* v_xs_4161_, lean_object* v_x_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_graph_4168_; lean_object* v_revDeps_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4222_; 
v_graph_4168_ = lean_ctor_get(v_a_4158_, 0);
v_revDeps_4169_ = lean_ctor_get(v_a_4158_, 1);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_a_4158_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4171_ = v_a_4158_;
v_isShared_4172_ = v_isSharedCheck_4222_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_revDeps_4169_);
lean_inc(v_graph_4168_);
lean_dec(v_a_4158_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4222_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v___x_4173_ = lean_array_get_borrowed(v___x_4159_, v_graph_4168_, v___x_4160_);
v___x_4174_ = lean_array_get_size(v_xs_4161_);
v___x_4175_ = lean_array_get_size(v___x_4173_);
v___x_4176_ = lean_nat_dec_eq(v___x_4174_, v___x_4175_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_del_object(v___x_4171_);
lean_dec_ref(v_revDeps_4169_);
lean_dec_ref(v_graph_4168_);
lean_dec_ref(v_xs_4161_);
lean_dec(v___x_4160_);
v___x_4177_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4178_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4177_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
return v___x_4178_;
}
else
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
v___x_4179_ = lean_mk_empty_array_with_capacity(v___x_4160_);
lean_inc_n(v___x_4160_, 2);
v___x_4180_ = l_Array_toSubarray___redArg(v_xs_4161_, v___x_4160_, v___x_4174_);
lean_inc(v___x_4173_);
v___x_4181_ = l_Array_toSubarray___redArg(v___x_4173_, v___x_4160_, v___x_4175_);
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 1, v___x_4181_);
lean_ctor_set(v___x_4171_, 0, v___x_4180_);
v___x_4183_ = v___x_4171_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4180_);
lean_ctor_set(v_reuseFailAlloc_4221_, 1, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_inc(v___x_4160_);
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4160_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
v___x_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4179_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
v___x_4186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4174_, v___x_4160_, v___x_4185_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v_snd_4188_; lean_object* v_fst_4189_; lean_object* v_fst_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4186_, 1);
v_snd_4188_ = lean_ctor_get(v_a_4187_, 1);
lean_inc(v_snd_4188_);
v_fst_4189_ = lean_ctor_get(v_a_4187_, 0);
lean_inc_n(v_fst_4189_, 2);
lean_dec(v_a_4187_);
v_fst_4190_ = lean_ctor_get(v_snd_4188_, 0);
lean_inc(v_fst_4190_);
lean_dec(v_snd_4188_);
v___x_4191_ = lean_unsigned_to_nat(1u);
v___x_4192_ = lean_array_get_size(v_graph_4168_);
v___x_4193_ = lean_mk_empty_array_with_capacity(v___x_4191_);
v___x_4194_ = lean_array_push(v___x_4193_, v_fst_4189_);
v___x_4195_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4192_, v_graph_4168_, v_fst_4189_, v___x_4191_, v___x_4194_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec(v_fst_4189_);
lean_dec_ref(v_graph_4168_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4204_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4204_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4204_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4200_; lean_object* v___x_4202_; 
v___x_4200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4200_, 0, v_fst_4190_);
lean_ctor_set(v___x_4200_, 1, v_a_4196_);
lean_ctor_set(v___x_4200_, 2, v_revDeps_4169_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4200_);
v___x_4202_ = v___x_4198_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec(v_fst_4190_);
lean_dec_ref(v_revDeps_4169_);
v_a_4205_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4195_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4195_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec_ref(v_revDeps_4169_);
lean_dec_ref(v_graph_4168_);
v_a_4213_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4186_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4186_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4223_, lean_object* v___x_4224_, lean_object* v___x_4225_, lean_object* v_xs_4226_, lean_object* v_x_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4223_, v___x_4224_, v___x_4225_, v_xs_4226_, v_x_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec_ref(v_x_4227_);
lean_dec_ref(v___x_4224_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v___x_4240_; 
lean_inc_ref(v_preDefs_4234_);
v___x_4240_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v_value_4245_; lean_object* v___x_4246_; lean_object* v___f_4247_; uint8_t v___x_4248_; lean_object* v___x_4249_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref_known(v___x_4240_, 1);
v___x_4242_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4243_ = lean_unsigned_to_nat(0u);
v___x_4244_ = lean_array_get(v___x_4242_, v_preDefs_4234_, v___x_4243_);
lean_dec_ref(v_preDefs_4234_);
v_value_4245_ = lean_ctor_get(v___x_4244_, 7);
lean_inc_ref(v_value_4245_);
lean_dec(v___x_4244_);
v___x_4246_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4247_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4247_, 0, v_a_4241_);
lean_closure_set(v___f_4247_, 1, v___x_4246_);
lean_closure_set(v___f_4247_, 2, v___x_4243_);
v___x_4248_ = 0;
v___x_4249_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4245_, v___f_4247_, v___x_4248_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
return v___x_4249_;
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec_ref(v_preDefs_4234_);
v_a_4250_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4240_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4240_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4265_, lean_object* v___x_4266_, lean_object* v___x_4267_, lean_object* v_inst_4268_, lean_object* v_R_4269_, lean_object* v_a_4270_, lean_object* v_b_4271_, lean_object* v_c_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4265_, v___x_4266_, v___x_4267_, v_a_4270_, v_b_4271_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4279_, lean_object* v___x_4280_, lean_object* v___x_4281_, lean_object* v_inst_4282_, lean_object* v_R_4283_, lean_object* v_a_4284_, lean_object* v_b_4285_, lean_object* v_c_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4279_, v___x_4280_, v___x_4281_, v_inst_4282_, v_R_4283_, v_a_4284_, v_b_4285_, v_c_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___x_4281_);
lean_dec_ref(v___x_4280_);
lean_dec(v_upperBound_4279_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4293_, lean_object* v_inst_4294_, lean_object* v_R_4295_, lean_object* v_a_4296_, lean_object* v_b_4297_, lean_object* v_c_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4293_, v_a_4296_, v_b_4297_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4305_, lean_object* v_inst_4306_, lean_object* v_R_4307_, lean_object* v_a_4308_, lean_object* v_b_4309_, lean_object* v_c_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4305_, v_inst_4306_, v_R_4307_, v_a_4308_, v_b_4309_, v_c_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v_upperBound_4305_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4317_, size_t v_i_4318_, size_t v_stop_4319_, lean_object* v_b_4320_){
_start:
{
uint8_t v___x_4321_; 
v___x_4321_ = lean_usize_dec_eq(v_i_4318_, v_stop_4319_);
if (v___x_4321_ == 0)
{
size_t v___x_4322_; size_t v___x_4323_; lean_object* v___x_4324_; 
v___x_4322_ = ((size_t)1ULL);
v___x_4323_ = lean_usize_sub(v_i_4318_, v___x_4322_);
v___x_4324_ = lean_array_uget_borrowed(v_as_4317_, v___x_4323_);
if (lean_obj_tag(v___x_4324_) == 0)
{
v_i_4318_ = v___x_4323_;
goto _start;
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = lean_unsigned_to_nat(1u);
v___x_4327_ = lean_nat_add(v_b_4320_, v___x_4326_);
lean_dec(v_b_4320_);
v_i_4318_ = v___x_4323_;
v_b_4320_ = v___x_4327_;
goto _start;
}
}
else
{
return v_b_4320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4329_, lean_object* v_i_4330_, lean_object* v_stop_4331_, lean_object* v_b_4332_){
_start:
{
size_t v_i_boxed_4333_; size_t v_stop_boxed_4334_; lean_object* v_res_4335_; 
v_i_boxed_4333_ = lean_unbox_usize(v_i_4330_);
lean_dec(v_i_4330_);
v_stop_boxed_4334_ = lean_unbox_usize(v_stop_4331_);
lean_dec(v_stop_4331_);
v_res_4335_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4329_, v_i_boxed_4333_, v_stop_boxed_4334_, v_b_4332_);
lean_dec_ref(v_as_4329_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4336_){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = lean_array_get_size(v_perm_4336_);
v___x_4339_ = lean_nat_dec_lt(v___x_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
return v___x_4337_;
}
else
{
size_t v___x_4340_; size_t v___x_4341_; lean_object* v___x_4342_; 
v___x_4340_ = lean_usize_of_nat(v___x_4338_);
v___x_4341_ = ((size_t)0ULL);
v___x_4342_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4336_, v___x_4340_, v___x_4341_, v___x_4337_);
return v___x_4342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4343_);
lean_dec_ref(v_perm_4343_);
return v_res_4344_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4345_, lean_object* v_i_4346_){
_start:
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = lean_array_get_size(v_perm_4345_);
v___x_4348_ = lean_nat_dec_lt(v_i_4346_, v___x_4347_);
if (v___x_4348_ == 0)
{
return v___x_4348_;
}
else
{
lean_object* v___x_4349_; 
v___x_4349_ = lean_array_fget_borrowed(v_perm_4345_, v_i_4346_);
if (lean_obj_tag(v___x_4349_) == 0)
{
uint8_t v___x_4350_; 
v___x_4350_ = 0;
return v___x_4350_;
}
else
{
return v___x_4348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4351_, lean_object* v_i_4352_){
_start:
{
uint8_t v_res_4353_; lean_object* v_r_4354_; 
v_res_4353_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4351_, v_i_4352_);
lean_dec(v_i_4352_);
lean_dec_ref(v_perm_4351_);
v_r_4354_ = lean_box(v_res_4353_);
return v_r_4354_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___f_4361_; lean_object* v___x_1003__overap_4362_; lean_object* v___x_4363_; 
v___f_4361_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_1003__overap_4362_ = lean_panic_fn_borrowed(v___f_4361_, v_msg_4355_);
lean_inc(v___y_4359_);
lean_inc_ref(v___y_4358_);
lean_inc(v___y_4357_);
lean_inc_ref(v___y_4356_);
v___x_4363_ = lean_apply_5(v___x_1003__overap_4362_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, lean_box(0));
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4371_, lean_object* v_msg_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4379_, lean_object* v_msg_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4379_, v_msg_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4387_, lean_object* v_maxFVars_x3f_4388_, lean_object* v_k_4389_, uint8_t v_cleanupAnnotations_4390_, uint8_t v_whnfType_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v___f_4397_; lean_object* v___x_4398_; 
v___f_4397_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4397_, 0, v_k_4389_);
v___x_4398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4387_, v_maxFVars_x3f_4388_, v___f_4397_, v_cleanupAnnotations_4390_, v_whnfType_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4398_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4398_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
v_a_4407_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4398_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4398_);
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
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4415_, lean_object* v_maxFVars_x3f_4416_, lean_object* v_k_4417_, lean_object* v_cleanupAnnotations_4418_, lean_object* v_whnfType_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4425_; uint8_t v_whnfType_boxed_4426_; lean_object* v_res_4427_; 
v_cleanupAnnotations_boxed_4425_ = lean_unbox(v_cleanupAnnotations_4418_);
v_whnfType_boxed_4426_ = lean_unbox(v_whnfType_4419_);
v_res_4427_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4415_, v_maxFVars_x3f_4416_, v_k_4417_, v_cleanupAnnotations_boxed_4425_, v_whnfType_boxed_4426_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4428_, lean_object* v_type_4429_, lean_object* v_maxFVars_x3f_4430_, lean_object* v_k_4431_, uint8_t v_cleanupAnnotations_4432_, uint8_t v_whnfType_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4429_, v_maxFVars_x3f_4430_, v_k_4431_, v_cleanupAnnotations_4432_, v_whnfType_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4440_, lean_object* v_type_4441_, lean_object* v_maxFVars_x3f_4442_, lean_object* v_k_4443_, lean_object* v_cleanupAnnotations_4444_, lean_object* v_whnfType_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4451_; uint8_t v_whnfType_boxed_4452_; lean_object* v_res_4453_; 
v_cleanupAnnotations_boxed_4451_ = lean_unbox(v_cleanupAnnotations_4444_);
v_whnfType_boxed_4452_ = lean_unbox(v_whnfType_4445_);
v_res_4453_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4440_, v_type_4441_, v_maxFVars_x3f_4442_, v_k_4443_, v_cleanupAnnotations_boxed_4451_, v_whnfType_boxed_4452_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4453_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4456_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4457_ = lean_unsigned_to_nat(6u);
v___x_4458_ = lean_unsigned_to_nat(329u);
v___x_4459_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4460_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4461_ = l_mkPanicMessageWithDecl(v___x_4460_, v___x_4459_, v___x_4458_, v___x_4457_, v___x_4456_);
return v___x_4461_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4466_ = lean_unsigned_to_nat(8u);
v___x_4467_ = lean_unsigned_to_nat(322u);
v___x_4468_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4469_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4470_ = l_mkPanicMessageWithDecl(v___x_4469_, v___x_4468_, v___x_4467_, v___x_4466_, v___x_4465_);
return v___x_4470_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4472_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4473_ = lean_unsigned_to_nat(8u);
v___x_4474_ = lean_unsigned_to_nat(324u);
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4476_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4477_ = l_mkPanicMessageWithDecl(v___x_4476_, v___x_4475_, v___x_4474_, v___x_4473_, v___x_4472_);
return v___x_4477_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4479_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4480_ = lean_unsigned_to_nat(8u);
v___x_4481_ = lean_unsigned_to_nat(325u);
v___x_4482_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4483_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4484_ = l_mkPanicMessageWithDecl(v___x_4483_, v___x_4482_, v___x_4481_, v___x_4480_, v___x_4479_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4485_, lean_object* v_xs_4486_, lean_object* v_val_4487_, lean_object* v_i_4488_, lean_object* v_perm_4489_, lean_object* v_k_4490_, lean_object* v_xs_x27_4491_, lean_object* v_type_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; uint8_t v___x_4499_; 
v___x_4498_ = lean_array_get_size(v_xs_x27_4491_);
v___x_4499_ = lean_nat_dec_eq(v___x_4498_, v___x_4485_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_dec_ref(v_type_4492_);
lean_dec_ref(v_k_4490_);
lean_dec_ref(v_perm_4489_);
lean_dec_ref(v_xs_4486_);
v___x_4500_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4501_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4500_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4501_;
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v_x_4504_; lean_object* v___x_4505_; 
v___x_4502_ = l_Lean_instInhabitedExpr;
v___x_4503_ = lean_unsigned_to_nat(0u);
v_x_4504_ = lean_array_get_borrowed(v___x_4502_, v_xs_x27_4491_, v___x_4503_);
lean_inc(v___y_4496_);
lean_inc_ref(v___y_4495_);
lean_inc(v___y_4494_);
lean_inc_ref(v___y_4493_);
lean_inc(v_x_4504_);
v___x_4505_ = lean_infer_type(v_x_4504_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; uint8_t v___x_4507_; uint8_t v___x_4508_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref_known(v___x_4505_, 1);
v___x_4507_ = l_Lean_Expr_hasLooseBVars(v_a_4506_);
lean_dec(v_a_4506_);
v___x_4508_ = lean_bool_not(v___x_4507_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec_ref(v_type_4492_);
lean_dec_ref(v_k_4490_);
lean_dec_ref(v_perm_4489_);
lean_dec_ref(v_xs_4486_);
v___x_4509_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4510_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4509_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4510_;
}
else
{
lean_object* v___x_4511_; uint8_t v___x_4512_; 
v___x_4511_ = lean_array_get_size(v_xs_4486_);
v___x_4512_ = lean_nat_dec_lt(v_val_4487_, v___x_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
lean_dec_ref(v_type_4492_);
lean_dec_ref(v_k_4490_);
lean_dec_ref(v_perm_4489_);
lean_dec_ref(v_xs_4486_);
v___x_4513_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4514_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4513_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4514_;
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4515_ = lean_nat_add(v_i_4488_, v___x_4485_);
lean_inc(v_x_4504_);
v___x_4516_ = lean_array_set(v_xs_4486_, v_val_4487_, v_x_4504_);
v___x_4517_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4489_, v_k_4490_, v___x_4515_, v_type_4492_, v___x_4516_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4517_;
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec_ref(v_type_4492_);
lean_dec_ref(v_k_4490_);
lean_dec_ref(v_perm_4489_);
lean_dec_ref(v_xs_4486_);
v_a_4518_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4505_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4505_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4526_, lean_object* v_xs_4527_, lean_object* v_val_4528_, lean_object* v_i_4529_, lean_object* v_perm_4530_, lean_object* v_k_4531_, lean_object* v_xs_x27_4532_, lean_object* v_type_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4526_, v_xs_4527_, v_val_4528_, v_i_4529_, v_perm_4530_, v_k_4531_, v_xs_x27_4532_, v_type_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec_ref(v_xs_x27_4532_);
lean_dec(v_i_4529_);
lean_dec(v_val_4528_);
lean_dec(v___x_4526_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4540_, lean_object* v_k_4541_, lean_object* v_i_4542_, lean_object* v_type_4543_, lean_object* v_xs_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4550_ = lean_array_get_size(v_perm_4540_);
v___x_4551_ = lean_nat_dec_lt(v_i_4542_, v___x_4550_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
lean_dec_ref(v_type_4543_);
lean_dec(v_i_4542_);
lean_dec_ref(v_perm_4540_);
lean_inc(v_a_4548_);
lean_inc_ref(v_a_4547_);
lean_inc(v_a_4546_);
lean_inc_ref(v_a_4545_);
v___x_4552_ = lean_apply_6(v_k_4541_, v_xs_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, lean_box(0));
return v___x_4552_;
}
else
{
lean_object* v___x_4553_; 
v___x_4553_ = lean_array_fget_borrowed(v_perm_4540_, v_i_4542_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v___x_4554_; 
lean_inc(v_a_4548_);
lean_inc_ref(v_a_4547_);
lean_inc(v_a_4546_);
lean_inc_ref(v_a_4545_);
v___x_4554_ = lean_whnf(v_type_4543_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; uint8_t v___x_4556_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v___x_4554_, 1);
v___x_4556_ = l_Lean_Expr_isForall(v_a_4555_);
if (v___x_4556_ == 0)
{
lean_object* v___x_4557_; lean_object* v___x_4558_; 
lean_dec(v_a_4555_);
lean_dec_ref(v_xs_4544_);
lean_dec(v_i_4542_);
lean_dec_ref(v_k_4541_);
lean_dec_ref(v_perm_4540_);
v___x_4557_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4558_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4557_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
return v___x_4558_;
}
else
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4559_ = lean_unsigned_to_nat(1u);
v___x_4560_ = lean_nat_add(v_i_4542_, v___x_4559_);
lean_dec(v_i_4542_);
v___x_4561_ = l_Lean_Expr_bindingBody_x21(v_a_4555_);
lean_dec(v_a_4555_);
v_i_4542_ = v___x_4560_;
v_type_4543_ = v___x_4561_;
goto _start;
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec_ref(v_xs_4544_);
lean_dec(v_i_4542_);
lean_dec_ref(v_k_4541_);
lean_dec_ref(v_perm_4540_);
v_a_4563_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4554_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4554_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
else
{
lean_object* v_val_4571_; lean_object* v___x_4572_; lean_object* v___f_4573_; lean_object* v___x_4574_; uint8_t v___x_4575_; lean_object* v___x_4576_; 
v_val_4571_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_val_4571_);
v___x_4572_ = lean_unsigned_to_nat(1u);
v___f_4573_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4573_, 0, v___x_4572_);
lean_closure_set(v___f_4573_, 1, v_xs_4544_);
lean_closure_set(v___f_4573_, 2, v_val_4571_);
lean_closure_set(v___f_4573_, 3, v_i_4542_);
lean_closure_set(v___f_4573_, 4, v_perm_4540_);
lean_closure_set(v___f_4573_, 5, v_k_4541_);
v___x_4574_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4575_ = 0;
v___x_4576_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4543_, v___x_4574_, v___f_4573_, v___x_4551_, v___x_4575_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
return v___x_4576_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4577_, lean_object* v_k_4578_, lean_object* v_i_4579_, lean_object* v_type_4580_, lean_object* v_xs_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4577_, v_k_4578_, v_i_4579_, v_type_4580_, v_xs_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec_ref(v_a_4582_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4588_, lean_object* v_perm_4589_, lean_object* v_k_4590_, lean_object* v_i_4591_, lean_object* v_type_4592_, lean_object* v_xs_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4589_, v_k_4590_, v_i_4591_, v_type_4592_, v_xs_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4600_, lean_object* v_perm_4601_, lean_object* v_k_4602_, lean_object* v_i_4603_, lean_object* v_type_4604_, lean_object* v_xs_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4600_, v_perm_4601_, v_k_4602_, v_i_4603_, v_type_4604_, v_xs_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4611_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4612_ = lean_unsigned_to_nat(0u);
v___x_4613_ = l_Lean_Level_ofNat(v___x_4612_);
return v___x_4613_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4615_ = l_Lean_mkSort(v___x_4614_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4616_, lean_object* v_type_4617_, lean_object* v_k_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4624_ = lean_unsigned_to_nat(0u);
v___x_4625_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4616_);
v___x_4626_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4627_ = lean_mk_array(v___x_4625_, v___x_4626_);
v___x_4628_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4616_, v_k_4618_, v___x_4624_, v_type_4617_, v___x_4627_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4629_, lean_object* v_type_4630_, lean_object* v_k_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4629_, v_type_4630_, v_k_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4638_, lean_object* v_perm_4639_, lean_object* v_type_4640_, lean_object* v_k_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4639_, v_type_4640_, v_k_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4648_, lean_object* v_perm_4649_, lean_object* v_type_4650_, lean_object* v_k_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4648_, v_perm_4649_, v_type_4650_, v_k_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
lean_dec(v_a_4653_);
lean_dec_ref(v_a_4652_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4658_, lean_object* v_runInBase_4659_, lean_object* v_b_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = lean_apply_1(v_k_4658_, v_b_4660_);
lean_inc(v___y_4664_);
lean_inc_ref(v___y_4663_);
lean_inc(v___y_4662_);
lean_inc_ref(v___y_4661_);
v___x_4667_ = lean_apply_7(v_runInBase_4659_, lean_box(0), v___x_4666_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, lean_box(0));
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4668_, lean_object* v_runInBase_4669_, lean_object* v_b_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4668_, v_runInBase_4669_, v_b_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4677_, lean_object* v_perm_4678_, lean_object* v_type_4679_, lean_object* v_runInBase_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v___f_4686_; lean_object* v___x_4687_; 
v___f_4686_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4686_, 0, v_k_4677_);
lean_closure_set(v___f_4686_, 1, v_runInBase_4680_);
v___x_4687_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4678_, v_type_4679_, v___f_4686_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4688_, lean_object* v_perm_4689_, lean_object* v_type_4690_, lean_object* v_runInBase_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_){
_start:
{
lean_object* v_res_4697_; 
v_res_4697_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4688_, v_perm_4689_, v_type_4690_, v_runInBase_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
return v_res_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4698_, lean_object* v_inst_4699_, lean_object* v_perm_4700_, lean_object* v_type_4701_, lean_object* v_k_4702_){
_start:
{
lean_object* v_toBind_4703_; lean_object* v_liftWith_4704_; lean_object* v_restoreM_4705_; lean_object* v___f_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v_toBind_4703_ = lean_ctor_get(v_inst_4699_, 1);
lean_inc(v_toBind_4703_);
lean_dec_ref(v_inst_4699_);
v_liftWith_4704_ = lean_ctor_get(v_inst_4698_, 0);
lean_inc(v_liftWith_4704_);
v_restoreM_4705_ = lean_ctor_get(v_inst_4698_, 1);
lean_inc(v_restoreM_4705_);
lean_dec_ref(v_inst_4698_);
v___f_4706_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4706_, 0, v_k_4702_);
lean_closure_set(v___f_4706_, 1, v_perm_4700_);
lean_closure_set(v___f_4706_, 2, v_type_4701_);
v___x_4707_ = lean_apply_2(v_liftWith_4704_, lean_box(0), v___f_4706_);
v___x_4708_ = lean_apply_1(v_restoreM_4705_, lean_box(0));
v___x_4709_ = lean_apply_4(v_toBind_4703_, lean_box(0), lean_box(0), v___x_4707_, v___x_4708_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4710_, lean_object* v_00_u03b1_4711_, lean_object* v_inst_4712_, lean_object* v_inst_4713_, lean_object* v_perm_4714_, lean_object* v_type_4715_, lean_object* v_k_4716_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4712_, v_inst_4713_, v_perm_4714_, v_type_4715_, v_k_4716_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v___f_4724_; lean_object* v___x_603__overap_4725_; lean_object* v___x_4726_; 
v___f_4724_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_603__overap_4725_ = lean_panic_fn_borrowed(v___f_4724_, v_msg_4718_);
lean_inc(v___y_4722_);
lean_inc_ref(v___y_4721_);
lean_inc(v___y_4720_);
lean_inc_ref(v___y_4719_);
v___x_4726_ = lean_apply_5(v___x_603__overap_4725_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, lean_box(0));
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
return v_res_4733_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4736_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4737_ = lean_unsigned_to_nat(10u);
v___x_4738_ = lean_unsigned_to_nat(353u);
v___x_4739_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4741_ = l_mkPanicMessageWithDecl(v___x_4740_, v___x_4739_, v___x_4738_, v___x_4737_, v___x_4736_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4742_, lean_object* v_xs_4743_, lean_object* v_tail_4744_, lean_object* v_ys_4745_, lean_object* v_type_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4742_, v_xs_4743_, v_tail_4744_, v_ys_4745_, v_type_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
lean_dec_ref(v_ys_4745_);
lean_dec(v___x_4742_);
return v_res_4752_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4753_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4754_ = lean_unsigned_to_nat(8u);
v___x_4755_ = lean_unsigned_to_nat(349u);
v___x_4756_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4757_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4758_ = l_mkPanicMessageWithDecl(v___x_4757_, v___x_4756_, v___x_4755_, v___x_4754_, v___x_4753_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4759_, lean_object* v_x_4760_, lean_object* v_x_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
if (lean_obj_tag(v_x_4760_) == 0)
{
lean_object* v___x_4767_; 
lean_dec_ref(v_xs_4759_);
v___x_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4767_, 0, v_x_4761_);
return v___x_4767_;
}
else
{
lean_object* v_head_4768_; 
v_head_4768_ = lean_ctor_get(v_x_4760_, 0);
if (lean_obj_tag(v_head_4768_) == 0)
{
lean_object* v_tail_4769_; lean_object* v___x_4770_; lean_object* v___f_4771_; lean_object* v___x_4772_; uint8_t v___x_4773_; lean_object* v___x_4774_; 
v_tail_4769_ = lean_ctor_get(v_x_4760_, 1);
lean_inc(v_tail_4769_);
lean_dec_ref_known(v_x_4760_, 2);
v___x_4770_ = lean_unsigned_to_nat(1u);
v___f_4771_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4771_, 0, v___x_4770_);
lean_closure_set(v___f_4771_, 1, v_xs_4759_);
lean_closure_set(v___f_4771_, 2, v_tail_4769_);
v___x_4772_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4773_ = 0;
v___x_4774_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4761_, v___x_4772_, v___f_4771_, v___x_4773_, v___x_4773_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
return v___x_4774_;
}
else
{
lean_object* v_tail_4775_; lean_object* v_val_4776_; lean_object* v___x_4777_; uint8_t v___x_4778_; 
lean_inc_ref(v_head_4768_);
v_tail_4775_ = lean_ctor_get(v_x_4760_, 1);
lean_inc(v_tail_4775_);
lean_dec_ref_known(v_x_4760_, 2);
v_val_4776_ = lean_ctor_get(v_head_4768_, 0);
lean_inc(v_val_4776_);
lean_dec_ref_known(v_head_4768_, 1);
v___x_4777_ = lean_array_get_size(v_xs_4759_);
v___x_4778_ = lean_nat_dec_lt(v_val_4776_, v___x_4777_);
if (v___x_4778_ == 0)
{
lean_object* v___x_4779_; lean_object* v___x_4780_; 
lean_dec(v_val_4776_);
lean_dec(v_tail_4775_);
lean_dec_ref(v_x_4761_);
lean_dec_ref(v_xs_4759_);
v___x_4779_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4780_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4779_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
return v___x_4780_;
}
else
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4781_ = l_Lean_instInhabitedExpr;
v___x_4782_ = lean_array_get_borrowed(v___x_4781_, v_xs_4759_, v_val_4776_);
lean_dec(v_val_4776_);
v___x_4783_ = lean_unsigned_to_nat(1u);
v___x_4784_ = lean_mk_empty_array_with_capacity(v___x_4783_);
lean_inc(v___x_4782_);
v___x_4785_ = lean_array_push(v___x_4784_, v___x_4782_);
v___x_4786_ = l_Lean_Meta_instantiateForall(v_x_4761_, v___x_4785_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
lean_dec_ref(v___x_4785_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_a_4787_);
lean_dec_ref_known(v___x_4786_, 1);
v_x_4760_ = v_tail_4775_;
v_x_4761_ = v_a_4787_;
goto _start;
}
else
{
lean_dec(v_tail_4775_);
lean_dec_ref(v_xs_4759_);
return v___x_4786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4789_, lean_object* v_xs_4790_, lean_object* v_tail_4791_, lean_object* v_ys_4792_, lean_object* v_type_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v___x_4799_; uint8_t v___x_4800_; 
v___x_4799_ = lean_array_get_size(v_ys_4792_);
v___x_4800_ = lean_nat_dec_eq(v___x_4799_, v___x_4789_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
lean_dec_ref(v_type_4793_);
lean_dec(v_tail_4791_);
lean_dec_ref(v_xs_4790_);
v___x_4801_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4802_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4801_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
return v___x_4802_;
}
else
{
lean_object* v___x_4803_; 
v___x_4803_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4790_, v_tail_4791_, v_type_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; uint8_t v___x_4805_; uint8_t v___x_4806_; lean_object* v___x_4807_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4804_);
lean_dec_ref_known(v___x_4803_, 1);
v___x_4805_ = 0;
v___x_4806_ = 1;
v___x_4807_ = l_Lean_Meta_mkForallFVars(v_ys_4792_, v_a_4804_, v___x_4805_, v___x_4800_, v___x_4800_, v___x_4806_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
return v___x_4807_;
}
else
{
return v___x_4803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4808_, lean_object* v_x_4809_, lean_object* v_x_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4808_, v_x_4809_, v_x_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
lean_dec(v_a_4814_);
lean_dec_ref(v_a_4813_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
return v_res_4816_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4819_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4820_ = lean_unsigned_to_nat(2u);
v___x_4821_ = lean_unsigned_to_nat(343u);
v___x_4822_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4823_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4824_ = l_mkPanicMessageWithDecl(v___x_4823_, v___x_4822_, v___x_4821_, v___x_4820_, v___x_4819_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4825_, lean_object* v_type_u2080_4826_, lean_object* v_xs_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v___x_4833_ = lean_array_get_size(v_xs_4827_);
v___x_4834_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4825_);
v___x_4835_ = lean_nat_dec_eq(v___x_4833_, v___x_4834_);
lean_dec(v___x_4834_);
if (v___x_4835_ == 0)
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
lean_dec_ref(v_xs_4827_);
lean_dec_ref(v_type_u2080_4826_);
lean_dec_ref(v_perm_4825_);
v___x_4836_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4837_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4836_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
return v___x_4837_;
}
else
{
lean_object* v_mask_4838_; lean_object* v___x_4839_; 
v_mask_4838_ = lean_array_to_list(v_perm_4825_);
v___x_4839_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4827_, v_mask_4838_, v_type_u2080_4826_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_);
return v___x_4839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4840_, lean_object* v_type_u2080_4841_, lean_object* v_xs_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v_res_4848_; 
v_res_4848_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4840_, v_type_u2080_4841_, v_xs_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
lean_dec(v_a_4846_);
lean_dec_ref(v_a_4845_);
lean_dec(v_a_4844_);
lean_dec_ref(v_a_4843_);
return v_res_4848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4849_, lean_object* v_maxFVars_4850_, lean_object* v_k_4851_, uint8_t v_cleanupAnnotations_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v___f_4858_; uint8_t v___x_4859_; uint8_t v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___f_4858_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4858_, 0, v_k_4851_);
v___x_4859_ = 1;
v___x_4860_ = 0;
v___x_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4861_, 0, v_maxFVars_4850_);
v___x_4862_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4849_, v___x_4859_, v___x_4860_, v___x_4859_, v___x_4860_, v___x_4861_, v___f_4858_, v_cleanupAnnotations_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
lean_dec_ref_known(v___x_4861_, 1);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4862_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4862_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
else
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
v_a_4871_ = lean_ctor_get(v___x_4862_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4862_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4862_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4862_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4879_, lean_object* v_maxFVars_4880_, lean_object* v_k_4881_, lean_object* v_cleanupAnnotations_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4888_; lean_object* v_res_4889_; 
v_cleanupAnnotations_boxed_4888_ = lean_unbox(v_cleanupAnnotations_4882_);
v_res_4889_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4879_, v_maxFVars_4880_, v_k_4881_, v_cleanupAnnotations_boxed_4888_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4890_, lean_object* v_e_4891_, lean_object* v_maxFVars_4892_, lean_object* v_k_4893_, uint8_t v_cleanupAnnotations_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v___x_4900_; 
v___x_4900_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4891_, v_maxFVars_4892_, v_k_4893_, v_cleanupAnnotations_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4901_, lean_object* v_e_4902_, lean_object* v_maxFVars_4903_, lean_object* v_k_4904_, lean_object* v_cleanupAnnotations_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4911_; lean_object* v_res_4912_; 
v_cleanupAnnotations_boxed_4911_ = lean_unbox(v_cleanupAnnotations_4905_);
v_res_4912_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4901_, v_e_4902_, v_maxFVars_4903_, v_k_4904_, v_cleanupAnnotations_boxed_4911_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
return v_res_4912_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4913_){
_start:
{
if (lean_obj_tag(v_x_4913_) == 0)
{
uint8_t v___x_4914_; 
v___x_4914_ = 1;
return v___x_4914_;
}
else
{
lean_object* v_head_4915_; 
v_head_4915_ = lean_ctor_get(v_x_4913_, 0);
if (lean_obj_tag(v_head_4915_) == 0)
{
lean_object* v_tail_4916_; 
v_tail_4916_ = lean_ctor_get(v_x_4913_, 1);
v_x_4913_ = v_tail_4916_;
goto _start;
}
else
{
uint8_t v___x_4918_; 
v___x_4918_ = 0;
return v___x_4918_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4919_){
_start:
{
uint8_t v_res_4920_; lean_object* v_r_4921_; 
v_res_4920_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4919_);
lean_dec(v_x_4919_);
v_r_4921_ = lean_box(v_res_4920_);
return v_r_4921_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4924_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4925_ = lean_unsigned_to_nat(12u);
v___x_4926_ = lean_unsigned_to_nat(376u);
v___x_4927_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4928_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4929_ = l_mkPanicMessageWithDecl(v___x_4928_, v___x_4927_, v___x_4926_, v___x_4925_, v___x_4924_);
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4930_, lean_object* v_xs_4931_, lean_object* v_tail_4932_, lean_object* v___x_4933_, lean_object* v___x_4934_, lean_object* v_ys_4935_, lean_object* v_value_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_){
_start:
{
uint8_t v___x_1310__boxed_4942_; uint8_t v___x_1311__boxed_4943_; lean_object* v_res_4944_; 
v___x_1310__boxed_4942_ = lean_unbox(v___x_4933_);
v___x_1311__boxed_4943_ = lean_unbox(v___x_4934_);
v_res_4944_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4930_, v_xs_4931_, v_tail_4932_, v___x_1310__boxed_4942_, v___x_1311__boxed_4943_, v_ys_4935_, v_value_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
lean_dec(v___y_4940_);
lean_dec_ref(v___y_4939_);
lean_dec(v___y_4938_);
lean_dec_ref(v___y_4937_);
lean_dec_ref(v_ys_4935_);
lean_dec(v___x_4930_);
return v_res_4944_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4945_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4946_ = lean_unsigned_to_nat(8u);
v___x_4947_ = lean_unsigned_to_nat(368u);
v___x_4948_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4949_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4950_ = l_mkPanicMessageWithDecl(v___x_4949_, v___x_4948_, v___x_4947_, v___x_4946_, v___x_4945_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4951_, lean_object* v_x_4952_, lean_object* v_x_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_){
_start:
{
if (lean_obj_tag(v_x_4952_) == 0)
{
lean_object* v___x_4959_; 
lean_dec_ref(v_xs_4951_);
v___x_4959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4959_, 0, v_x_4953_);
return v___x_4959_;
}
else
{
lean_object* v_head_4960_; 
v_head_4960_ = lean_ctor_get(v_x_4952_, 0);
if (lean_obj_tag(v_head_4960_) == 0)
{
lean_object* v_tail_4961_; uint8_t v___x_4962_; 
v_tail_4961_ = lean_ctor_get(v_x_4952_, 1);
lean_inc(v_tail_4961_);
lean_dec_ref_known(v_x_4952_, 2);
v___x_4962_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4961_);
if (v___x_4962_ == 0)
{
uint8_t v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___f_4967_; lean_object* v___x_4968_; 
v___x_4963_ = 1;
v___x_4964_ = lean_unsigned_to_nat(1u);
v___x_4965_ = lean_box(v___x_4962_);
v___x_4966_ = lean_box(v___x_4963_);
v___f_4967_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4967_, 0, v___x_4964_);
lean_closure_set(v___f_4967_, 1, v_xs_4951_);
lean_closure_set(v___f_4967_, 2, v_tail_4961_);
lean_closure_set(v___f_4967_, 3, v___x_4965_);
lean_closure_set(v___f_4967_, 4, v___x_4966_);
v___x_4968_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4953_, v___x_4964_, v___f_4967_, v___x_4962_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_);
return v___x_4968_;
}
else
{
lean_object* v___x_4969_; 
lean_dec(v_tail_4961_);
lean_dec_ref(v_xs_4951_);
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v_x_4953_);
return v___x_4969_;
}
}
else
{
lean_object* v_tail_4970_; lean_object* v_val_4971_; lean_object* v___x_4972_; uint8_t v___x_4973_; 
lean_inc_ref(v_head_4960_);
v_tail_4970_ = lean_ctor_get(v_x_4952_, 1);
lean_inc(v_tail_4970_);
lean_dec_ref_known(v_x_4952_, 2);
v_val_4971_ = lean_ctor_get(v_head_4960_, 0);
lean_inc(v_val_4971_);
lean_dec_ref_known(v_head_4960_, 1);
v___x_4972_ = lean_array_get_size(v_xs_4951_);
v___x_4973_ = lean_nat_dec_lt(v_val_4971_, v___x_4972_);
if (v___x_4973_ == 0)
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
lean_dec(v_val_4971_);
lean_dec(v_tail_4970_);
lean_dec_ref(v_x_4953_);
lean_dec_ref(v_xs_4951_);
v___x_4974_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4975_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4974_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_);
return v___x_4975_;
}
else
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4976_ = l_Lean_instInhabitedExpr;
v___x_4977_ = lean_array_get_borrowed(v___x_4976_, v_xs_4951_, v_val_4971_);
lean_dec(v_val_4971_);
v___x_4978_ = lean_unsigned_to_nat(1u);
v___x_4979_ = lean_mk_empty_array_with_capacity(v___x_4978_);
lean_inc(v___x_4977_);
v___x_4980_ = lean_array_push(v___x_4979_, v___x_4977_);
v___x_4981_ = l_Lean_Meta_instantiateLambda(v_x_4953_, v___x_4980_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_);
lean_dec_ref(v___x_4980_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_a_4982_);
lean_dec_ref_known(v___x_4981_, 1);
v_x_4952_ = v_tail_4970_;
v_x_4953_ = v_a_4982_;
goto _start;
}
else
{
lean_dec(v_tail_4970_);
lean_dec_ref(v_xs_4951_);
return v___x_4981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4984_, lean_object* v_xs_4985_, lean_object* v_tail_4986_, uint8_t v___x_4987_, uint8_t v___x_4988_, lean_object* v_ys_4989_, lean_object* v_value_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_){
_start:
{
lean_object* v___x_4996_; uint8_t v___x_4997_; 
v___x_4996_ = lean_array_get_size(v_ys_4989_);
v___x_4997_ = lean_nat_dec_eq(v___x_4996_, v___x_4984_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec_ref(v_value_4990_);
lean_dec(v_tail_4986_);
lean_dec_ref(v_xs_4985_);
v___x_4998_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4999_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4998_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
return v___x_4999_;
}
else
{
lean_object* v___x_5000_; 
v___x_5000_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4985_, v_tail_4986_, v_value_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_a_5001_; uint8_t v___x_5002_; lean_object* v___x_5003_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
lean_inc(v_a_5001_);
lean_dec_ref_known(v___x_5000_, 1);
v___x_5002_ = 1;
v___x_5003_ = l_Lean_Meta_mkLambdaFVars(v_ys_4989_, v_a_5001_, v___x_4987_, v___x_4988_, v___x_4987_, v___x_4988_, v___x_5002_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
return v___x_5003_;
}
else
{
return v___x_5000_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_5004_, lean_object* v_x_5005_, lean_object* v_x_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5004_, v_x_5005_, v_x_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
return v_res_5012_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5014_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5015_ = lean_unsigned_to_nat(2u);
v___x_5016_ = lean_unsigned_to_nat(362u);
v___x_5017_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5018_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5019_ = l_mkPanicMessageWithDecl(v___x_5018_, v___x_5017_, v___x_5016_, v___x_5015_, v___x_5014_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5020_, lean_object* v_value_u2080_5021_, lean_object* v_xs_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; uint8_t v___x_5030_; 
v___x_5028_ = lean_array_get_size(v_xs_5022_);
v___x_5029_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5020_);
v___x_5030_ = lean_nat_dec_eq(v___x_5028_, v___x_5029_);
lean_dec(v___x_5029_);
if (v___x_5030_ == 0)
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
lean_dec_ref(v_xs_5022_);
lean_dec_ref(v_value_u2080_5021_);
lean_dec_ref(v_perm_5020_);
v___x_5031_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5032_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5031_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
return v___x_5032_;
}
else
{
lean_object* v_mask_5033_; lean_object* v___x_5034_; 
v_mask_5033_ = lean_array_to_list(v_perm_5020_);
v___x_5034_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5022_, v_mask_5033_, v_value_u2080_5021_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_);
return v___x_5034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5035_, lean_object* v_value_u2080_5036_, lean_object* v_xs_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5035_, v_value_u2080_5036_, v_xs_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
lean_dec(v_a_5041_);
lean_dec_ref(v_a_5040_);
lean_dec(v_a_5039_);
lean_dec_ref(v_a_5038_);
return v_res_5043_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5051_; 
v___x_5051_ = l_Array_instInhabited(lean_box(0));
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5052_){
_start:
{
lean_object* v___f_5053_; lean_object* v___f_5054_; lean_object* v___f_5055_; lean_object* v___f_5056_; lean_object* v___f_5057_; lean_object* v___f_5058_; lean_object* v___f_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___f_5053_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5054_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5055_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5056_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5057_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5058_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5059_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5060_, 0, v___f_5053_);
lean_ctor_set(v___x_5060_, 1, v___f_5054_);
v___x_5061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5061_, 0, v___x_5060_);
lean_ctor_set(v___x_5061_, 1, v___f_5055_);
lean_ctor_set(v___x_5061_, 2, v___f_5056_);
lean_ctor_set(v___x_5061_, 3, v___f_5057_);
lean_ctor_set(v___x_5061_, 4, v___f_5058_);
v___x_5062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5062_, 0, v___x_5061_);
lean_ctor_set(v___x_5062_, 1, v___f_5059_);
v___x_5063_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5064_ = l_instInhabitedOfMonad___redArg(v___x_5062_, v___x_5063_);
v___x_5065_ = lean_panic_fn_borrowed(v___x_5064_, v_msg_5052_);
lean_dec(v___x_5064_);
return v___x_5065_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5066_, lean_object* v_msg_5067_){
_start:
{
lean_object* v___x_5068_; 
v___x_5068_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5067_);
return v___x_5068_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5071_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5072_ = lean_unsigned_to_nat(8u);
v___x_5073_ = lean_unsigned_to_nat(394u);
v___x_5074_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5075_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5076_ = l_mkPanicMessageWithDecl(v___x_5075_, v___x_5074_, v___x_5073_, v___x_5072_, v___x_5071_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5077_, lean_object* v_x_5078_){
_start:
{
if (lean_obj_tag(v_x_5077_) == 0)
{
return v_x_5078_;
}
else
{
lean_object* v_head_5079_; lean_object* v_fst_5080_; 
v_head_5079_ = lean_ctor_get(v_x_5077_, 0);
v_fst_5080_ = lean_ctor_get(v_head_5079_, 0);
if (lean_obj_tag(v_fst_5080_) == 0)
{
lean_object* v_tail_5081_; 
v_tail_5081_ = lean_ctor_get(v_x_5077_, 1);
lean_inc(v_tail_5081_);
lean_dec_ref_known(v_x_5077_, 2);
v_x_5077_ = v_tail_5081_;
goto _start;
}
else
{
lean_object* v_tail_5083_; lean_object* v_snd_5084_; lean_object* v_val_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; 
lean_inc_ref(v_fst_5080_);
lean_inc(v_head_5079_);
v_tail_5083_ = lean_ctor_get(v_x_5077_, 1);
lean_inc(v_tail_5083_);
lean_dec_ref_known(v_x_5077_, 2);
v_snd_5084_ = lean_ctor_get(v_head_5079_, 1);
lean_inc(v_snd_5084_);
lean_dec(v_head_5079_);
v_val_5085_ = lean_ctor_get(v_fst_5080_, 0);
lean_inc(v_val_5085_);
lean_dec_ref_known(v_fst_5080_, 1);
v___x_5086_ = lean_array_get_size(v_x_5078_);
v___x_5087_ = lean_nat_dec_lt(v_val_5085_, v___x_5086_);
if (v___x_5087_ == 0)
{
lean_object* v___x_5088_; lean_object* v___x_5089_; 
lean_dec(v_val_5085_);
lean_dec(v_snd_5084_);
lean_dec(v_tail_5083_);
lean_dec_ref(v_x_5078_);
v___x_5088_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5089_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5088_);
return v___x_5089_;
}
else
{
lean_object* v___x_5090_; 
v___x_5090_ = lean_array_set(v_x_5078_, v_val_5085_, v_snd_5084_);
lean_dec(v_val_5085_);
v_x_5077_ = v_tail_5083_;
v_x_5078_ = v___x_5090_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5092_, lean_object* v_x_5093_, lean_object* v_x_5094_){
_start:
{
lean_object* v___x_5095_; 
v___x_5095_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5093_, v_x_5094_);
return v___x_5095_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5098_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5099_ = lean_unsigned_to_nat(2u);
v___x_5100_ = lean_unsigned_to_nat(384u);
v___x_5101_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5102_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5103_ = l_mkPanicMessageWithDecl(v___x_5102_, v___x_5101_, v___x_5100_, v___x_5099_, v___x_5098_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5106_, lean_object* v_xs_5107_){
_start:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; uint8_t v___x_5110_; 
v___x_5108_ = lean_array_get_size(v_xs_5107_);
v___x_5109_ = lean_array_get_size(v_perm_5106_);
v___x_5110_ = lean_nat_dec_eq(v___x_5108_, v___x_5109_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; lean_object* v___x_5112_; 
v___x_5111_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5112_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5111_);
return v___x_5112_;
}
else
{
lean_object* v___x_5113_; uint8_t v___x_5114_; 
v___x_5113_ = lean_unsigned_to_nat(0u);
v___x_5114_ = lean_nat_dec_eq(v___x_5108_, v___x_5113_);
if (v___x_5114_ == 0)
{
lean_object* v_dummy_5115_; lean_object* v___x_5116_; lean_object* v_ys_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v_dummy_5115_ = lean_array_fget_borrowed(v_xs_5107_, v___x_5113_);
v___x_5116_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5106_);
lean_inc(v_dummy_5115_);
v_ys_5117_ = lean_mk_array(v___x_5116_, v_dummy_5115_);
v___x_5118_ = l_Array_zip___redArg(v_perm_5106_, v_xs_5107_);
v___x_5119_ = lean_array_to_list(v___x_5118_);
v___x_5120_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5119_, v_ys_5117_);
return v___x_5120_;
}
else
{
lean_object* v___x_5121_; 
v___x_5121_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5122_, lean_object* v_xs_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5122_, v_xs_5123_);
lean_dec_ref(v_xs_5123_);
lean_dec_ref(v_perm_5122_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5125_, lean_object* v_perm_5126_, lean_object* v_xs_5127_){
_start:
{
lean_object* v___x_5128_; 
v___x_5128_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5126_, v_xs_5127_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5129_, lean_object* v_perm_5130_, lean_object* v_xs_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5129_, v_perm_5130_, v_xs_5131_);
lean_dec_ref(v_xs_5131_);
lean_dec_ref(v_perm_5130_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5133_, lean_object* v_upperBound_5134_, lean_object* v_perm_5135_, lean_object* v_a_5136_, lean_object* v_b_5137_){
_start:
{
lean_object* v_a_5139_; uint8_t v___x_5146_; 
v___x_5146_ = lean_nat_dec_lt(v_a_5136_, v_upperBound_5134_);
if (v___x_5146_ == 0)
{
lean_dec(v_a_5136_);
return v_b_5137_;
}
else
{
lean_object* v___x_5147_; uint8_t v___x_5148_; 
v___x_5147_ = lean_array_get_size(v_perm_5135_);
v___x_5148_ = lean_nat_dec_lt(v_a_5136_, v___x_5147_);
if (v___x_5148_ == 0)
{
goto v___jp_5143_;
}
else
{
lean_object* v___x_5149_; 
v___x_5149_ = lean_array_fget_borrowed(v_perm_5135_, v_a_5136_);
if (lean_obj_tag(v___x_5149_) == 0)
{
goto v___jp_5143_;
}
else
{
v_a_5139_ = v_b_5137_;
goto v___jp_5138_;
}
}
}
v___jp_5138_:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___x_5140_ = lean_unsigned_to_nat(1u);
v___x_5141_ = lean_nat_add(v_a_5136_, v___x_5140_);
lean_dec(v_a_5136_);
v_a_5136_ = v___x_5141_;
v_b_5137_ = v_a_5139_;
goto _start;
}
v___jp_5143_:
{
lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5144_ = lean_array_fget_borrowed(v_xs_5133_, v_a_5136_);
lean_inc(v___x_5144_);
v___x_5145_ = lean_array_push(v_b_5137_, v___x_5144_);
v_a_5139_ = v___x_5145_;
goto v___jp_5138_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5150_, lean_object* v_upperBound_5151_, lean_object* v_perm_5152_, lean_object* v_a_5153_, lean_object* v_b_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5150_, v_upperBound_5151_, v_perm_5152_, v_a_5153_, v_b_5154_);
lean_dec_ref(v_perm_5152_);
lean_dec(v_upperBound_5151_);
lean_dec_ref(v_xs_5150_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5156_, lean_object* v_xs_5157_){
_start:
{
lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v_ys_5160_; lean_object* v___x_5161_; 
v___x_5158_ = lean_array_get_size(v_xs_5157_);
v___x_5159_ = lean_unsigned_to_nat(0u);
v_ys_5160_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5157_, v___x_5158_, v_perm_5156_, v___x_5159_, v_ys_5160_);
return v___x_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5162_, lean_object* v_xs_5163_){
_start:
{
lean_object* v_res_5164_; 
v_res_5164_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5162_, v_xs_5163_);
lean_dec_ref(v_xs_5163_);
lean_dec_ref(v_perm_5162_);
return v_res_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5165_, lean_object* v_perm_5166_, lean_object* v_xs_5167_){
_start:
{
lean_object* v___x_5168_; 
v___x_5168_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5166_, v_xs_5167_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5169_, lean_object* v_perm_5170_, lean_object* v_xs_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5169_, v_perm_5170_, v_xs_5171_);
lean_dec_ref(v_xs_5171_);
lean_dec_ref(v_perm_5170_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5173_, lean_object* v_xs_5174_, lean_object* v_upperBound_5175_, lean_object* v_perm_5176_, lean_object* v_inst_5177_, lean_object* v_R_5178_, lean_object* v_a_5179_, lean_object* v_b_5180_, lean_object* v_c_5181_){
_start:
{
lean_object* v___x_5182_; 
v___x_5182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5174_, v_upperBound_5175_, v_perm_5176_, v_a_5179_, v_b_5180_);
return v___x_5182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5183_, lean_object* v_xs_5184_, lean_object* v_upperBound_5185_, lean_object* v_perm_5186_, lean_object* v_inst_5187_, lean_object* v_R_5188_, lean_object* v_a_5189_, lean_object* v_b_5190_, lean_object* v_c_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5183_, v_xs_5184_, v_upperBound_5185_, v_perm_5186_, v_inst_5187_, v_R_5188_, v_a_5189_, v_b_5190_, v_c_5191_);
lean_dec_ref(v_perm_5186_);
lean_dec(v_upperBound_5185_);
lean_dec_ref(v_xs_5184_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5193_){
_start:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; 
v___x_5194_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5195_ = lean_panic_fn_borrowed(v___x_5194_, v_msg_5193_);
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5196_, lean_object* v_msg_5197_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5197_);
return v___x_5198_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___closed__0(void){
_start:
{
uint8_t v___x_5199_; uint8_t v___x_5200_; 
v___x_5199_ = 1;
v___x_5200_ = lean_bool_not(v___x_5199_);
return v___x_5200_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_as_5201_, size_t v_i_5202_, size_t v_stop_5203_){
_start:
{
uint8_t v___x_5204_; 
v___x_5204_ = lean_usize_dec_eq(v_i_5202_, v_stop_5203_);
if (v___x_5204_ == 0)
{
uint8_t v___x_5205_; uint8_t v___y_5207_; lean_object* v___x_5211_; 
v___x_5205_ = 1;
v___x_5211_ = lean_array_uget_borrowed(v_as_5201_, v_i_5202_);
if (lean_obj_tag(v___x_5211_) == 0)
{
uint8_t v___x_5212_; 
v___x_5212_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___closed__0);
v___y_5207_ = v___x_5212_;
goto v___jp_5206_;
}
else
{
uint8_t v___x_5213_; 
v___x_5213_ = lean_bool_not(v___x_5204_);
v___y_5207_ = v___x_5213_;
goto v___jp_5206_;
}
v___jp_5206_:
{
if (v___y_5207_ == 0)
{
size_t v___x_5208_; size_t v___x_5209_; 
v___x_5208_ = ((size_t)1ULL);
v___x_5209_ = lean_usize_add(v_i_5202_, v___x_5208_);
v_i_5202_ = v___x_5209_;
goto _start;
}
else
{
return v___x_5205_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_as_5215_, lean_object* v_i_5216_, lean_object* v_stop_5217_){
_start:
{
size_t v_i_boxed_5218_; size_t v_stop_boxed_5219_; uint8_t v_res_5220_; lean_object* v_r_5221_; 
v_i_boxed_5218_ = lean_unbox_usize(v_i_5216_);
lean_dec(v_i_5216_);
v_stop_boxed_5219_ = lean_unbox_usize(v_stop_5217_);
lean_dec(v_stop_5217_);
v_res_5220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_as_5215_, v_i_boxed_5218_, v_stop_boxed_5219_);
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
lean_object* v_lower_5244_; lean_object* v_upper_5245_; uint8_t v___y_5250_; lean_object* v___y_5254_; lean_object* v___y_5255_; lean_object* v___y_5256_; lean_object* v_lower_5264_; lean_object* v_upper_5265_; lean_object* v___x_5274_; uint8_t v___x_5275_; 
v___x_5274_ = lean_array_get_size(v_perm_5237_);
v___x_5275_ = lean_nat_dec_lt(v_i_5240_, v___x_5274_);
if (v___x_5275_ == 0)
{
lean_object* v___x_5276_; lean_object* v___x_5277_; uint8_t v___x_5278_; 
lean_dec(v_i_5240_);
lean_dec_ref(v_perm_5237_);
v___x_5276_ = lean_unsigned_to_nat(0u);
v___x_5277_ = lean_array_get_size(v_varyingArgs_5239_);
v___x_5278_ = lean_nat_dec_le(v_j_5241_, v___x_5276_);
if (v___x_5278_ == 0)
{
v_lower_5244_ = v_j_5241_;
v_upper_5245_ = v___x_5277_;
goto v___jp_5243_;
}
else
{
lean_dec(v_j_5241_);
v_lower_5244_ = v___x_5276_;
v_upper_5245_ = v___x_5277_;
goto v___jp_5243_;
}
}
else
{
lean_object* v___x_5279_; 
v___x_5279_ = lean_array_fget_borrowed(v_perm_5237_, v_i_5240_);
if (lean_obj_tag(v___x_5279_) == 1)
{
lean_object* v_val_5280_; lean_object* v___x_5281_; uint8_t v___x_5282_; 
v_val_5280_ = lean_ctor_get(v___x_5279_, 0);
v___x_5281_ = lean_array_get_size(v_fixedArgs_5238_);
v___x_5282_ = lean_nat_dec_lt(v_val_5280_, v___x_5281_);
if (v___x_5282_ == 0)
{
lean_object* v___x_5283_; lean_object* v___x_5284_; 
lean_dec_ref(v_xs_5242_);
lean_dec(v_j_5241_);
lean_dec(v_i_5240_);
lean_dec_ref(v_varyingArgs_5239_);
lean_dec_ref(v_perm_5237_);
v___x_5283_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5284_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5283_);
return v___x_5284_;
}
else
{
lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5285_ = lean_unsigned_to_nat(1u);
v___x_5286_ = lean_nat_add(v_i_5240_, v___x_5285_);
lean_dec(v_i_5240_);
v___x_5287_ = lean_array_fget_borrowed(v_fixedArgs_5238_, v_val_5280_);
lean_inc(v___x_5287_);
v___x_5288_ = lean_array_push(v_xs_5242_, v___x_5287_);
v_i_5240_ = v___x_5286_;
v_xs_5242_ = v___x_5288_;
goto _start;
}
}
else
{
lean_object* v___x_5290_; uint8_t v___x_5291_; 
v___x_5290_ = lean_array_get_size(v_varyingArgs_5239_);
v___x_5291_ = lean_nat_dec_lt(v_j_5241_, v___x_5290_);
if (v___x_5291_ == 0)
{
lean_object* v___x_5292_; uint8_t v___x_5293_; 
lean_dec(v_j_5241_);
lean_dec_ref(v_varyingArgs_5239_);
v___x_5292_ = lean_unsigned_to_nat(0u);
v___x_5293_ = lean_nat_dec_le(v_i_5240_, v___x_5292_);
if (v___x_5293_ == 0)
{
v_lower_5264_ = v_i_5240_;
v_upper_5265_ = v___x_5274_;
goto v___jp_5263_;
}
else
{
lean_dec(v_i_5240_);
v_lower_5264_ = v___x_5292_;
v_upper_5265_ = v___x_5274_;
goto v___jp_5263_;
}
}
else
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5294_ = lean_unsigned_to_nat(1u);
v___x_5295_ = lean_nat_add(v_i_5240_, v___x_5294_);
lean_dec(v_i_5240_);
v___x_5296_ = lean_nat_add(v_j_5241_, v___x_5294_);
v___x_5297_ = lean_array_fget_borrowed(v_varyingArgs_5239_, v_j_5241_);
lean_dec(v_j_5241_);
lean_inc(v___x_5297_);
v___x_5298_ = lean_array_push(v_xs_5242_, v___x_5297_);
v_i_5240_ = v___x_5295_;
v_j_5241_ = v___x_5296_;
v_xs_5242_ = v___x_5298_;
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
if (v___y_5250_ == 0)
{
lean_object* v___x_5251_; lean_object* v___x_5252_; 
lean_dec_ref(v_xs_5242_);
v___x_5251_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5252_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5251_);
return v___x_5252_;
}
else
{
return v_xs_5242_;
}
}
v___jp_5253_:
{
uint8_t v___x_5257_; 
v___x_5257_ = lean_nat_dec_lt(v___y_5255_, v___y_5256_);
if (v___x_5257_ == 0)
{
uint8_t v___x_5258_; 
lean_dec(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
v___x_5258_ = lean_bool_not(v___x_5257_);
v___y_5250_ = v___x_5258_;
goto v___jp_5249_;
}
else
{
size_t v___x_5259_; size_t v___x_5260_; uint8_t v___x_5261_; uint8_t v___x_5262_; 
v___x_5259_ = lean_usize_of_nat(v___y_5255_);
lean_dec(v___y_5255_);
v___x_5260_ = lean_usize_of_nat(v___y_5256_);
lean_dec(v___y_5256_);
v___x_5261_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v___y_5254_, v___x_5259_, v___x_5260_);
lean_dec_ref(v___y_5254_);
v___x_5262_ = lean_bool_not(v___x_5261_);
v___y_5250_ = v___x_5262_;
goto v___jp_5249_;
}
}
v___jp_5263_:
{
lean_object* v___x_5266_; lean_object* v_array_5267_; lean_object* v_start_5268_; lean_object* v_stop_5269_; uint8_t v___x_5270_; 
v___x_5266_ = l_Array_toSubarray___redArg(v_perm_5237_, v_lower_5264_, v_upper_5265_);
v_array_5267_ = lean_ctor_get(v___x_5266_, 0);
lean_inc_ref(v_array_5267_);
v_start_5268_ = lean_ctor_get(v___x_5266_, 1);
lean_inc(v_start_5268_);
v_stop_5269_ = lean_ctor_get(v___x_5266_, 2);
lean_inc(v_stop_5269_);
lean_dec_ref(v___x_5266_);
v___x_5270_ = lean_nat_dec_lt(v_start_5268_, v_stop_5269_);
if (v___x_5270_ == 0)
{
uint8_t v___x_5271_; 
lean_dec(v_stop_5269_);
lean_dec(v_start_5268_);
lean_dec_ref(v_array_5267_);
v___x_5271_ = lean_bool_not(v___x_5270_);
v___y_5250_ = v___x_5271_;
goto v___jp_5249_;
}
else
{
lean_object* v___x_5272_; uint8_t v___x_5273_; 
v___x_5272_ = lean_array_get_size(v_array_5267_);
v___x_5273_ = lean_nat_dec_le(v_stop_5269_, v___x_5272_);
if (v___x_5273_ == 0)
{
lean_dec(v_stop_5269_);
v___y_5254_ = v_array_5267_;
v___y_5255_ = v_start_5268_;
v___y_5256_ = v___x_5272_;
goto v___jp_5253_;
}
else
{
v___y_5254_ = v_array_5267_;
v___y_5255_ = v_start_5268_;
v___y_5256_ = v_stop_5269_;
goto v___jp_5253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5300_, lean_object* v_fixedArgs_5301_, lean_object* v_varyingArgs_5302_, lean_object* v_i_5303_, lean_object* v_j_5304_, lean_object* v_xs_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5300_, v_fixedArgs_5301_, v_varyingArgs_5302_, v_i_5303_, v_j_5304_, v_xs_5305_);
lean_dec_ref(v_fixedArgs_5301_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5307_, lean_object* v_perm_5308_, lean_object* v_fixedArgs_5309_, lean_object* v_varyingArgs_5310_, lean_object* v_i_5311_, lean_object* v_j_5312_, lean_object* v_xs_5313_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5308_, v_fixedArgs_5309_, v_varyingArgs_5310_, v_i_5311_, v_j_5312_, v_xs_5313_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5315_, lean_object* v_perm_5316_, lean_object* v_fixedArgs_5317_, lean_object* v_varyingArgs_5318_, lean_object* v_i_5319_, lean_object* v_j_5320_, lean_object* v_xs_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5315_, v_perm_5316_, v_fixedArgs_5317_, v_varyingArgs_5318_, v_i_5319_, v_j_5320_, v_xs_5321_);
lean_dec_ref(v_fixedArgs_5317_);
return v_res_5322_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5325_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5326_ = lean_unsigned_to_nat(2u);
v___x_5327_ = lean_unsigned_to_nat(416u);
v___x_5328_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5329_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5330_ = l_mkPanicMessageWithDecl(v___x_5329_, v___x_5328_, v___x_5327_, v___x_5326_, v___x_5325_);
return v___x_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5331_, lean_object* v_fixedArgs_5332_, lean_object* v_varyingArgs_5333_){
_start:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; uint8_t v___x_5336_; 
v___x_5334_ = lean_array_get_size(v_fixedArgs_5332_);
v___x_5335_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5331_);
v___x_5336_ = lean_nat_dec_eq(v___x_5334_, v___x_5335_);
lean_dec(v___x_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; lean_object* v___x_5338_; 
lean_dec_ref(v_varyingArgs_5333_);
lean_dec_ref(v_perm_5331_);
v___x_5337_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5338_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5337_);
return v___x_5338_;
}
else
{
lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; 
v___x_5339_ = lean_unsigned_to_nat(0u);
v___x_5340_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5341_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5331_, v_fixedArgs_5332_, v_varyingArgs_5333_, v___x_5339_, v___x_5339_, v___x_5340_);
return v___x_5341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5342_, lean_object* v_fixedArgs_5343_, lean_object* v_varyingArgs_5344_){
_start:
{
lean_object* v_res_5345_; 
v_res_5345_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5342_, v_fixedArgs_5343_, v_varyingArgs_5344_);
lean_dec_ref(v_fixedArgs_5343_);
return v_res_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5346_, lean_object* v_perm_5347_, lean_object* v_fixedArgs_5348_, lean_object* v_varyingArgs_5349_){
_start:
{
lean_object* v___x_5350_; 
v___x_5350_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5347_, v_fixedArgs_5348_, v_varyingArgs_5349_);
return v___x_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5351_, lean_object* v_perm_5352_, lean_object* v_fixedArgs_5353_, lean_object* v_varyingArgs_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5351_, v_perm_5352_, v_fixedArgs_5353_, v_varyingArgs_5354_);
lean_dec_ref(v_fixedArgs_5353_);
return v_res_5355_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5356_, lean_object* v_x_5357_){
_start:
{
if (lean_obj_tag(v_x_5356_) == 0)
{
if (lean_obj_tag(v_x_5357_) == 0)
{
uint8_t v___x_5358_; 
v___x_5358_ = 1;
return v___x_5358_;
}
else
{
uint8_t v___x_5359_; 
v___x_5359_ = 0;
return v___x_5359_;
}
}
else
{
if (lean_obj_tag(v_x_5357_) == 0)
{
uint8_t v___x_5360_; 
v___x_5360_ = 0;
return v___x_5360_;
}
else
{
lean_object* v_val_5361_; lean_object* v_val_5362_; uint8_t v___x_5363_; 
v_val_5361_ = lean_ctor_get(v_x_5356_, 0);
v_val_5362_ = lean_ctor_get(v_x_5357_, 0);
v___x_5363_ = lean_nat_dec_eq(v_val_5361_, v_val_5362_);
return v___x_5363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5364_, lean_object* v_x_5365_){
_start:
{
uint8_t v_res_5366_; lean_object* v_r_5367_; 
v_res_5366_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5364_, v_x_5365_);
lean_dec(v_x_5365_);
lean_dec(v_x_5364_);
v_r_5367_ = lean_box(v_res_5366_);
return v_r_5367_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5368_, lean_object* v_ys_5369_, lean_object* v_x_5370_){
_start:
{
lean_object* v_zero_5371_; uint8_t v_isZero_5372_; 
v_zero_5371_ = lean_unsigned_to_nat(0u);
v_isZero_5372_ = lean_nat_dec_eq(v_x_5370_, v_zero_5371_);
if (v_isZero_5372_ == 1)
{
lean_dec(v_x_5370_);
return v_isZero_5372_;
}
else
{
lean_object* v_one_5373_; lean_object* v_n_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; 
v_one_5373_ = lean_unsigned_to_nat(1u);
v_n_5374_ = lean_nat_sub(v_x_5370_, v_one_5373_);
lean_dec(v_x_5370_);
v___x_5375_ = lean_array_fget_borrowed(v_xs_5368_, v_n_5374_);
v___x_5376_ = lean_array_fget_borrowed(v_ys_5369_, v_n_5374_);
v___x_5377_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5375_, v___x_5376_);
if (v___x_5377_ == 0)
{
lean_dec(v_n_5374_);
return v___x_5377_;
}
else
{
v_x_5370_ = v_n_5374_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5379_, lean_object* v_ys_5380_, lean_object* v_x_5381_){
_start:
{
uint8_t v_res_5382_; lean_object* v_r_5383_; 
v_res_5382_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5379_, v_ys_5380_, v_x_5381_);
lean_dec_ref(v_ys_5380_);
lean_dec_ref(v_xs_5379_);
v_r_5383_ = lean_box(v_res_5382_);
return v_r_5383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5384_, size_t v_i_5385_, lean_object* v_bs_5386_){
_start:
{
uint8_t v___x_5387_; 
v___x_5387_ = lean_usize_dec_lt(v_i_5385_, v_sz_5384_);
if (v___x_5387_ == 0)
{
return v_bs_5386_;
}
else
{
lean_object* v_v_5388_; lean_object* v___x_5389_; lean_object* v_bs_x27_5390_; lean_object* v___x_5391_; size_t v___x_5392_; size_t v___x_5393_; lean_object* v___x_5394_; 
v_v_5388_ = lean_array_uget(v_bs_5386_, v_i_5385_);
v___x_5389_ = lean_unsigned_to_nat(0u);
v_bs_x27_5390_ = lean_array_uset(v_bs_5386_, v_i_5385_, v___x_5389_);
v___x_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5391_, 0, v_v_5388_);
v___x_5392_ = ((size_t)1ULL);
v___x_5393_ = lean_usize_add(v_i_5385_, v___x_5392_);
v___x_5394_ = lean_array_uset(v_bs_x27_5390_, v_i_5385_, v___x_5391_);
v_i_5385_ = v___x_5393_;
v_bs_5386_ = v___x_5394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5396_, lean_object* v_i_5397_, lean_object* v_bs_5398_){
_start:
{
size_t v_sz_boxed_5399_; size_t v_i_boxed_5400_; lean_object* v_res_5401_; 
v_sz_boxed_5399_ = lean_unbox_usize(v_sz_5396_);
lean_dec(v_sz_5396_);
v_i_boxed_5400_ = lean_unbox_usize(v_i_5397_);
lean_dec(v_i_5397_);
v_res_5401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5399_, v_i_boxed_5400_, v_bs_5398_);
return v_res_5401_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5402_, lean_object* v_as_5403_, size_t v_i_5404_, size_t v_stop_5405_){
_start:
{
uint8_t v___x_5406_; 
v___x_5406_ = lean_usize_dec_eq(v_i_5404_, v_stop_5405_);
if (v___x_5406_ == 0)
{
lean_object* v_numFixed_5407_; uint8_t v___x_5408_; uint8_t v___y_5410_; lean_object* v___x_5414_; lean_object* v___x_5415_; size_t v_sz_5416_; size_t v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; uint8_t v___x_5425_; 
v_numFixed_5407_ = lean_ctor_get(v_fixedParamPerms_5402_, 0);
v___x_5408_ = 1;
v___x_5414_ = lean_array_uget_borrowed(v_as_5403_, v_i_5404_);
lean_inc(v_numFixed_5407_);
v___x_5415_ = l_Array_range(v_numFixed_5407_);
v_sz_5416_ = lean_array_size(v___x_5415_);
v___x_5417_ = ((size_t)0ULL);
v___x_5418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5416_, v___x_5417_, v___x_5415_);
v___x_5419_ = lean_array_get_size(v___x_5414_);
v___x_5420_ = lean_nat_sub(v___x_5419_, v_numFixed_5407_);
v___x_5421_ = lean_box(0);
v___x_5422_ = lean_mk_array(v___x_5420_, v___x_5421_);
v___x_5423_ = l_Array_append___redArg(v___x_5418_, v___x_5422_);
lean_dec_ref(v___x_5422_);
v___x_5424_ = lean_array_get_size(v___x_5423_);
v___x_5425_ = lean_nat_dec_eq(v___x_5419_, v___x_5424_);
if (v___x_5425_ == 0)
{
uint8_t v___x_5426_; 
lean_dec_ref(v___x_5423_);
v___x_5426_ = lean_bool_not(v___x_5406_);
v___y_5410_ = v___x_5426_;
goto v___jp_5409_;
}
else
{
uint8_t v___x_5427_; uint8_t v___x_5428_; 
v___x_5427_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5414_, v___x_5423_, v___x_5419_);
lean_dec_ref(v___x_5423_);
v___x_5428_ = lean_bool_not(v___x_5427_);
v___y_5410_ = v___x_5428_;
goto v___jp_5409_;
}
v___jp_5409_:
{
if (v___y_5410_ == 0)
{
size_t v___x_5411_; size_t v___x_5412_; 
v___x_5411_ = ((size_t)1ULL);
v___x_5412_ = lean_usize_add(v_i_5404_, v___x_5411_);
v_i_5404_ = v___x_5412_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5402_);
return v___x_5408_;
}
}
}
else
{
uint8_t v___x_5429_; 
lean_dec_ref(v_fixedParamPerms_5402_);
v___x_5429_ = 0;
return v___x_5429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5430_, lean_object* v_as_5431_, lean_object* v_i_5432_, lean_object* v_stop_5433_){
_start:
{
size_t v_i_boxed_5434_; size_t v_stop_boxed_5435_; uint8_t v_res_5436_; lean_object* v_r_5437_; 
v_i_boxed_5434_ = lean_unbox_usize(v_i_5432_);
lean_dec(v_i_5432_);
v_stop_boxed_5435_ = lean_unbox_usize(v_stop_5433_);
lean_dec(v_stop_5433_);
v_res_5436_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5430_, v_as_5431_, v_i_boxed_5434_, v_stop_boxed_5435_);
lean_dec_ref(v_as_5431_);
v_r_5437_ = lean_box(v_res_5436_);
return v_r_5437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5438_){
_start:
{
lean_object* v_perms_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; uint8_t v___x_5442_; 
v_perms_5439_ = lean_ctor_get(v_fixedParamPerms_5438_, 1);
lean_inc_ref(v_perms_5439_);
v___x_5440_ = lean_unsigned_to_nat(0u);
v___x_5441_ = lean_array_get_size(v_perms_5439_);
v___x_5442_ = lean_nat_dec_lt(v___x_5440_, v___x_5441_);
if (v___x_5442_ == 0)
{
uint8_t v___x_5443_; 
lean_dec_ref(v_perms_5439_);
lean_dec_ref(v_fixedParamPerms_5438_);
v___x_5443_ = lean_bool_not(v___x_5442_);
return v___x_5443_;
}
else
{
if (v___x_5442_ == 0)
{
uint8_t v___x_5444_; 
lean_dec_ref(v_perms_5439_);
lean_dec_ref(v_fixedParamPerms_5438_);
v___x_5444_ = lean_bool_not(v___x_5442_);
return v___x_5444_;
}
else
{
size_t v___x_5445_; size_t v___x_5446_; uint8_t v___x_5447_; uint8_t v___x_5448_; 
v___x_5445_ = ((size_t)0ULL);
v___x_5446_ = lean_usize_of_nat(v___x_5441_);
v___x_5447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5438_, v_perms_5439_, v___x_5445_, v___x_5446_);
lean_dec_ref(v_perms_5439_);
v___x_5448_ = lean_bool_not(v___x_5447_);
return v___x_5448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5449_){
_start:
{
uint8_t v_res_5450_; lean_object* v_r_5451_; 
v_res_5450_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5449_);
v_r_5451_ = lean_box(v_res_5450_);
return v_r_5451_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5452_, lean_object* v_ys_5453_, lean_object* v_hsz_5454_, lean_object* v_x_5455_, lean_object* v_x_5456_){
_start:
{
uint8_t v___x_5457_; 
v___x_5457_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5452_, v_ys_5453_, v_x_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5458_, lean_object* v_ys_5459_, lean_object* v_hsz_5460_, lean_object* v_x_5461_, lean_object* v_x_5462_){
_start:
{
uint8_t v_res_5463_; lean_object* v_r_5464_; 
v_res_5463_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5458_, v_ys_5459_, v_hsz_5460_, v_x_5461_, v_x_5462_);
lean_dec_ref(v_ys_5459_);
lean_dec_ref(v_xs_5458_);
v_r_5464_ = lean_box(v_res_5463_);
return v_r_5464_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5465_; 
v___x_5465_ = l_Array_instInhabited(lean_box(0));
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5466_){
_start:
{
lean_object* v___f_5467_; lean_object* v___f_5468_; lean_object* v___f_5469_; lean_object* v___f_5470_; lean_object* v___f_5471_; lean_object* v___f_5472_; lean_object* v___f_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___f_5467_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5468_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5469_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5470_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5471_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5472_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5473_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5474_, 0, v___f_5467_);
lean_ctor_set(v___x_5474_, 1, v___f_5468_);
v___x_5475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5475_, 0, v___x_5474_);
lean_ctor_set(v___x_5475_, 1, v___f_5469_);
lean_ctor_set(v___x_5475_, 2, v___f_5470_);
lean_ctor_set(v___x_5475_, 3, v___f_5471_);
lean_ctor_set(v___x_5475_, 4, v___f_5472_);
v___x_5476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5476_, 0, v___x_5475_);
lean_ctor_set(v___x_5476_, 1, v___f_5473_);
v___x_5477_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5478_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5478_);
lean_ctor_set(v___x_5479_, 1, v___x_5478_);
v___x_5480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5477_);
lean_ctor_set(v___x_5480_, 1, v___x_5479_);
v___x_5481_ = l_instInhabitedOfMonad___redArg(v___x_5476_, v___x_5480_);
v___x_5482_ = lean_panic_fn_borrowed(v___x_5481_, v_msg_5466_);
lean_dec(v___x_5481_);
return v___x_5482_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5483_; 
v___x_5483_ = l_Array_instInhabited(lean_box(0));
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5484_){
_start:
{
lean_object* v___f_5485_; lean_object* v___f_5486_; lean_object* v___f_5487_; lean_object* v___f_5488_; lean_object* v___f_5489_; lean_object* v___f_5490_; lean_object* v___f_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___f_5485_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5486_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5487_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5488_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5489_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5490_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5491_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5492_, 0, v___f_5485_);
lean_ctor_set(v___x_5492_, 1, v___f_5486_);
v___x_5493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5493_, 0, v___x_5492_);
lean_ctor_set(v___x_5493_, 1, v___f_5487_);
lean_ctor_set(v___x_5493_, 2, v___f_5488_);
lean_ctor_set(v___x_5493_, 3, v___f_5489_);
lean_ctor_set(v___x_5493_, 4, v___f_5490_);
v___x_5494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5494_, 0, v___x_5493_);
lean_ctor_set(v___x_5494_, 1, v___f_5491_);
v___x_5495_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5496_, 0, v___x_5495_);
v___x_5497_ = l_instInhabitedOfMonad___redArg(v___x_5494_, v___x_5496_);
v___x_5498_ = lean_panic_fn_borrowed(v___x_5497_, v_msg_5484_);
lean_dec(v___x_5497_);
return v___x_5498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5499_, uint8_t v___y_5500_, lean_object* v_as_5501_, size_t v_sz_5502_, size_t v_i_5503_, lean_object* v_b_5504_){
_start:
{
lean_object* v_a_5506_; uint8_t v___x_5510_; 
v___x_5510_ = lean_usize_dec_lt(v_i_5503_, v_sz_5502_);
if (v___x_5510_ == 0)
{
return v_b_5504_;
}
else
{
lean_object* v_fst_5511_; lean_object* v_snd_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5537_; 
v_fst_5511_ = lean_ctor_get(v_b_5504_, 0);
v_snd_5512_ = lean_ctor_get(v_b_5504_, 1);
v_isSharedCheck_5537_ = !lean_is_exclusive(v_b_5504_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5514_ = v_b_5504_;
v_isShared_5515_ = v_isSharedCheck_5537_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_snd_5512_);
lean_inc(v_fst_5511_);
lean_dec(v_b_5504_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5537_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v_a_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; 
v_a_5516_ = lean_array_uget_borrowed(v_as_5501_, v_i_5503_);
v___x_5517_ = lean_box(0);
v___x_5518_ = lean_array_get_borrowed(v___x_5517_, v___x_5499_, v_a_5516_);
if (lean_obj_tag(v___x_5518_) == 1)
{
lean_object* v_val_5519_; uint8_t v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; uint8_t v___x_5523_; uint8_t v___x_5524_; 
v_val_5519_ = lean_ctor_get(v___x_5518_, 0);
v___x_5520_ = 0;
v___x_5521_ = lean_box(v___x_5520_);
v___x_5522_ = lean_array_get(v___x_5521_, v_fst_5511_, v_val_5519_);
lean_dec(v___x_5521_);
v___x_5523_ = lean_unbox(v___x_5522_);
lean_dec(v___x_5522_);
v___x_5524_ = lean_bool_not(v___x_5523_);
if (v___x_5524_ == 0)
{
lean_object* v___x_5526_; 
if (v_isShared_5515_ == 0)
{
v___x_5526_ = v___x_5514_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_fst_5511_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v_snd_5512_);
v___x_5526_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
v_a_5506_ = v___x_5526_;
goto v___jp_5505_;
}
}
else
{
lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5532_; 
lean_dec(v_snd_5512_);
v___x_5528_ = lean_box(v___y_5500_);
v___x_5529_ = lean_array_set(v_fst_5511_, v_val_5519_, v___x_5528_);
v___x_5530_ = lean_box(v___y_5500_);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5530_);
lean_ctor_set(v___x_5514_, 0, v___x_5529_);
v___x_5532_ = v___x_5514_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5529_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v___x_5530_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
v_a_5506_ = v___x_5532_;
goto v___jp_5505_;
}
}
}
else
{
lean_object* v___x_5535_; 
if (v_isShared_5515_ == 0)
{
v___x_5535_ = v___x_5514_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_fst_5511_);
lean_ctor_set(v_reuseFailAlloc_5536_, 1, v_snd_5512_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
v_a_5506_ = v___x_5535_;
goto v___jp_5505_;
}
}
}
}
v___jp_5505_:
{
size_t v___x_5507_; size_t v___x_5508_; 
v___x_5507_ = ((size_t)1ULL);
v___x_5508_ = lean_usize_add(v_i_5503_, v___x_5507_);
v_i_5503_ = v___x_5508_;
v_b_5504_ = v_a_5506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5538_, lean_object* v___y_5539_, lean_object* v_as_5540_, lean_object* v_sz_5541_, lean_object* v_i_5542_, lean_object* v_b_5543_){
_start:
{
uint8_t v___y_7945__boxed_5544_; size_t v_sz_boxed_5545_; size_t v_i_boxed_5546_; lean_object* v_res_5547_; 
v___y_7945__boxed_5544_ = lean_unbox(v___y_5539_);
v_sz_boxed_5545_ = lean_unbox_usize(v_sz_5541_);
lean_dec(v_sz_5541_);
v_i_boxed_5546_ = lean_unbox_usize(v_i_5542_);
lean_dec(v_i_5542_);
v_res_5547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5538_, v___y_7945__boxed_5544_, v_as_5540_, v_sz_boxed_5545_, v_i_boxed_5546_, v_b_5543_);
lean_dec_ref(v_as_5540_);
lean_dec_ref(v___x_5538_);
return v_res_5547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object* v_upperBound_5548_, lean_object* v___x_5549_, lean_object* v_fixedParamPerms_5550_, lean_object* v_next_5551_, uint8_t v___y_5552_, lean_object* v_a_5553_, lean_object* v_b_5554_){
_start:
{
lean_object* v_a_5556_; uint8_t v___x_5560_; 
v___x_5560_ = lean_nat_dec_lt(v_a_5553_, v_upperBound_5548_);
if (v___x_5560_ == 0)
{
lean_dec(v_a_5553_);
return v_b_5554_;
}
else
{
lean_object* v_fst_5561_; lean_object* v_snd_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5597_; 
v_fst_5561_ = lean_ctor_get(v_b_5554_, 0);
v_snd_5562_ = lean_ctor_get(v_b_5554_, 1);
v_isSharedCheck_5597_ = !lean_is_exclusive(v_b_5554_);
if (v_isSharedCheck_5597_ == 0)
{
v___x_5564_ = v_b_5554_;
v_isShared_5565_ = v_isSharedCheck_5597_;
goto v_resetjp_5563_;
}
else
{
lean_inc(v_snd_5562_);
lean_inc(v_fst_5561_);
lean_dec(v_b_5554_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5597_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5566_; 
v___x_5566_ = lean_array_fget_borrowed(v___x_5549_, v_a_5553_);
if (lean_obj_tag(v___x_5566_) == 1)
{
lean_object* v_val_5567_; uint8_t v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; uint8_t v___x_5571_; 
v_val_5567_ = lean_ctor_get(v___x_5566_, 0);
v___x_5568_ = 0;
v___x_5569_ = lean_box(v___x_5568_);
v___x_5570_ = lean_array_get(v___x_5569_, v_fst_5561_, v_val_5567_);
lean_dec(v___x_5569_);
v___x_5571_ = lean_unbox(v___x_5570_);
lean_dec(v___x_5570_);
if (v___x_5571_ == 0)
{
lean_object* v___x_5573_; 
if (v_isShared_5565_ == 0)
{
v___x_5573_ = v___x_5564_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_fst_5561_);
lean_ctor_set(v_reuseFailAlloc_5574_, 1, v_snd_5562_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
v_a_5556_ = v___x_5573_;
goto v___jp_5555_;
}
}
else
{
lean_object* v_revDeps_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5580_; 
v_revDeps_5575_ = lean_ctor_get(v_fixedParamPerms_5550_, 2);
v___x_5576_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5577_ = lean_array_get_borrowed(v___x_5576_, v_revDeps_5575_, v_next_5551_);
v___x_5578_ = lean_array_get_borrowed(v___x_5576_, v___x_5577_, v_a_5553_);
if (v_isShared_5565_ == 0)
{
v___x_5580_ = v___x_5564_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_fst_5561_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_snd_5562_);
v___x_5580_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
size_t v_sz_5581_; size_t v___x_5582_; lean_object* v___x_5583_; lean_object* v_fst_5584_; lean_object* v_snd_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
v_sz_5581_ = lean_array_size(v___x_5578_);
v___x_5582_ = ((size_t)0ULL);
v___x_5583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5549_, v___y_5552_, v___x_5578_, v_sz_5581_, v___x_5582_, v___x_5580_);
v_fst_5584_ = lean_ctor_get(v___x_5583_, 0);
v_snd_5585_ = lean_ctor_get(v___x_5583_, 1);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5583_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5587_ = v___x_5583_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_snd_5585_);
lean_inc(v_fst_5584_);
lean_dec(v___x_5583_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_fst_5584_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v_snd_5585_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
v_a_5556_ = v___x_5590_;
goto v___jp_5555_;
}
}
}
}
}
else
{
lean_object* v___x_5595_; 
if (v_isShared_5565_ == 0)
{
v___x_5595_ = v___x_5564_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_fst_5561_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_snd_5562_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
v_a_5556_ = v___x_5595_;
goto v___jp_5555_;
}
}
}
}
v___jp_5555_:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5557_ = lean_unsigned_to_nat(1u);
v___x_5558_ = lean_nat_add(v_a_5553_, v___x_5557_);
lean_dec(v_a_5553_);
v_a_5553_ = v___x_5558_;
v_b_5554_ = v_a_5556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object* v_upperBound_5598_, lean_object* v___x_5599_, lean_object* v_fixedParamPerms_5600_, lean_object* v_next_5601_, lean_object* v___y_5602_, lean_object* v_a_5603_, lean_object* v_b_5604_){
_start:
{
uint8_t v___y_8013__boxed_5605_; lean_object* v_res_5606_; 
v___y_8013__boxed_5605_ = lean_unbox(v___y_5602_);
v_res_5606_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5598_, v___x_5599_, v_fixedParamPerms_5600_, v_next_5601_, v___y_8013__boxed_5605_, v_a_5603_, v_b_5604_);
lean_dec(v_next_5601_);
lean_dec_ref(v_fixedParamPerms_5600_);
lean_dec_ref(v___x_5599_);
lean_dec(v_upperBound_5598_);
return v_res_5606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5607_, lean_object* v___x_5608_, uint8_t v___y_5609_, lean_object* v_fixedParamPerms_5610_, lean_object* v_next_5611_, lean_object* v_a_5612_, lean_object* v_b_5613_){
_start:
{
lean_object* v_a_5615_; uint8_t v___x_5619_; 
v___x_5619_ = lean_nat_dec_lt(v_a_5612_, v_upperBound_5607_);
if (v___x_5619_ == 0)
{
return v_b_5613_;
}
else
{
lean_object* v_fst_5620_; lean_object* v_snd_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5656_; 
v_fst_5620_ = lean_ctor_get(v_b_5613_, 0);
v_snd_5621_ = lean_ctor_get(v_b_5613_, 1);
v_isSharedCheck_5656_ = !lean_is_exclusive(v_b_5613_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5623_ = v_b_5613_;
v_isShared_5624_ = v_isSharedCheck_5656_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_snd_5621_);
lean_inc(v_fst_5620_);
lean_dec(v_b_5613_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5656_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5625_; 
v___x_5625_ = lean_array_fget_borrowed(v___x_5608_, v_a_5612_);
if (lean_obj_tag(v___x_5625_) == 1)
{
lean_object* v_val_5626_; uint8_t v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; uint8_t v___x_5630_; 
v_val_5626_ = lean_ctor_get(v___x_5625_, 0);
v___x_5627_ = 0;
v___x_5628_ = lean_box(v___x_5627_);
v___x_5629_ = lean_array_get(v___x_5628_, v_fst_5620_, v_val_5626_);
lean_dec(v___x_5628_);
v___x_5630_ = lean_unbox(v___x_5629_);
lean_dec(v___x_5629_);
if (v___x_5630_ == 0)
{
lean_object* v___x_5632_; 
if (v_isShared_5624_ == 0)
{
v___x_5632_ = v___x_5623_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_fst_5620_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v_snd_5621_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
v_a_5615_ = v___x_5632_;
goto v___jp_5614_;
}
}
else
{
lean_object* v_revDeps_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5639_; 
v_revDeps_5634_ = lean_ctor_get(v_fixedParamPerms_5610_, 2);
v___x_5635_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5636_ = lean_array_get_borrowed(v___x_5635_, v_revDeps_5634_, v_next_5611_);
v___x_5637_ = lean_array_get_borrowed(v___x_5635_, v___x_5636_, v_a_5612_);
if (v_isShared_5624_ == 0)
{
v___x_5639_ = v___x_5623_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_fst_5620_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_snd_5621_);
v___x_5639_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
size_t v_sz_5640_; size_t v___x_5641_; lean_object* v___x_5642_; lean_object* v_fst_5643_; lean_object* v_snd_5644_; lean_object* v___x_5646_; uint8_t v_isShared_5647_; uint8_t v_isSharedCheck_5651_; 
v_sz_5640_ = lean_array_size(v___x_5637_);
v___x_5641_ = ((size_t)0ULL);
v___x_5642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5608_, v___y_5609_, v___x_5637_, v_sz_5640_, v___x_5641_, v___x_5639_);
v_fst_5643_ = lean_ctor_get(v___x_5642_, 0);
v_snd_5644_ = lean_ctor_get(v___x_5642_, 1);
v_isSharedCheck_5651_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5651_ == 0)
{
v___x_5646_ = v___x_5642_;
v_isShared_5647_ = v_isSharedCheck_5651_;
goto v_resetjp_5645_;
}
else
{
lean_inc(v_snd_5644_);
lean_inc(v_fst_5643_);
lean_dec(v___x_5642_);
v___x_5646_ = lean_box(0);
v_isShared_5647_ = v_isSharedCheck_5651_;
goto v_resetjp_5645_;
}
v_resetjp_5645_:
{
lean_object* v___x_5649_; 
if (v_isShared_5647_ == 0)
{
v___x_5649_ = v___x_5646_;
goto v_reusejp_5648_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_fst_5643_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v_snd_5644_);
v___x_5649_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5648_;
}
v_reusejp_5648_:
{
v_a_5615_ = v___x_5649_;
goto v___jp_5614_;
}
}
}
}
}
else
{
lean_object* v___x_5654_; 
if (v_isShared_5624_ == 0)
{
v___x_5654_ = v___x_5623_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_fst_5620_);
lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_snd_5621_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
v_a_5615_ = v___x_5654_;
goto v___jp_5614_;
}
}
}
}
v___jp_5614_:
{
lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; 
v___x_5616_ = lean_unsigned_to_nat(1u);
v___x_5617_ = lean_nat_add(v_a_5612_, v___x_5616_);
v___x_5618_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5607_, v___x_5608_, v_fixedParamPerms_5610_, v_next_5611_, v___y_5609_, v___x_5617_, v_a_5615_);
return v___x_5618_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5657_, lean_object* v___x_5658_, lean_object* v___y_5659_, lean_object* v_fixedParamPerms_5660_, lean_object* v_next_5661_, lean_object* v_a_5662_, lean_object* v_b_5663_){
_start:
{
uint8_t v___y_8097__boxed_5664_; lean_object* v_res_5665_; 
v___y_8097__boxed_5664_ = lean_unbox(v___y_5659_);
v_res_5665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5657_, v___x_5658_, v___y_8097__boxed_5664_, v_fixedParamPerms_5660_, v_next_5661_, v_a_5662_, v_b_5663_);
lean_dec(v_a_5662_);
lean_dec(v_next_5661_);
lean_dec_ref(v_fixedParamPerms_5660_);
lean_dec_ref(v___x_5658_);
lean_dec(v_upperBound_5657_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5666_, lean_object* v___x_5667_, uint8_t v___y_5668_, lean_object* v_fixedParamPerms_5669_, lean_object* v_a_5670_, lean_object* v_b_5671_){
_start:
{
uint8_t v___x_5672_; 
v___x_5672_ = lean_nat_dec_lt(v_a_5670_, v_upperBound_5666_);
if (v___x_5672_ == 0)
{
lean_dec(v_a_5670_);
return v_b_5671_;
}
else
{
lean_object* v_fst_5673_; lean_object* v_snd_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5697_; 
v_fst_5673_ = lean_ctor_get(v_b_5671_, 0);
v_snd_5674_ = lean_ctor_get(v_b_5671_, 1);
v_isSharedCheck_5697_ = !lean_is_exclusive(v_b_5671_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5676_ = v_b_5671_;
v_isShared_5677_ = v_isSharedCheck_5697_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_snd_5674_);
lean_inc(v_fst_5673_);
lean_dec(v_b_5671_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5697_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5682_; 
v___x_5678_ = lean_array_fget_borrowed(v___x_5667_, v_a_5670_);
v___x_5679_ = lean_array_get_size(v___x_5678_);
v___x_5680_ = lean_unsigned_to_nat(0u);
if (v_isShared_5677_ == 0)
{
v___x_5682_ = v___x_5676_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_fst_5673_);
lean_ctor_set(v_reuseFailAlloc_5696_, 1, v_snd_5674_);
v___x_5682_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
lean_object* v___x_5683_; lean_object* v_fst_5684_; lean_object* v_snd_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5695_; 
v___x_5683_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5679_, v___x_5678_, v___y_5668_, v_fixedParamPerms_5669_, v_a_5670_, v___x_5680_, v___x_5682_);
v_fst_5684_ = lean_ctor_get(v___x_5683_, 0);
v_snd_5685_ = lean_ctor_get(v___x_5683_, 1);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5687_ = v___x_5683_;
v_isShared_5688_ = v_isSharedCheck_5695_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_snd_5685_);
lean_inc(v_fst_5684_);
lean_dec(v___x_5683_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5695_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v___x_5690_; 
if (v_isShared_5688_ == 0)
{
v___x_5690_ = v___x_5687_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_fst_5684_);
lean_ctor_set(v_reuseFailAlloc_5694_, 1, v_snd_5685_);
v___x_5690_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5691_ = lean_unsigned_to_nat(1u);
v___x_5692_ = lean_nat_add(v_a_5670_, v___x_5691_);
lean_dec(v_a_5670_);
v_a_5670_ = v___x_5692_;
v_b_5671_ = v___x_5690_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5698_, lean_object* v___x_5699_, lean_object* v___y_5700_, lean_object* v_fixedParamPerms_5701_, lean_object* v_a_5702_, lean_object* v_b_5703_){
_start:
{
uint8_t v___y_8180__boxed_5704_; lean_object* v_res_5705_; 
v___y_8180__boxed_5704_ = lean_unbox(v___y_5700_);
v_res_5705_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5698_, v___x_5699_, v___y_8180__boxed_5704_, v_fixedParamPerms_5701_, v_a_5702_, v_b_5703_);
lean_dec_ref(v_fixedParamPerms_5701_);
lean_dec_ref(v___x_5699_);
lean_dec(v_upperBound_5698_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5706_, lean_object* v___x_5707_, uint8_t v___y_5708_, lean_object* v_fixedParamPerms_5709_, lean_object* v_a_5710_){
_start:
{
lean_object* v_snd_5711_; uint8_t v___x_5712_; 
v_snd_5711_ = lean_ctor_get(v_a_5710_, 1);
v___x_5712_ = lean_unbox(v_snd_5711_);
if (v___x_5712_ == 0)
{
lean_object* v_fst_5713_; lean_object* v___x_5715_; uint8_t v_isShared_5716_; uint8_t v_isSharedCheck_5720_; 
lean_inc(v_snd_5711_);
v_fst_5713_ = lean_ctor_get(v_a_5710_, 0);
v_isSharedCheck_5720_ = !lean_is_exclusive(v_a_5710_);
if (v_isSharedCheck_5720_ == 0)
{
lean_object* v_unused_5721_; 
v_unused_5721_ = lean_ctor_get(v_a_5710_, 1);
lean_dec(v_unused_5721_);
v___x_5715_ = v_a_5710_;
v_isShared_5716_ = v_isSharedCheck_5720_;
goto v_resetjp_5714_;
}
else
{
lean_inc(v_fst_5713_);
lean_dec(v_a_5710_);
v___x_5715_ = lean_box(0);
v_isShared_5716_ = v_isSharedCheck_5720_;
goto v_resetjp_5714_;
}
v_resetjp_5714_:
{
lean_object* v___x_5718_; 
if (v_isShared_5716_ == 0)
{
v___x_5718_ = v___x_5715_;
goto v_reusejp_5717_;
}
else
{
lean_object* v_reuseFailAlloc_5719_; 
v_reuseFailAlloc_5719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5719_, 0, v_fst_5713_);
lean_ctor_set(v_reuseFailAlloc_5719_, 1, v_snd_5711_);
v___x_5718_ = v_reuseFailAlloc_5719_;
goto v_reusejp_5717_;
}
v_reusejp_5717_:
{
return v___x_5718_;
}
}
}
else
{
lean_object* v_fst_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5743_; 
v_fst_5722_ = lean_ctor_get(v_a_5710_, 0);
v_isSharedCheck_5743_ = !lean_is_exclusive(v_a_5710_);
if (v_isSharedCheck_5743_ == 0)
{
lean_object* v_unused_5744_; 
v_unused_5744_ = lean_ctor_get(v_a_5710_, 1);
lean_dec(v_unused_5744_);
v___x_5724_ = v_a_5710_;
v_isShared_5725_ = v_isSharedCheck_5743_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_fst_5722_);
lean_dec(v_a_5710_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5743_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
uint8_t v_changed_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5730_; 
v_changed_5726_ = 0;
v___x_5727_ = lean_unsigned_to_nat(0u);
v___x_5728_ = lean_box(v_changed_5726_);
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5728_);
v___x_5730_ = v___x_5724_;
goto v_reusejp_5729_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_fst_5722_);
lean_ctor_set(v_reuseFailAlloc_5742_, 1, v___x_5728_);
v___x_5730_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5729_;
}
v_reusejp_5729_:
{
lean_object* v___x_5731_; lean_object* v_fst_5732_; lean_object* v_snd_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5741_; 
v___x_5731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5706_, v___x_5707_, v___y_5708_, v_fixedParamPerms_5709_, v___x_5727_, v___x_5730_);
v_fst_5732_ = lean_ctor_get(v___x_5731_, 0);
v_snd_5733_ = lean_ctor_get(v___x_5731_, 1);
v_isSharedCheck_5741_ = !lean_is_exclusive(v___x_5731_);
if (v_isSharedCheck_5741_ == 0)
{
v___x_5735_ = v___x_5731_;
v_isShared_5736_ = v_isSharedCheck_5741_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_snd_5733_);
lean_inc(v_fst_5732_);
lean_dec(v___x_5731_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5741_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5736_ == 0)
{
v___x_5738_ = v___x_5735_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_fst_5732_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v_snd_5733_);
v___x_5738_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
v_a_5710_ = v___x_5738_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5745_, lean_object* v___x_5746_, lean_object* v___y_5747_, lean_object* v_fixedParamPerms_5748_, lean_object* v_a_5749_){
_start:
{
uint8_t v___y_8233__boxed_5750_; lean_object* v_res_5751_; 
v___y_8233__boxed_5750_ = lean_unbox(v___y_5747_);
v_res_5751_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5745_, v___x_5746_, v___y_8233__boxed_5750_, v_fixedParamPerms_5748_, v_a_5749_);
lean_dec_ref(v_fixedParamPerms_5748_);
lean_dec_ref(v___x_5746_);
lean_dec(v___x_5745_);
return v_res_5751_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5752_, lean_object* v_a_5753_, lean_object* v_b_5754_){
_start:
{
lean_object* v_a_5756_; uint8_t v___x_5760_; 
v___x_5760_ = lean_nat_dec_lt(v_a_5753_, v_upperBound_5752_);
if (v___x_5760_ == 0)
{
lean_dec(v_a_5753_);
return v_b_5754_;
}
else
{
lean_object* v_snd_5761_; lean_object* v_snd_5762_; lean_object* v_snd_5763_; lean_object* v_snd_5764_; lean_object* v_fst_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5877_; 
v_snd_5761_ = lean_ctor_get(v_b_5754_, 1);
lean_inc(v_snd_5761_);
v_snd_5762_ = lean_ctor_get(v_snd_5761_, 1);
lean_inc(v_snd_5762_);
v_snd_5763_ = lean_ctor_get(v_snd_5762_, 1);
lean_inc(v_snd_5763_);
v_snd_5764_ = lean_ctor_get(v_snd_5763_, 1);
lean_inc(v_snd_5764_);
v_fst_5765_ = lean_ctor_get(v_b_5754_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v_b_5754_);
if (v_isSharedCheck_5877_ == 0)
{
lean_object* v_unused_5878_; 
v_unused_5878_ = lean_ctor_get(v_b_5754_, 1);
lean_dec(v_unused_5878_);
v___x_5767_ = v_b_5754_;
v_isShared_5768_ = v_isSharedCheck_5877_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_fst_5765_);
lean_dec(v_b_5754_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5877_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v_fst_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5875_; 
v_fst_5769_ = lean_ctor_get(v_snd_5761_, 0);
v_isSharedCheck_5875_ = !lean_is_exclusive(v_snd_5761_);
if (v_isSharedCheck_5875_ == 0)
{
lean_object* v_unused_5876_; 
v_unused_5876_ = lean_ctor_get(v_snd_5761_, 1);
lean_dec(v_unused_5876_);
v___x_5771_ = v_snd_5761_;
v_isShared_5772_ = v_isSharedCheck_5875_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_fst_5769_);
lean_dec(v_snd_5761_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5875_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
lean_object* v_fst_5773_; lean_object* v___x_5775_; uint8_t v_isShared_5776_; uint8_t v_isSharedCheck_5873_; 
v_fst_5773_ = lean_ctor_get(v_snd_5762_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v_snd_5762_);
if (v_isSharedCheck_5873_ == 0)
{
lean_object* v_unused_5874_; 
v_unused_5874_ = lean_ctor_get(v_snd_5762_, 1);
lean_dec(v_unused_5874_);
v___x_5775_ = v_snd_5762_;
v_isShared_5776_ = v_isSharedCheck_5873_;
goto v_resetjp_5774_;
}
else
{
lean_inc(v_fst_5773_);
lean_dec(v_snd_5762_);
v___x_5775_ = lean_box(0);
v_isShared_5776_ = v_isSharedCheck_5873_;
goto v_resetjp_5774_;
}
v_resetjp_5774_:
{
lean_object* v_fst_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5871_; 
v_fst_5777_ = lean_ctor_get(v_snd_5763_, 0);
v_isSharedCheck_5871_ = !lean_is_exclusive(v_snd_5763_);
if (v_isSharedCheck_5871_ == 0)
{
lean_object* v_unused_5872_; 
v_unused_5872_ = lean_ctor_get(v_snd_5763_, 1);
lean_dec(v_unused_5872_);
v___x_5779_ = v_snd_5763_;
v_isShared_5780_ = v_isSharedCheck_5871_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_fst_5777_);
lean_dec(v_snd_5763_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5871_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v_array_5781_; lean_object* v_start_5782_; lean_object* v_stop_5783_; uint8_t v___x_5784_; 
v_array_5781_ = lean_ctor_get(v_snd_5764_, 0);
v_start_5782_ = lean_ctor_get(v_snd_5764_, 1);
v_stop_5783_ = lean_ctor_get(v_snd_5764_, 2);
v___x_5784_ = lean_nat_dec_lt(v_start_5782_, v_stop_5783_);
if (v___x_5784_ == 0)
{
lean_object* v___x_5786_; 
lean_dec(v_a_5753_);
if (v_isShared_5780_ == 0)
{
v___x_5786_ = v___x_5779_;
goto v_reusejp_5785_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v_fst_5777_);
lean_ctor_set(v_reuseFailAlloc_5796_, 1, v_snd_5764_);
v___x_5786_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5785_;
}
v_reusejp_5785_:
{
lean_object* v___x_5788_; 
if (v_isShared_5776_ == 0)
{
lean_ctor_set(v___x_5775_, 1, v___x_5786_);
v___x_5788_ = v___x_5775_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_fst_5773_);
lean_ctor_set(v_reuseFailAlloc_5795_, 1, v___x_5786_);
v___x_5788_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
lean_object* v___x_5790_; 
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 1, v___x_5788_);
v___x_5790_ = v___x_5771_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_fst_5769_);
lean_ctor_set(v_reuseFailAlloc_5794_, 1, v___x_5788_);
v___x_5790_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
lean_object* v___x_5792_; 
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5790_);
v___x_5792_ = v___x_5767_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v_fst_5765_);
lean_ctor_set(v_reuseFailAlloc_5793_, 1, v___x_5790_);
v___x_5792_ = v_reuseFailAlloc_5793_;
goto v_reusejp_5791_;
}
v_reusejp_5791_:
{
return v___x_5792_;
}
}
}
}
}
else
{
lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5867_; 
lean_inc(v_stop_5783_);
lean_inc(v_start_5782_);
lean_inc_ref(v_array_5781_);
v_isSharedCheck_5867_ = !lean_is_exclusive(v_snd_5764_);
if (v_isSharedCheck_5867_ == 0)
{
lean_object* v_unused_5868_; lean_object* v_unused_5869_; lean_object* v_unused_5870_; 
v_unused_5868_ = lean_ctor_get(v_snd_5764_, 2);
lean_dec(v_unused_5868_);
v_unused_5869_ = lean_ctor_get(v_snd_5764_, 1);
lean_dec(v_unused_5869_);
v_unused_5870_ = lean_ctor_get(v_snd_5764_, 0);
lean_dec(v_unused_5870_);
v___x_5798_ = v_snd_5764_;
v_isShared_5799_ = v_isSharedCheck_5867_;
goto v_resetjp_5797_;
}
else
{
lean_dec(v_snd_5764_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5867_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v_array_5800_; lean_object* v_start_5801_; lean_object* v_stop_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5807_; 
v_array_5800_ = lean_ctor_get(v_fst_5777_, 0);
v_start_5801_ = lean_ctor_get(v_fst_5777_, 1);
v_stop_5802_ = lean_ctor_get(v_fst_5777_, 2);
v___x_5803_ = lean_array_fget(v_array_5781_, v_start_5782_);
v___x_5804_ = lean_unsigned_to_nat(1u);
v___x_5805_ = lean_nat_add(v_start_5782_, v___x_5804_);
lean_dec(v_start_5782_);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 1, v___x_5805_);
v___x_5807_ = v___x_5798_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_array_5781_);
lean_ctor_set(v_reuseFailAlloc_5866_, 1, v___x_5805_);
lean_ctor_set(v_reuseFailAlloc_5866_, 2, v_stop_5783_);
v___x_5807_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
uint8_t v___x_5808_; 
v___x_5808_ = lean_nat_dec_lt(v_start_5801_, v_stop_5802_);
if (v___x_5808_ == 0)
{
lean_object* v___x_5810_; 
lean_dec(v___x_5803_);
lean_dec(v_a_5753_);
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 1, v___x_5807_);
v___x_5810_ = v___x_5779_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_fst_5777_);
lean_ctor_set(v_reuseFailAlloc_5820_, 1, v___x_5807_);
v___x_5810_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
lean_object* v___x_5812_; 
if (v_isShared_5776_ == 0)
{
lean_ctor_set(v___x_5775_, 1, v___x_5810_);
v___x_5812_ = v___x_5775_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_fst_5773_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v___x_5810_);
v___x_5812_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
lean_object* v___x_5814_; 
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 1, v___x_5812_);
v___x_5814_ = v___x_5771_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_fst_5769_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v___x_5812_);
v___x_5814_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
lean_object* v___x_5816_; 
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5814_);
v___x_5816_ = v___x_5767_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_fst_5765_);
lean_ctor_set(v_reuseFailAlloc_5817_, 1, v___x_5814_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
return v___x_5816_;
}
}
}
}
}
else
{
lean_object* v___x_5822_; uint8_t v_isShared_5823_; uint8_t v_isSharedCheck_5862_; 
lean_inc(v_stop_5802_);
lean_inc(v_start_5801_);
lean_inc_ref(v_array_5800_);
v_isSharedCheck_5862_ = !lean_is_exclusive(v_fst_5777_);
if (v_isSharedCheck_5862_ == 0)
{
lean_object* v_unused_5863_; lean_object* v_unused_5864_; lean_object* v_unused_5865_; 
v_unused_5863_ = lean_ctor_get(v_fst_5777_, 2);
lean_dec(v_unused_5863_);
v_unused_5864_ = lean_ctor_get(v_fst_5777_, 1);
lean_dec(v_unused_5864_);
v_unused_5865_ = lean_ctor_get(v_fst_5777_, 0);
lean_dec(v_unused_5865_);
v___x_5822_ = v_fst_5777_;
v_isShared_5823_ = v_isSharedCheck_5862_;
goto v_resetjp_5821_;
}
else
{
lean_dec(v_fst_5777_);
v___x_5822_ = lean_box(0);
v_isShared_5823_ = v_isSharedCheck_5862_;
goto v_resetjp_5821_;
}
v_resetjp_5821_:
{
lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5827_; 
v___x_5824_ = lean_array_fget(v_array_5800_, v_start_5801_);
v___x_5825_ = lean_nat_add(v_start_5801_, v___x_5804_);
lean_dec(v_start_5801_);
if (v_isShared_5823_ == 0)
{
lean_ctor_set(v___x_5822_, 1, v___x_5825_);
v___x_5827_ = v___x_5822_;
goto v_reusejp_5826_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_array_5800_);
lean_ctor_set(v_reuseFailAlloc_5861_, 1, v___x_5825_);
lean_ctor_set(v_reuseFailAlloc_5861_, 2, v_stop_5802_);
v___x_5827_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5826_;
}
v_reusejp_5826_:
{
uint8_t v___x_5828_; 
v___x_5828_ = lean_unbox(v___x_5824_);
lean_dec(v___x_5824_);
if (v___x_5828_ == 0)
{
lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5834_; 
v___x_5829_ = lean_array_get_size(v_fst_5773_);
v___x_5830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5829_);
v___x_5831_ = lean_array_push(v_fst_5765_, v___x_5830_);
v___x_5832_ = lean_array_push(v_fst_5773_, v___x_5803_);
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 1, v___x_5807_);
lean_ctor_set(v___x_5779_, 0, v___x_5827_);
v___x_5834_ = v___x_5779_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v___x_5827_);
lean_ctor_set(v_reuseFailAlloc_5844_, 1, v___x_5807_);
v___x_5834_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
lean_object* v___x_5836_; 
if (v_isShared_5776_ == 0)
{
lean_ctor_set(v___x_5775_, 1, v___x_5834_);
lean_ctor_set(v___x_5775_, 0, v___x_5832_);
v___x_5836_ = v___x_5775_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v___x_5832_);
lean_ctor_set(v_reuseFailAlloc_5843_, 1, v___x_5834_);
v___x_5836_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
lean_object* v___x_5838_; 
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 1, v___x_5836_);
v___x_5838_ = v___x_5771_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_fst_5769_);
lean_ctor_set(v_reuseFailAlloc_5842_, 1, v___x_5836_);
v___x_5838_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
lean_object* v___x_5840_; 
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5838_);
lean_ctor_set(v___x_5767_, 0, v___x_5831_);
v___x_5840_ = v___x_5767_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v___x_5831_);
lean_ctor_set(v_reuseFailAlloc_5841_, 1, v___x_5838_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
v_a_5756_ = v___x_5840_;
goto v___jp_5755_;
}
}
}
}
}
else
{
lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5850_; 
v___x_5845_ = lean_box(0);
v___x_5846_ = lean_array_push(v_fst_5765_, v___x_5845_);
v___x_5847_ = l_Lean_Expr_fvarId_x21(v___x_5803_);
lean_dec(v___x_5803_);
v___x_5848_ = lean_array_push(v_fst_5769_, v___x_5847_);
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 1, v___x_5807_);
lean_ctor_set(v___x_5779_, 0, v___x_5827_);
v___x_5850_ = v___x_5779_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v___x_5827_);
lean_ctor_set(v_reuseFailAlloc_5860_, 1, v___x_5807_);
v___x_5850_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
lean_object* v___x_5852_; 
if (v_isShared_5776_ == 0)
{
lean_ctor_set(v___x_5775_, 1, v___x_5850_);
v___x_5852_ = v___x_5775_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_fst_5773_);
lean_ctor_set(v_reuseFailAlloc_5859_, 1, v___x_5850_);
v___x_5852_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
lean_object* v___x_5854_; 
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 1, v___x_5852_);
lean_ctor_set(v___x_5771_, 0, v___x_5848_);
v___x_5854_ = v___x_5771_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v___x_5848_);
lean_ctor_set(v_reuseFailAlloc_5858_, 1, v___x_5852_);
v___x_5854_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
lean_object* v___x_5856_; 
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5854_);
lean_ctor_set(v___x_5767_, 0, v___x_5846_);
v___x_5856_ = v___x_5767_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v___x_5846_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v___x_5854_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
v_a_5756_ = v___x_5856_;
goto v___jp_5755_;
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
v___jp_5755_:
{
lean_object* v___x_5757_; lean_object* v___x_5758_; 
v___x_5757_ = lean_unsigned_to_nat(1u);
v___x_5758_ = lean_nat_add(v_a_5753_, v___x_5757_);
lean_dec(v_a_5753_);
v_a_5753_ = v___x_5758_;
v_b_5754_ = v_a_5756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5879_, lean_object* v_a_5880_, lean_object* v_b_5881_){
_start:
{
lean_object* v_res_5882_; 
v_res_5882_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5879_, v_a_5880_, v_b_5881_);
lean_dec(v_upperBound_5879_);
return v_res_5882_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5883_, size_t v_i_5884_, size_t v_stop_5885_){
_start:
{
uint8_t v___x_5886_; 
v___x_5886_ = lean_usize_dec_eq(v_i_5884_, v_stop_5885_);
if (v___x_5886_ == 0)
{
lean_object* v___x_5887_; uint8_t v___x_5888_; uint8_t v___x_5889_; 
v___x_5887_ = lean_array_uget_borrowed(v_as_5883_, v_i_5884_);
v___x_5888_ = l_Lean_Expr_isFVar(v___x_5887_);
v___x_5889_ = lean_bool_not(v___x_5888_);
if (v___x_5889_ == 0)
{
size_t v___x_5890_; size_t v___x_5891_; 
v___x_5890_ = ((size_t)1ULL);
v___x_5891_ = lean_usize_add(v_i_5884_, v___x_5890_);
v_i_5884_ = v___x_5891_;
goto _start;
}
else
{
return v___x_5889_;
}
}
else
{
uint8_t v___x_5893_; 
v___x_5893_ = 0;
return v___x_5893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5894_, lean_object* v_i_5895_, lean_object* v_stop_5896_){
_start:
{
size_t v_i_boxed_5897_; size_t v_stop_boxed_5898_; uint8_t v_res_5899_; lean_object* v_r_5900_; 
v_i_boxed_5897_ = lean_unbox_usize(v_i_5895_);
lean_dec(v_i_5895_);
v_stop_boxed_5898_ = lean_unbox_usize(v_stop_5896_);
lean_dec(v_stop_5896_);
v_res_5899_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5894_, v_i_boxed_5897_, v_stop_boxed_5898_);
lean_dec_ref(v_as_5894_);
v_r_5900_ = lean_box(v_res_5899_);
return v_r_5900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5901_, size_t v_sz_5902_, size_t v_i_5903_, lean_object* v_bs_5904_){
_start:
{
uint8_t v___x_5905_; 
v___x_5905_ = lean_usize_dec_lt(v_i_5903_, v_sz_5902_);
if (v___x_5905_ == 0)
{
return v_bs_5904_;
}
else
{
lean_object* v_v_5906_; lean_object* v___x_5907_; lean_object* v_bs_x27_5908_; lean_object* v___y_5910_; 
v_v_5906_ = lean_array_uget(v_bs_5904_, v_i_5903_);
v___x_5907_ = lean_unsigned_to_nat(0u);
v_bs_x27_5908_ = lean_array_uset(v_bs_5904_, v_i_5903_, v___x_5907_);
if (lean_obj_tag(v_v_5906_) == 0)
{
v___y_5910_ = v_v_5906_;
goto v___jp_5909_;
}
else
{
lean_object* v_val_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v_val_5915_ = lean_ctor_get(v_v_5906_, 0);
lean_inc(v_val_5915_);
lean_dec_ref_known(v_v_5906_, 1);
v___x_5916_ = lean_box(0);
v___x_5917_ = lean_array_get_borrowed(v___x_5916_, v___x_5901_, v_val_5915_);
lean_dec(v_val_5915_);
lean_inc(v___x_5917_);
v___y_5910_ = v___x_5917_;
goto v___jp_5909_;
}
v___jp_5909_:
{
size_t v___x_5911_; size_t v___x_5912_; lean_object* v___x_5913_; 
v___x_5911_ = ((size_t)1ULL);
v___x_5912_ = lean_usize_add(v_i_5903_, v___x_5911_);
v___x_5913_ = lean_array_uset(v_bs_x27_5908_, v_i_5903_, v___y_5910_);
v_i_5903_ = v___x_5912_;
v_bs_5904_ = v___x_5913_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5918_, lean_object* v_sz_5919_, lean_object* v_i_5920_, lean_object* v_bs_5921_){
_start:
{
size_t v_sz_boxed_5922_; size_t v_i_boxed_5923_; lean_object* v_res_5924_; 
v_sz_boxed_5922_ = lean_unbox_usize(v_sz_5919_);
lean_dec(v_sz_5919_);
v_i_boxed_5923_ = lean_unbox_usize(v_i_5920_);
lean_dec(v_i_5920_);
v_res_5924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5918_, v_sz_boxed_5922_, v_i_boxed_5923_, v_bs_5921_);
lean_dec_ref(v___x_5918_);
return v_res_5924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5925_, size_t v_sz_5926_, size_t v_i_5927_, lean_object* v_bs_5928_){
_start:
{
uint8_t v___x_5929_; 
v___x_5929_ = lean_usize_dec_lt(v_i_5927_, v_sz_5926_);
if (v___x_5929_ == 0)
{
return v_bs_5928_;
}
else
{
lean_object* v_v_5930_; lean_object* v___x_5931_; lean_object* v_bs_x27_5932_; size_t v_sz_5933_; size_t v___x_5934_; lean_object* v___x_5935_; size_t v___x_5936_; size_t v___x_5937_; lean_object* v___x_5938_; 
v_v_5930_ = lean_array_uget(v_bs_5928_, v_i_5927_);
v___x_5931_ = lean_unsigned_to_nat(0u);
v_bs_x27_5932_ = lean_array_uset(v_bs_5928_, v_i_5927_, v___x_5931_);
v_sz_5933_ = lean_array_size(v_v_5930_);
v___x_5934_ = ((size_t)0ULL);
v___x_5935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5925_, v_sz_5933_, v___x_5934_, v_v_5930_);
v___x_5936_ = ((size_t)1ULL);
v___x_5937_ = lean_usize_add(v_i_5927_, v___x_5936_);
v___x_5938_ = lean_array_uset(v_bs_x27_5932_, v_i_5927_, v___x_5935_);
v_i_5927_ = v___x_5937_;
v_bs_5928_ = v___x_5938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5940_, lean_object* v_sz_5941_, lean_object* v_i_5942_, lean_object* v_bs_5943_){
_start:
{
size_t v_sz_boxed_5944_; size_t v_i_boxed_5945_; lean_object* v_res_5946_; 
v_sz_boxed_5944_ = lean_unbox_usize(v_sz_5941_);
lean_dec(v_sz_5941_);
v_i_boxed_5945_ = lean_unbox_usize(v_i_5942_);
lean_dec(v_i_5942_);
v_res_5946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5940_, v_sz_boxed_5944_, v_i_boxed_5945_, v_bs_5943_);
lean_dec_ref(v___x_5940_);
return v_res_5946_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; 
v___x_5949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5950_ = lean_unsigned_to_nat(6u);
v___x_5951_ = lean_unsigned_to_nat(463u);
v___x_5952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5953_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5954_ = l_mkPanicMessageWithDecl(v___x_5953_, v___x_5952_, v___x_5951_, v___x_5950_, v___x_5949_);
return v___x_5954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5955_, uint8_t v___y_5956_, lean_object* v_as_5957_, size_t v_sz_5958_, size_t v_i_5959_, lean_object* v_b_5960_){
_start:
{
lean_object* v_a_5962_; uint8_t v___x_5966_; 
v___x_5966_ = lean_usize_dec_lt(v_i_5959_, v_sz_5958_);
if (v___x_5966_ == 0)
{
return v_b_5960_;
}
else
{
lean_object* v_a_5967_; lean_object* v___x_5968_; uint8_t v___x_5969_; 
v_a_5967_ = lean_array_uget_borrowed(v_as_5957_, v_i_5959_);
v___x_5968_ = lean_array_get_size(v___x_5955_);
v___x_5969_ = lean_nat_dec_lt(v_a_5967_, v___x_5968_);
if (v___x_5969_ == 0)
{
lean_object* v___x_5970_; lean_object* v___x_5971_; 
lean_dec_ref(v_b_5960_);
v___x_5970_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5971_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5970_);
if (lean_obj_tag(v___x_5971_) == 0)
{
lean_object* v_a_5972_; 
v_a_5972_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5972_);
lean_dec_ref_known(v___x_5971_, 1);
return v_a_5972_;
}
else
{
lean_object* v_a_5973_; 
v_a_5973_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5973_);
lean_dec_ref_known(v___x_5971_, 1);
v_a_5962_ = v_a_5973_;
goto v___jp_5961_;
}
}
else
{
lean_object* v___x_5974_; lean_object* v___x_5975_; 
v___x_5974_ = lean_box(0);
v___x_5975_ = lean_array_get_borrowed(v___x_5974_, v___x_5955_, v_a_5967_);
if (lean_obj_tag(v___x_5975_) == 1)
{
lean_object* v_val_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v_val_5976_ = lean_ctor_get(v___x_5975_, 0);
v___x_5977_ = lean_box(v___y_5956_);
v___x_5978_ = lean_array_set(v_b_5960_, v_val_5976_, v___x_5977_);
v_a_5962_ = v___x_5978_;
goto v___jp_5961_;
}
else
{
v_a_5962_ = v_b_5960_;
goto v___jp_5961_;
}
}
}
v___jp_5961_:
{
size_t v___x_5963_; size_t v___x_5964_; 
v___x_5963_ = ((size_t)1ULL);
v___x_5964_ = lean_usize_add(v_i_5959_, v___x_5963_);
v_i_5959_ = v___x_5964_;
v_b_5960_ = v_a_5962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5979_, lean_object* v___y_5980_, lean_object* v_as_5981_, lean_object* v_sz_5982_, lean_object* v_i_5983_, lean_object* v_b_5984_){
_start:
{
uint8_t v___y_8597__boxed_5985_; size_t v_sz_boxed_5986_; size_t v_i_boxed_5987_; lean_object* v_res_5988_; 
v___y_8597__boxed_5985_ = lean_unbox(v___y_5980_);
v_sz_boxed_5986_ = lean_unbox_usize(v_sz_5982_);
lean_dec(v_sz_5982_);
v_i_boxed_5987_ = lean_unbox_usize(v_i_5983_);
lean_dec(v_i_5983_);
v_res_5988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5979_, v___y_8597__boxed_5985_, v_as_5981_, v_sz_boxed_5986_, v_i_boxed_5987_, v_b_5984_);
lean_dec_ref(v_as_5981_);
lean_dec_ref(v___x_5979_);
return v_res_5988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5989_, uint8_t v___y_5990_, lean_object* v_a_5991_, lean_object* v_b_5992_){
_start:
{
uint8_t v___x_5993_; 
v___x_5993_ = lean_nat_dec_lt(v_a_5991_, v_upperBound_5989_);
if (v___x_5993_ == 0)
{
lean_dec(v_a_5991_);
return v_b_5992_;
}
else
{
lean_object* v_snd_5994_; lean_object* v_snd_5995_; lean_object* v_fst_5996_; lean_object* v___x_5998_; uint8_t v_isShared_5999_; uint8_t v_isSharedCheck_6062_; 
v_snd_5994_ = lean_ctor_get(v_b_5992_, 1);
lean_inc(v_snd_5994_);
v_snd_5995_ = lean_ctor_get(v_snd_5994_, 1);
lean_inc(v_snd_5995_);
v_fst_5996_ = lean_ctor_get(v_b_5992_, 0);
v_isSharedCheck_6062_ = !lean_is_exclusive(v_b_5992_);
if (v_isSharedCheck_6062_ == 0)
{
lean_object* v_unused_6063_; 
v_unused_6063_ = lean_ctor_get(v_b_5992_, 1);
lean_dec(v_unused_6063_);
v___x_5998_ = v_b_5992_;
v_isShared_5999_ = v_isSharedCheck_6062_;
goto v_resetjp_5997_;
}
else
{
lean_inc(v_fst_5996_);
lean_dec(v_b_5992_);
v___x_5998_ = lean_box(0);
v_isShared_5999_ = v_isSharedCheck_6062_;
goto v_resetjp_5997_;
}
v_resetjp_5997_:
{
lean_object* v_fst_6000_; lean_object* v___x_6002_; uint8_t v_isShared_6003_; uint8_t v_isSharedCheck_6060_; 
v_fst_6000_ = lean_ctor_get(v_snd_5994_, 0);
v_isSharedCheck_6060_ = !lean_is_exclusive(v_snd_5994_);
if (v_isSharedCheck_6060_ == 0)
{
lean_object* v_unused_6061_; 
v_unused_6061_ = lean_ctor_get(v_snd_5994_, 1);
lean_dec(v_unused_6061_);
v___x_6002_ = v_snd_5994_;
v_isShared_6003_ = v_isSharedCheck_6060_;
goto v_resetjp_6001_;
}
else
{
lean_inc(v_fst_6000_);
lean_dec(v_snd_5994_);
v___x_6002_ = lean_box(0);
v_isShared_6003_ = v_isSharedCheck_6060_;
goto v_resetjp_6001_;
}
v_resetjp_6001_:
{
lean_object* v_array_6004_; lean_object* v_start_6005_; lean_object* v_stop_6006_; uint8_t v___x_6007_; 
v_array_6004_ = lean_ctor_get(v_snd_5995_, 0);
v_start_6005_ = lean_ctor_get(v_snd_5995_, 1);
v_stop_6006_ = lean_ctor_get(v_snd_5995_, 2);
v___x_6007_ = lean_nat_dec_lt(v_start_6005_, v_stop_6006_);
if (v___x_6007_ == 0)
{
lean_object* v___x_6009_; 
lean_dec(v_a_5991_);
if (v_isShared_6003_ == 0)
{
v___x_6009_ = v___x_6002_;
goto v_reusejp_6008_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_fst_6000_);
lean_ctor_set(v_reuseFailAlloc_6013_, 1, v_snd_5995_);
v___x_6009_ = v_reuseFailAlloc_6013_;
goto v_reusejp_6008_;
}
v_reusejp_6008_:
{
lean_object* v___x_6011_; 
if (v_isShared_5999_ == 0)
{
lean_ctor_set(v___x_5998_, 1, v___x_6009_);
v___x_6011_ = v___x_5998_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v_fst_5996_);
lean_ctor_set(v_reuseFailAlloc_6012_, 1, v___x_6009_);
v___x_6011_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
return v___x_6011_;
}
}
}
else
{
lean_object* v___x_6015_; uint8_t v_isShared_6016_; uint8_t v_isSharedCheck_6056_; 
lean_inc(v_stop_6006_);
lean_inc(v_start_6005_);
lean_inc_ref(v_array_6004_);
v_isSharedCheck_6056_ = !lean_is_exclusive(v_snd_5995_);
if (v_isSharedCheck_6056_ == 0)
{
lean_object* v_unused_6057_; lean_object* v_unused_6058_; lean_object* v_unused_6059_; 
v_unused_6057_ = lean_ctor_get(v_snd_5995_, 2);
lean_dec(v_unused_6057_);
v_unused_6058_ = lean_ctor_get(v_snd_5995_, 1);
lean_dec(v_unused_6058_);
v_unused_6059_ = lean_ctor_get(v_snd_5995_, 0);
lean_dec(v_unused_6059_);
v___x_6015_ = v_snd_5995_;
v_isShared_6016_ = v_isSharedCheck_6056_;
goto v_resetjp_6014_;
}
else
{
lean_dec(v_snd_5995_);
v___x_6015_ = lean_box(0);
v_isShared_6016_ = v_isSharedCheck_6056_;
goto v_resetjp_6014_;
}
v_resetjp_6014_:
{
lean_object* v_array_6017_; lean_object* v_start_6018_; lean_object* v_stop_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6024_; 
v_array_6017_ = lean_ctor_get(v_fst_6000_, 0);
v_start_6018_ = lean_ctor_get(v_fst_6000_, 1);
v_stop_6019_ = lean_ctor_get(v_fst_6000_, 2);
v___x_6020_ = lean_array_fget(v_array_6004_, v_start_6005_);
v___x_6021_ = lean_unsigned_to_nat(1u);
v___x_6022_ = lean_nat_add(v_start_6005_, v___x_6021_);
lean_dec(v_start_6005_);
if (v_isShared_6016_ == 0)
{
lean_ctor_set(v___x_6015_, 1, v___x_6022_);
v___x_6024_ = v___x_6015_;
goto v_reusejp_6023_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_array_6004_);
lean_ctor_set(v_reuseFailAlloc_6055_, 1, v___x_6022_);
lean_ctor_set(v_reuseFailAlloc_6055_, 2, v_stop_6006_);
v___x_6024_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6023_;
}
v_reusejp_6023_:
{
uint8_t v___x_6025_; 
v___x_6025_ = lean_nat_dec_lt(v_start_6018_, v_stop_6019_);
if (v___x_6025_ == 0)
{
lean_object* v___x_6027_; 
lean_dec(v___x_6020_);
lean_dec(v_a_5991_);
if (v_isShared_6003_ == 0)
{
lean_ctor_set(v___x_6002_, 1, v___x_6024_);
v___x_6027_ = v___x_6002_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_fst_6000_);
lean_ctor_set(v_reuseFailAlloc_6031_, 1, v___x_6024_);
v___x_6027_ = v_reuseFailAlloc_6031_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
lean_object* v___x_6029_; 
if (v_isShared_5999_ == 0)
{
lean_ctor_set(v___x_5998_, 1, v___x_6027_);
v___x_6029_ = v___x_5998_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6030_; 
v_reuseFailAlloc_6030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_fst_5996_);
lean_ctor_set(v_reuseFailAlloc_6030_, 1, v___x_6027_);
v___x_6029_ = v_reuseFailAlloc_6030_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
return v___x_6029_;
}
}
}
else
{
lean_object* v___x_6033_; uint8_t v_isShared_6034_; uint8_t v_isSharedCheck_6051_; 
lean_inc(v_stop_6019_);
lean_inc(v_start_6018_);
lean_inc_ref(v_array_6017_);
v_isSharedCheck_6051_ = !lean_is_exclusive(v_fst_6000_);
if (v_isSharedCheck_6051_ == 0)
{
lean_object* v_unused_6052_; lean_object* v_unused_6053_; lean_object* v_unused_6054_; 
v_unused_6052_ = lean_ctor_get(v_fst_6000_, 2);
lean_dec(v_unused_6052_);
v_unused_6053_ = lean_ctor_get(v_fst_6000_, 1);
lean_dec(v_unused_6053_);
v_unused_6054_ = lean_ctor_get(v_fst_6000_, 0);
lean_dec(v_unused_6054_);
v___x_6033_ = v_fst_6000_;
v_isShared_6034_ = v_isSharedCheck_6051_;
goto v_resetjp_6032_;
}
else
{
lean_dec(v_fst_6000_);
v___x_6033_ = lean_box(0);
v_isShared_6034_ = v_isSharedCheck_6051_;
goto v_resetjp_6032_;
}
v_resetjp_6032_:
{
lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6038_; 
v___x_6035_ = lean_array_fget(v_array_6017_, v_start_6018_);
v___x_6036_ = lean_nat_add(v_start_6018_, v___x_6021_);
lean_dec(v_start_6018_);
if (v_isShared_6034_ == 0)
{
lean_ctor_set(v___x_6033_, 1, v___x_6036_);
v___x_6038_ = v___x_6033_;
goto v_reusejp_6037_;
}
else
{
lean_object* v_reuseFailAlloc_6050_; 
v_reuseFailAlloc_6050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6050_, 0, v_array_6017_);
lean_ctor_set(v_reuseFailAlloc_6050_, 1, v___x_6036_);
lean_ctor_set(v_reuseFailAlloc_6050_, 2, v_stop_6019_);
v___x_6038_ = v_reuseFailAlloc_6050_;
goto v_reusejp_6037_;
}
v_reusejp_6037_:
{
size_t v_sz_6039_; size_t v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6043_; 
v_sz_6039_ = lean_array_size(v___x_6035_);
v___x_6040_ = ((size_t)0ULL);
v___x_6041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_6020_, v___y_5990_, v___x_6035_, v_sz_6039_, v___x_6040_, v_fst_5996_);
lean_dec(v___x_6035_);
lean_dec(v___x_6020_);
if (v_isShared_6003_ == 0)
{
lean_ctor_set(v___x_6002_, 1, v___x_6024_);
lean_ctor_set(v___x_6002_, 0, v___x_6038_);
v___x_6043_ = v___x_6002_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6049_; 
v_reuseFailAlloc_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6049_, 0, v___x_6038_);
lean_ctor_set(v_reuseFailAlloc_6049_, 1, v___x_6024_);
v___x_6043_ = v_reuseFailAlloc_6049_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
lean_object* v___x_6045_; 
if (v_isShared_5999_ == 0)
{
lean_ctor_set(v___x_5998_, 1, v___x_6043_);
lean_ctor_set(v___x_5998_, 0, v___x_6041_);
v___x_6045_ = v___x_5998_;
goto v_reusejp_6044_;
}
else
{
lean_object* v_reuseFailAlloc_6048_; 
v_reuseFailAlloc_6048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6041_);
lean_ctor_set(v_reuseFailAlloc_6048_, 1, v___x_6043_);
v___x_6045_ = v_reuseFailAlloc_6048_;
goto v_reusejp_6044_;
}
v_reusejp_6044_:
{
lean_object* v___x_6046_; 
v___x_6046_ = lean_nat_add(v_a_5991_, v___x_6021_);
lean_dec(v_a_5991_);
v_a_5991_ = v___x_6046_;
v_b_5992_ = v___x_6045_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6064_, lean_object* v___y_6065_, lean_object* v_a_6066_, lean_object* v_b_6067_){
_start:
{
uint8_t v___y_8645__boxed_6068_; lean_object* v_res_6069_; 
v___y_8645__boxed_6068_ = lean_unbox(v___y_6065_);
v_res_6069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6064_, v___y_8645__boxed_6068_, v_a_6066_, v_b_6067_);
lean_dec(v_upperBound_6064_);
return v_res_6069_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6071_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6072_ = lean_unsigned_to_nat(2u);
v___x_6073_ = lean_unsigned_to_nat(456u);
v___x_6074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6075_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6076_ = l_mkPanicMessageWithDecl(v___x_6075_, v___x_6074_, v___x_6073_, v___x_6072_, v___x_6071_);
return v___x_6076_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; 
v___x_6078_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6079_ = lean_unsigned_to_nat(2u);
v___x_6080_ = lean_unsigned_to_nat(457u);
v___x_6081_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6082_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6083_ = l_mkPanicMessageWithDecl(v___x_6082_, v___x_6081_, v___x_6080_, v___x_6079_, v___x_6078_);
return v___x_6083_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; 
v___x_6085_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6086_ = lean_unsigned_to_nat(2u);
v___x_6087_ = lean_unsigned_to_nat(458u);
v___x_6088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6089_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6090_ = l_mkPanicMessageWithDecl(v___x_6089_, v___x_6088_, v___x_6087_, v___x_6086_, v___x_6085_);
return v___x_6090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6091_, lean_object* v_xs_6092_, lean_object* v_toErase_6093_){
_start:
{
lean_object* v___x_6094_; lean_object* v___x_6095_; uint8_t v___y_6097_; uint8_t v___x_6182_; 
v___x_6094_ = lean_unsigned_to_nat(0u);
v___x_6095_ = lean_array_get_size(v_xs_6092_);
v___x_6182_ = lean_nat_dec_lt(v___x_6094_, v___x_6095_);
if (v___x_6182_ == 0)
{
uint8_t v___x_6183_; 
v___x_6183_ = lean_bool_not(v___x_6182_);
v___y_6097_ = v___x_6183_;
goto v___jp_6096_;
}
else
{
if (v___x_6182_ == 0)
{
uint8_t v___x_6184_; 
v___x_6184_ = lean_bool_not(v___x_6182_);
v___y_6097_ = v___x_6184_;
goto v___jp_6096_;
}
else
{
size_t v___x_6185_; size_t v___x_6186_; uint8_t v___x_6187_; uint8_t v___x_6188_; 
v___x_6185_ = ((size_t)0ULL);
v___x_6186_ = lean_usize_of_nat(v___x_6095_);
v___x_6187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6092_, v___x_6185_, v___x_6186_);
v___x_6188_ = lean_bool_not(v___x_6187_);
v___y_6097_ = v___x_6188_;
goto v___jp_6096_;
}
}
v___jp_6096_:
{
if (v___y_6097_ == 0)
{
lean_object* v___x_6098_; lean_object* v___x_6099_; 
lean_dec_ref(v_toErase_6093_);
lean_dec_ref(v_xs_6092_);
lean_dec_ref(v_fixedParamPerms_6091_);
v___x_6098_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6099_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6098_);
return v___x_6099_;
}
else
{
lean_object* v_numFixed_6100_; lean_object* v_perms_6101_; lean_object* v_revDeps_6102_; uint8_t v___x_6103_; 
v_numFixed_6100_ = lean_ctor_get(v_fixedParamPerms_6091_, 0);
v_perms_6101_ = lean_ctor_get(v_fixedParamPerms_6091_, 1);
lean_inc_ref(v_perms_6101_);
v_revDeps_6102_ = lean_ctor_get(v_fixedParamPerms_6091_, 2);
lean_inc_ref(v_revDeps_6102_);
v___x_6103_ = lean_nat_dec_eq(v_numFixed_6100_, v___x_6095_);
if (v___x_6103_ == 0)
{
lean_object* v___x_6104_; lean_object* v___x_6105_; 
lean_dec_ref(v_revDeps_6102_);
lean_dec_ref(v_perms_6101_);
lean_dec_ref(v_toErase_6093_);
lean_dec_ref(v_xs_6092_);
lean_dec_ref(v_fixedParamPerms_6091_);
v___x_6104_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6105_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6104_);
return v___x_6105_;
}
else
{
lean_object* v___x_6106_; lean_object* v___x_6107_; uint8_t v___x_6108_; 
v___x_6106_ = lean_array_get_size(v_toErase_6093_);
v___x_6107_ = lean_array_get_size(v_perms_6101_);
v___x_6108_ = lean_nat_dec_eq(v___x_6106_, v___x_6107_);
if (v___x_6108_ == 0)
{
lean_object* v___x_6109_; lean_object* v___x_6110_; 
lean_dec_ref(v_revDeps_6102_);
lean_dec_ref(v_perms_6101_);
lean_dec_ref(v_toErase_6093_);
lean_dec_ref(v_xs_6092_);
lean_dec_ref(v_fixedParamPerms_6091_);
v___x_6109_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6110_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6109_);
return v___x_6110_;
}
else
{
uint8_t v_changed_6111_; lean_object* v___x_6112_; lean_object* v_mask_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v_fst_6119_; lean_object* v___x_6121_; uint8_t v_isShared_6122_; uint8_t v_isSharedCheck_6180_; 
v_changed_6111_ = 0;
v___x_6112_ = lean_box(v_changed_6111_);
lean_inc(v_numFixed_6100_);
v_mask_6113_ = lean_mk_array(v_numFixed_6100_, v___x_6112_);
v___x_6114_ = l_Array_toSubarray___redArg(v_toErase_6093_, v___x_6094_, v___x_6106_);
lean_inc_ref(v_perms_6101_);
v___x_6115_ = l_Array_toSubarray___redArg(v_perms_6101_, v___x_6094_, v___x_6107_);
v___x_6116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6114_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6117_, 0, v_mask_6113_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v___x_6118_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6106_, v___y_6097_, v___x_6094_, v___x_6117_);
v_fst_6119_ = lean_ctor_get(v___x_6118_, 0);
v_isSharedCheck_6180_ = !lean_is_exclusive(v___x_6118_);
if (v_isSharedCheck_6180_ == 0)
{
lean_object* v_unused_6181_; 
v_unused_6181_ = lean_ctor_get(v___x_6118_, 1);
lean_dec(v_unused_6181_);
v___x_6121_ = v___x_6118_;
v_isShared_6122_ = v_isSharedCheck_6180_;
goto v_resetjp_6120_;
}
else
{
lean_inc(v_fst_6119_);
lean_dec(v___x_6118_);
v___x_6121_ = lean_box(0);
v_isShared_6122_ = v_isSharedCheck_6180_;
goto v_resetjp_6120_;
}
v_resetjp_6120_:
{
lean_object* v___x_6123_; lean_object* v___x_6125_; 
v___x_6123_ = lean_box(v___y_6097_);
if (v_isShared_6122_ == 0)
{
lean_ctor_set(v___x_6121_, 1, v___x_6123_);
v___x_6125_ = v___x_6121_;
goto v_reusejp_6124_;
}
else
{
lean_object* v_reuseFailAlloc_6179_; 
v_reuseFailAlloc_6179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6179_, 0, v_fst_6119_);
lean_ctor_set(v_reuseFailAlloc_6179_, 1, v___x_6123_);
v___x_6125_ = v_reuseFailAlloc_6179_;
goto v_reusejp_6124_;
}
v_reusejp_6124_:
{
lean_object* v___x_6126_; lean_object* v___x_6128_; uint8_t v_isShared_6129_; uint8_t v_isSharedCheck_6175_; 
v___x_6126_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6107_, v_perms_6101_, v___y_6097_, v_fixedParamPerms_6091_, v___x_6125_);
v_isSharedCheck_6175_ = !lean_is_exclusive(v_fixedParamPerms_6091_);
if (v_isSharedCheck_6175_ == 0)
{
lean_object* v_unused_6176_; lean_object* v_unused_6177_; lean_object* v_unused_6178_; 
v_unused_6176_ = lean_ctor_get(v_fixedParamPerms_6091_, 2);
lean_dec(v_unused_6176_);
v_unused_6177_ = lean_ctor_get(v_fixedParamPerms_6091_, 1);
lean_dec(v_unused_6177_);
v_unused_6178_ = lean_ctor_get(v_fixedParamPerms_6091_, 0);
lean_dec(v_unused_6178_);
v___x_6128_ = v_fixedParamPerms_6091_;
v_isShared_6129_ = v_isSharedCheck_6175_;
goto v_resetjp_6127_;
}
else
{
lean_dec(v_fixedParamPerms_6091_);
v___x_6128_ = lean_box(0);
v_isShared_6129_ = v_isSharedCheck_6175_;
goto v_resetjp_6127_;
}
v_resetjp_6127_:
{
lean_object* v_fst_6130_; lean_object* v___x_6132_; uint8_t v_isShared_6133_; uint8_t v_isSharedCheck_6173_; 
v_fst_6130_ = lean_ctor_get(v___x_6126_, 0);
v_isSharedCheck_6173_ = !lean_is_exclusive(v___x_6126_);
if (v_isSharedCheck_6173_ == 0)
{
lean_object* v_unused_6174_; 
v_unused_6174_ = lean_ctor_get(v___x_6126_, 1);
lean_dec(v_unused_6174_);
v___x_6132_ = v___x_6126_;
v_isShared_6133_ = v_isSharedCheck_6173_;
goto v_resetjp_6131_;
}
else
{
lean_inc(v_fst_6130_);
lean_dec(v___x_6126_);
v___x_6132_ = lean_box(0);
v_isShared_6133_ = v_isSharedCheck_6173_;
goto v_resetjp_6131_;
}
v_resetjp_6131_:
{
lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6139_; 
v___x_6134_ = lean_array_get_size(v_fst_6130_);
v___x_6135_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6136_ = l_Array_toSubarray___redArg(v_fst_6130_, v___x_6094_, v___x_6134_);
v___x_6137_ = l_Array_toSubarray___redArg(v_xs_6092_, v___x_6094_, v___x_6095_);
if (v_isShared_6133_ == 0)
{
lean_ctor_set(v___x_6132_, 1, v___x_6137_);
lean_ctor_set(v___x_6132_, 0, v___x_6136_);
v___x_6139_ = v___x_6132_;
goto v_reusejp_6138_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v___x_6136_);
lean_ctor_set(v_reuseFailAlloc_6172_, 1, v___x_6137_);
v___x_6139_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6138_;
}
v_reusejp_6138_:
{
lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v_snd_6144_; lean_object* v_snd_6145_; lean_object* v_fst_6146_; lean_object* v_fst_6147_; lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6170_; 
v___x_6140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6135_);
lean_ctor_set(v___x_6140_, 1, v___x_6139_);
v___x_6141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6141_, 0, v___x_6135_);
lean_ctor_set(v___x_6141_, 1, v___x_6140_);
v___x_6142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6135_);
lean_ctor_set(v___x_6142_, 1, v___x_6141_);
v___x_6143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6134_, v___x_6094_, v___x_6142_);
v_snd_6144_ = lean_ctor_get(v___x_6143_, 1);
lean_inc(v_snd_6144_);
v_snd_6145_ = lean_ctor_get(v_snd_6144_, 1);
lean_inc(v_snd_6145_);
v_fst_6146_ = lean_ctor_get(v___x_6143_, 0);
lean_inc(v_fst_6146_);
lean_dec_ref(v___x_6143_);
v_fst_6147_ = lean_ctor_get(v_snd_6144_, 0);
v_isSharedCheck_6170_ = !lean_is_exclusive(v_snd_6144_);
if (v_isSharedCheck_6170_ == 0)
{
lean_object* v_unused_6171_; 
v_unused_6171_ = lean_ctor_get(v_snd_6144_, 1);
lean_dec(v_unused_6171_);
v___x_6149_ = v_snd_6144_;
v_isShared_6150_ = v_isSharedCheck_6170_;
goto v_resetjp_6148_;
}
else
{
lean_inc(v_fst_6147_);
lean_dec(v_snd_6144_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6170_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
lean_object* v_fst_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6168_; 
v_fst_6151_ = lean_ctor_get(v_snd_6145_, 0);
v_isSharedCheck_6168_ = !lean_is_exclusive(v_snd_6145_);
if (v_isSharedCheck_6168_ == 0)
{
lean_object* v_unused_6169_; 
v_unused_6169_ = lean_ctor_get(v_snd_6145_, 1);
lean_dec(v_unused_6169_);
v___x_6153_ = v_snd_6145_;
v_isShared_6154_ = v_isSharedCheck_6168_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_fst_6151_);
lean_dec(v_snd_6145_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6168_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
lean_object* v___x_6155_; size_t v_sz_6156_; size_t v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6160_; 
v___x_6155_ = lean_array_get_size(v_fst_6151_);
v_sz_6156_ = lean_array_size(v_perms_6101_);
v___x_6157_ = ((size_t)0ULL);
v___x_6158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6146_, v_sz_6156_, v___x_6157_, v_perms_6101_);
lean_dec(v_fst_6146_);
if (v_isShared_6129_ == 0)
{
lean_ctor_set(v___x_6128_, 1, v___x_6158_);
lean_ctor_set(v___x_6128_, 0, v___x_6155_);
v___x_6160_ = v___x_6128_;
goto v_reusejp_6159_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v___x_6155_);
lean_ctor_set(v_reuseFailAlloc_6167_, 1, v___x_6158_);
lean_ctor_set(v_reuseFailAlloc_6167_, 2, v_revDeps_6102_);
v___x_6160_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6159_;
}
v_reusejp_6159_:
{
lean_object* v___x_6162_; 
if (v_isShared_6154_ == 0)
{
lean_ctor_set(v___x_6153_, 1, v_fst_6147_);
v___x_6162_ = v___x_6153_;
goto v_reusejp_6161_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_fst_6151_);
lean_ctor_set(v_reuseFailAlloc_6166_, 1, v_fst_6147_);
v___x_6162_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6161_;
}
v_reusejp_6161_:
{
lean_object* v___x_6164_; 
if (v_isShared_6150_ == 0)
{
lean_ctor_set(v___x_6149_, 1, v___x_6162_);
lean_ctor_set(v___x_6149_, 0, v___x_6160_);
v___x_6164_ = v___x_6149_;
goto v_reusejp_6163_;
}
else
{
lean_object* v_reuseFailAlloc_6165_; 
v_reuseFailAlloc_6165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6165_, 0, v___x_6160_);
lean_ctor_set(v_reuseFailAlloc_6165_, 1, v___x_6162_);
v___x_6164_ = v_reuseFailAlloc_6165_;
goto v_reusejp_6163_;
}
v_reusejp_6163_:
{
return v___x_6164_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6189_, lean_object* v___x_6190_, uint8_t v___y_6191_, lean_object* v_fixedParamPerms_6192_, lean_object* v_next_6193_, lean_object* v_inst_6194_, lean_object* v_R_6195_, lean_object* v_a_6196_, lean_object* v_b_6197_, lean_object* v_c_6198_){
_start:
{
lean_object* v___x_6199_; 
v___x_6199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6189_, v___x_6190_, v___y_6191_, v_fixedParamPerms_6192_, v_next_6193_, v_a_6196_, v_b_6197_);
return v___x_6199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6200_, lean_object* v___x_6201_, lean_object* v___y_6202_, lean_object* v_fixedParamPerms_6203_, lean_object* v_next_6204_, lean_object* v_inst_6205_, lean_object* v_R_6206_, lean_object* v_a_6207_, lean_object* v_b_6208_, lean_object* v_c_6209_){
_start:
{
uint8_t v___y_9007__boxed_6210_; lean_object* v_res_6211_; 
v___y_9007__boxed_6210_ = lean_unbox(v___y_6202_);
v_res_6211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6200_, v___x_6201_, v___y_9007__boxed_6210_, v_fixedParamPerms_6203_, v_next_6204_, v_inst_6205_, v_R_6206_, v_a_6207_, v_b_6208_, v_c_6209_);
lean_dec(v_a_6207_);
lean_dec(v_next_6204_);
lean_dec_ref(v_fixedParamPerms_6203_);
lean_dec_ref(v___x_6201_);
lean_dec(v_upperBound_6200_);
return v_res_6211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6212_, lean_object* v___x_6213_, uint8_t v___y_6214_, lean_object* v_fixedParamPerms_6215_, lean_object* v_inst_6216_, lean_object* v_R_6217_, lean_object* v_a_6218_, lean_object* v_b_6219_, lean_object* v_c_6220_){
_start:
{
lean_object* v___x_6221_; 
v___x_6221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6212_, v___x_6213_, v___y_6214_, v_fixedParamPerms_6215_, v_a_6218_, v_b_6219_);
return v___x_6221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6222_, lean_object* v___x_6223_, lean_object* v___y_6224_, lean_object* v_fixedParamPerms_6225_, lean_object* v_inst_6226_, lean_object* v_R_6227_, lean_object* v_a_6228_, lean_object* v_b_6229_, lean_object* v_c_6230_){
_start:
{
uint8_t v___y_9021__boxed_6231_; lean_object* v_res_6232_; 
v___y_9021__boxed_6231_ = lean_unbox(v___y_6224_);
v_res_6232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6222_, v___x_6223_, v___y_9021__boxed_6231_, v_fixedParamPerms_6225_, v_inst_6226_, v_R_6227_, v_a_6228_, v_b_6229_, v_c_6230_);
lean_dec_ref(v_fixedParamPerms_6225_);
lean_dec_ref(v___x_6223_);
lean_dec(v_upperBound_6222_);
return v_res_6232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6233_, lean_object* v___x_6234_, uint8_t v___y_6235_, lean_object* v_fixedParamPerms_6236_, lean_object* v_inst_6237_, lean_object* v_a_6238_){
_start:
{
lean_object* v___x_6239_; 
v___x_6239_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6233_, v___x_6234_, v___y_6235_, v_fixedParamPerms_6236_, v_a_6238_);
return v___x_6239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6240_, lean_object* v___x_6241_, lean_object* v___y_6242_, lean_object* v_fixedParamPerms_6243_, lean_object* v_inst_6244_, lean_object* v_a_6245_){
_start:
{
uint8_t v___y_9035__boxed_6246_; lean_object* v_res_6247_; 
v___y_9035__boxed_6246_ = lean_unbox(v___y_6242_);
v_res_6247_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6240_, v___x_6241_, v___y_9035__boxed_6246_, v_fixedParamPerms_6243_, v_inst_6244_, v_a_6245_);
lean_dec_ref(v_fixedParamPerms_6243_);
lean_dec_ref(v___x_6241_);
lean_dec(v___x_6240_);
return v_res_6247_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6248_, lean_object* v_inst_6249_, lean_object* v_R_6250_, lean_object* v_a_6251_, lean_object* v_b_6252_, lean_object* v_c_6253_){
_start:
{
lean_object* v___x_6254_; 
v___x_6254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6248_, v_a_6251_, v_b_6252_);
return v___x_6254_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6255_, lean_object* v_inst_6256_, lean_object* v_R_6257_, lean_object* v_a_6258_, lean_object* v_b_6259_, lean_object* v_c_6260_){
_start:
{
lean_object* v_res_6261_; 
v_res_6261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6255_, v_inst_6256_, v_R_6257_, v_a_6258_, v_b_6259_, v_c_6260_);
lean_dec(v_upperBound_6255_);
return v_res_6261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6262_, uint8_t v___y_6263_, lean_object* v_inst_6264_, lean_object* v_R_6265_, lean_object* v_a_6266_, lean_object* v_b_6267_, lean_object* v_c_6268_){
_start:
{
lean_object* v___x_6269_; 
v___x_6269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6262_, v___y_6263_, v_a_6266_, v_b_6267_);
return v___x_6269_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6270_, lean_object* v___y_6271_, lean_object* v_inst_6272_, lean_object* v_R_6273_, lean_object* v_a_6274_, lean_object* v_b_6275_, lean_object* v_c_6276_){
_start:
{
uint8_t v___y_9056__boxed_6277_; lean_object* v_res_6278_; 
v___y_9056__boxed_6277_ = lean_unbox(v___y_6271_);
v_res_6278_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6270_, v___y_9056__boxed_6277_, v_inst_6272_, v_R_6273_, v_a_6274_, v_b_6275_, v_c_6276_);
lean_dec(v_upperBound_6270_);
return v_res_6278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object* v_upperBound_6279_, lean_object* v___x_6280_, lean_object* v_fixedParamPerms_6281_, lean_object* v_next_6282_, uint8_t v___y_6283_, lean_object* v_inst_6284_, lean_object* v_R_6285_, lean_object* v_a_6286_, lean_object* v_b_6287_, lean_object* v_c_6288_){
_start:
{
lean_object* v___x_6289_; 
v___x_6289_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_6279_, v___x_6280_, v_fixedParamPerms_6281_, v_next_6282_, v___y_6283_, v_a_6286_, v_b_6287_);
return v___x_6289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object* v_upperBound_6290_, lean_object* v___x_6291_, lean_object* v_fixedParamPerms_6292_, lean_object* v_next_6293_, lean_object* v___y_6294_, lean_object* v_inst_6295_, lean_object* v_R_6296_, lean_object* v_a_6297_, lean_object* v_b_6298_, lean_object* v_c_6299_){
_start:
{
uint8_t v___y_9068__boxed_6300_; lean_object* v_res_6301_; 
v___y_9068__boxed_6300_ = lean_unbox(v___y_6294_);
v_res_6301_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(v_upperBound_6290_, v___x_6291_, v_fixedParamPerms_6292_, v_next_6293_, v___y_9068__boxed_6300_, v_inst_6295_, v_R_6296_, v_a_6297_, v_b_6298_, v_c_6299_);
lean_dec(v_next_6293_);
lean_dec_ref(v_fixedParamPerms_6292_);
lean_dec_ref(v___x_6291_);
lean_dec(v_upperBound_6290_);
return v_res_6301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6359_; uint8_t v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; 
v___x_6359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6360_ = 0;
v___x_6361_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6362_ = l_Lean_registerTraceClass(v___x_6359_, v___x_6360_, v___x_6361_);
return v___x_6362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6363_){
_start:
{
lean_object* v_res_6364_; 
v_res_6364_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6364_;
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
