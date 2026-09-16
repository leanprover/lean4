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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_FixedParams_Info_setVarying___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "_private.Lean.Elab.PreDefinition.FixedParams.0.Lean.Elab.FixedParamPerm.buildArgs.go"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "FixedParams.buildArgs: too few fixed args"};
static const lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "FixedParams.buildArgs: too few varying args"};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0(void){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Array_instInhabited(lean_box(0));
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(lean_object* v_upperBound_140_, lean_object* v_next_141_, lean_object* v_funIdx_142_, lean_object* v_paramIdx_143_, lean_object* v_a_144_, lean_object* v_b_145_){
_start:
{
lean_object* v_a_147_; uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_lt(v_a_144_, v_upperBound_140_);
if (v___x_151_ == 0)
{
lean_dec(v_a_144_);
lean_dec(v_paramIdx_143_);
return v_b_145_;
}
else
{
lean_object* v_graph_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_graph_152_ = lean_ctor_get(v_b_145_, 0);
v___x_153_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_154_ = lean_box(0);
v___x_155_ = lean_array_get_borrowed(v___x_153_, v_graph_152_, v_next_141_);
v___x_156_ = lean_array_get(v___x_154_, v___x_155_, v_a_144_);
if (lean_obj_tag(v___x_156_) == 1)
{
lean_object* v_val_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_168_; 
v_val_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_168_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_168_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_val_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_168_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_161_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_162_ = lean_array_get(v___x_154_, v_val_157_, v_funIdx_142_);
lean_dec(v_val_157_);
lean_inc(v_paramIdx_143_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v_paramIdx_143_);
v___x_164_ = v___x_159_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_paramIdx_143_);
v___x_164_ = v_reuseFailAlloc_167_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
uint8_t v___x_165_; 
v___x_165_ = l_Option_instDecidableEq___redArg(v___x_161_, v___x_162_, v___x_164_);
if (v___x_165_ == 0)
{
v_a_147_ = v_b_145_;
goto v___jp_146_;
}
else
{
lean_object* v___x_166_; 
lean_inc(v_a_144_);
v___x_166_ = l_Lean_Elab_FixedParams_Info_setVarying(v_next_141_, v_a_144_, v_b_145_);
v_a_147_ = v___x_166_;
goto v___jp_146_;
}
}
}
}
else
{
lean_dec(v___x_156_);
v_a_147_ = v_b_145_;
goto v___jp_146_;
}
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_a_144_, v___x_148_);
lean_dec(v_a_144_);
v_a_144_ = v___x_149_;
v_b_145_ = v_a_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(lean_object* v_upperBound_169_, lean_object* v_funIdx_170_, lean_object* v_paramIdx_171_, lean_object* v_a_172_, lean_object* v_b_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = lean_nat_dec_lt(v_a_172_, v_upperBound_169_);
if (v___x_174_ == 0)
{
lean_dec(v_a_172_);
lean_dec(v_paramIdx_171_);
return v_b_173_;
}
else
{
lean_object* v_graph_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_graph_175_ = lean_ctor_get(v_b_173_, 0);
v___x_176_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_177_ = lean_array_get_borrowed(v___x_176_, v_graph_175_, v_a_172_);
v___x_178_ = lean_array_get_size(v___x_177_);
v___x_179_ = lean_unsigned_to_nat(0u);
lean_inc(v_paramIdx_171_);
v___x_180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v___x_178_, v_a_172_, v_funIdx_170_, v_paramIdx_171_, v___x_179_, v_b_173_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_a_172_, v___x_181_);
lean_dec(v_a_172_);
v_a_172_ = v___x_182_;
v_b_173_ = v___x_180_;
goto _start;
}
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
lean_object* v___x_193_; lean_object* v___y_195_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_193_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_208_ = lean_array_get_size(v_graph_188_);
v___x_209_ = lean_nat_dec_lt(v_funIdx_184_, v___x_208_);
if (v___x_209_ == 0)
{
v___y_195_ = v_graph_188_;
goto v___jp_194_;
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
v___y_195_ = v___x_215_;
goto v___jp_194_;
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_info_199_; 
v___x_196_ = lean_array_get_size(v___y_195_);
v___x_197_ = lean_unsigned_to_nat(0u);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___y_195_);
v_info_199_ = v___x_191_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___y_195_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v_revDeps_189_);
v_info_199_ = v_reuseFailAlloc_207_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; lean_object* v_revDeps_201_; lean_object* v___x_202_; lean_object* v___x_203_; size_t v_sz_204_; size_t v___x_205_; lean_object* v___x_206_; 
lean_inc(v_paramIdx_185_);
v___x_200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v___x_196_, v_funIdx_184_, v_paramIdx_185_, v___x_197_, v_info_199_);
v_revDeps_201_ = lean_ctor_get(v___x_200_, 1);
lean_inc_ref(v_revDeps_201_);
v___x_202_ = lean_array_get(v___x_193_, v_revDeps_201_, v_funIdx_184_);
lean_dec_ref(v_revDeps_201_);
v___x_203_ = lean_array_get(v___x_193_, v___x_202_, v_paramIdx_185_);
lean_dec(v_paramIdx_185_);
lean_dec(v___x_202_);
v_sz_204_ = lean_array_size(v___x_203_);
v___x_205_ = ((size_t)0ULL);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_184_, v___x_203_, v_sz_204_, v___x_205_, v___x_200_);
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
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___y_348_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_345_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_346_ = lean_box(0);
v___x_359_ = lean_array_get_size(v_graph_340_);
v___x_360_ = lean_nat_dec_lt(v_calleeIdx_322_, v___x_359_);
if (v___x_360_ == 0)
{
v___y_348_ = v_graph_340_;
goto v___jp_347_;
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
v___y_348_ = v___x_366_;
goto v___jp_347_;
}
}
v___jp_347_:
{
lean_object* v_info_350_; 
lean_inc_ref(v___y_348_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___y_348_);
v_info_350_ = v___x_343_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___y_348_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_revDeps_341_);
v_info_350_ = v_reuseFailAlloc_358_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_array_get_borrowed(v___x_345_, v___y_348_, v_callerIdx_324_);
v___x_352_ = lean_array_get_borrowed(v___x_346_, v___x_351_, v_paramIdx_325_);
if (lean_obj_tag(v___x_352_) == 1)
{
lean_object* v_val_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_graph_357_; 
lean_inc_ref(v___x_352_);
lean_dec_ref(v___y_348_);
v_val_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_val_353_);
lean_dec_ref_known(v___x_352_, 1);
v___x_354_ = lean_array_get_size(v_val_353_);
v___x_355_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_323_);
v___x_356_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v___x_354_, v_val_353_, v_calleeIdx_322_, v_argIdx_323_, v___x_355_, v_info_350_);
lean_dec(v_val_353_);
v_graph_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_graph_357_);
v_info_328_ = v___x_356_;
v_graph_329_ = v_graph_357_;
goto v___jp_327_;
}
else
{
v_info_328_ = v_info_350_;
v_graph_329_ = v___y_348_;
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
v___x_695_ = lean_st_ref_put(v___y_679_, v___x_694_);
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
lean_object* v___f_1009_; lean_object* v___x_25810__overap_1010_; lean_object* v___x_1011_; 
v___f_1009_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_25810__overap_1010_ = lean_panic_fn_borrowed(v___f_1009_, v_msg_1003_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
v___x_1011_ = lean_apply_5(v___x_25810__overap_1010_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, lean_box(0));
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
v___x_1147_ = lean_st_ref_put(v___y_1108_, v___x_1146_);
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
v___x_1313_ = lean_st_ref_put(v_a_1307_, v___x_1312_);
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
v___x_2388_ = lean_st_ref_put(v_val_2376_, v___x_2387_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_upperBound_2402_, lean_object* v_val_2403_, lean_object* v_next_2404_, lean_object* v_params_2405_, lean_object* v___x_2406_, lean_object* v_val_2407_, lean_object* v_next_2408_, lean_object* v___x_2409_, lean_object* v___x_2410_, lean_object* v_a_2411_, uint8_t v_b_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
uint8_t v_a_2419_; uint8_t v___x_2423_; 
v___x_2423_ = lean_nat_dec_lt(v_a_2411_, v_upperBound_2402_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_dec(v_a_2411_);
lean_dec(v_next_2408_);
lean_dec_ref(v___x_2406_);
v___x_2424_ = lean_box(v_b_2412_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = lean_st_ref_get(v_val_2403_);
v___x_2427_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2404_, v_a_2411_, v___x_2426_);
lean_dec(v___x_2426_);
if (v___x_2427_ == 0)
{
v_a_2419_ = v_b_2412_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2428_; uint8_t v_foApprox_2429_; uint8_t v_ctxApprox_2430_; uint8_t v_quasiPatternApprox_2431_; uint8_t v_constApprox_2432_; uint8_t v_isDefEqStuckEx_2433_; uint8_t v_unificationHints_2434_; uint8_t v_assignSyntheticOpaque_2435_; uint8_t v_offsetCnstrs_2436_; uint8_t v_transparency_2437_; uint8_t v_etaStruct_2438_; uint8_t v_univApprox_2439_; uint8_t v_iota_2440_; uint8_t v_beta_2441_; uint8_t v_proj_2442_; uint8_t v_zeta_2443_; uint8_t v_zetaDelta_2444_; uint8_t v_zetaUnused_2445_; uint8_t v_zetaHave_2446_; uint8_t v_canUnfoldPredicateConfig_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2478_; 
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
v_canUnfoldPredicateConfig_2447_ = lean_ctor_get_uint8(v___x_2428_, 19);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2449_ = v___x_2428_;
v_isShared_2450_ = v_isSharedCheck_2478_;
goto v_resetjp_2448_;
}
else
{
lean_dec(v___x_2428_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2478_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v_trackZetaDelta_2451_; lean_object* v_zetaDeltaSet_2452_; lean_object* v_lctx_2453_; lean_object* v_localInstances_2454_; lean_object* v_defEqCtx_x3f_2455_; lean_object* v_synthPendingDepth_2456_; lean_object* v_customCanUnfoldPredicate_x3f_2457_; uint8_t v_univApprox_2458_; uint8_t v_inTypeClassResolution_2459_; uint8_t v_cacheInferType_2460_; uint8_t v___x_2461_; lean_object* v___x_2463_; 
v_trackZetaDelta_2451_ = lean_ctor_get_uint8(v___y_2413_, sizeof(void*)*7);
v_zetaDeltaSet_2452_ = lean_ctor_get(v___y_2413_, 1);
v_lctx_2453_ = lean_ctor_get(v___y_2413_, 2);
v_localInstances_2454_ = lean_ctor_get(v___y_2413_, 3);
v_defEqCtx_x3f_2455_ = lean_ctor_get(v___y_2413_, 4);
v_synthPendingDepth_2456_ = lean_ctor_get(v___y_2413_, 5);
v_customCanUnfoldPredicate_x3f_2457_ = lean_ctor_get(v___y_2413_, 6);
v_univApprox_2458_ = lean_ctor_get_uint8(v___y_2413_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2459_ = lean_ctor_get_uint8(v___y_2413_, sizeof(void*)*7 + 2);
v_cacheInferType_2460_ = lean_ctor_get_uint8(v___y_2413_, sizeof(void*)*7 + 3);
v___x_2461_ = 0;
if (v_isShared_2450_ == 0)
{
v___x_2463_ = v___x_2449_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 0, v_foApprox_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 1, v_ctxApprox_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 2, v_quasiPatternApprox_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 3, v_constApprox_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 4, v_isDefEqStuckEx_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 5, v_unificationHints_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 7, v_assignSyntheticOpaque_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 8, v_offsetCnstrs_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 9, v_transparency_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 10, v_etaStruct_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 11, v_univApprox_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 12, v_iota_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 13, v_beta_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 14, v_proj_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 15, v_zeta_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 16, v_zetaDelta_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 17, v_zetaUnused_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 18, v_zetaHave_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, 19, v_canUnfoldPredicateConfig_2447_);
v___x_2463_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
uint64_t v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_ctor_set_uint8(v___x_2463_, 6, v___x_2461_);
v___x_2464_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2463_);
v___x_2465_ = lean_array_fget_borrowed(v_params_2405_, v_a_2411_);
v___x_2466_ = 2;
v___x_2467_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2467_, 0, v___x_2463_);
lean_ctor_set_uint64(v___x_2467_, sizeof(void*)*1, v___x_2464_);
v___x_2468_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2466_, v___x_2467_);
lean_inc(v_customCanUnfoldPredicate_x3f_2457_);
lean_inc(v_synthPendingDepth_2456_);
lean_inc(v_defEqCtx_x3f_2455_);
lean_inc_ref(v_localInstances_2454_);
lean_inc_ref(v_lctx_2453_);
lean_inc(v_zetaDeltaSet_2452_);
v___x_2469_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v_zetaDeltaSet_2452_);
lean_ctor_set(v___x_2469_, 2, v_lctx_2453_);
lean_ctor_set(v___x_2469_, 3, v_localInstances_2454_);
lean_ctor_set(v___x_2469_, 4, v_defEqCtx_x3f_2455_);
lean_ctor_set(v___x_2469_, 5, v_synthPendingDepth_2456_);
lean_ctor_set(v___x_2469_, 6, v_customCanUnfoldPredicate_x3f_2457_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*7, v_trackZetaDelta_2451_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*7 + 1, v_univApprox_2458_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2459_);
lean_ctor_set_uint8(v___x_2469_, sizeof(void*)*7 + 3, v_cacheInferType_2460_);
lean_inc_ref(v___x_2406_);
lean_inc(v___x_2465_);
v___x_2470_ = l_Lean_Meta_isExprDefEq(v___x_2465_, v___x_2406_, v___x_2469_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec_ref_known(v___x_2469_, 7);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; uint8_t v___x_2472_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2472_ = lean_unbox(v_a_2471_);
lean_dec(v_a_2471_);
if (v___x_2472_ == 0)
{
v_a_2419_ = v_b_2412_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2473_ = lean_st_ref_take(v_val_2403_);
lean_inc(v_a_2411_);
lean_inc(v_next_2408_);
v___x_2474_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2407_, v_next_2408_, v_next_2404_, v_a_2411_, v___x_2473_);
v___x_2475_ = lean_st_ref_put(v_val_2403_, v___x_2474_);
v___x_2476_ = lean_nat_dec_eq(v___x_2409_, v___x_2410_);
v_a_2419_ = v___x_2476_;
goto v___jp_2418_;
}
}
else
{
lean_dec(v_a_2411_);
lean_dec(v_next_2408_);
lean_dec_ref(v___x_2406_);
return v___x_2470_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_upperBound_2479_, lean_object* v_val_2480_, lean_object* v_next_2481_, lean_object* v_params_2482_, lean_object* v___x_2483_, lean_object* v_val_2484_, lean_object* v_next_2485_, lean_object* v___x_2486_, lean_object* v___x_2487_, lean_object* v_a_2488_, lean_object* v_b_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v_b_boxed_2495_; lean_object* v_res_2496_; 
v_b_boxed_2495_ = lean_unbox(v_b_2489_);
v_res_2496_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_2479_, v_val_2480_, v_next_2481_, v_params_2482_, v___x_2483_, v_val_2484_, v_next_2485_, v___x_2486_, v___x_2487_, v_a_2488_, v_b_boxed_2495_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___x_2487_);
lean_dec(v___x_2486_);
lean_dec(v_val_2484_);
lean_dec_ref(v_params_2482_);
lean_dec(v_next_2481_);
lean_dec(v_val_2480_);
lean_dec(v_upperBound_2479_);
return v_res_2496_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2508_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2509_ = l_Lean_Name_append(v___x_2508_, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2514_ = l_Lean_stringToMessageData(v___x_2513_);
return v___x_2514_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2517_ = l_Lean_stringToMessageData(v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2520_ = l_Lean_stringToMessageData(v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2526_ = l_Lean_stringToMessageData(v___x_2525_);
return v___x_2526_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2529_ = l_Lean_stringToMessageData(v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2530_, lean_object* v_val_2531_, lean_object* v_upperBound_2532_, lean_object* v_args_2533_, lean_object* v_e_2534_, lean_object* v_next_2535_, lean_object* v_params_2536_, lean_object* v___x_2537_, lean_object* v___x_2538_, lean_object* v_a_2539_, lean_object* v_b_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_a_2547_; lean_object* v___y_2552_; uint8_t v___x_2571_; 
v___x_2571_ = lean_nat_dec_lt(v_a_2539_, v_upperBound_2532_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_b_2540_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; 
v___x_2573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2530_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = lean_box(0);
v___x_2576_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2531_, v_a_2539_, v_a_2574_);
lean_dec(v_a_2574_);
if (v___x_2576_ == 0)
{
v_a_2547_ = v___x_2575_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2577_ = lean_array_get_size(v_args_2533_);
v___x_2578_ = lean_nat_dec_lt(v_a_2539_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v_options_2579_; lean_object* v_inheritedTraceOptions_2580_; uint8_t v_hasTrace_2581_; 
v_options_2579_ = lean_ctor_get(v___y_2543_, 2);
v_inheritedTraceOptions_2580_ = lean_ctor_get(v___y_2543_, 13);
v_hasTrace_2581_ = lean_ctor_get_uint8(v_options_2579_, sizeof(void*)*1);
if (v_hasTrace_2581_ == 0)
{
goto v___jp_2582_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2585_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2586_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2580_, v_options_2579_, v___x_2585_);
if (v___x_2586_ == 0)
{
goto v___jp_2582_;
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2587_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2531_);
v___x_2588_ = l_Nat_reprFast(v_val_2531_);
v___x_2589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
v___x_2590_ = l_Lean_MessageData_ofFormat(v___x_2589_);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2587_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
lean_inc(v_a_2539_);
v___x_2594_ = l_Nat_reprFast(v_a_2539_);
v___x_2595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
v___x_2596_ = l_Lean_MessageData_ofFormat(v___x_2595_);
lean_inc_ref(v___x_2596_);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2593_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
lean_inc_ref(v_e_2534_);
v___x_2600_ = l_Lean_MessageData_ofExpr(v_e_2534_);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v___x_2596_);
v___x_2605_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2584_, v___x_2604_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
lean_inc(v_a_2539_);
v___x_2607_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2530_, v_val_2531_, v_a_2539_, v___x_2575_, v_a_2606_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
v___y_2552_ = v___x_2607_;
goto v___jp_2551_;
}
else
{
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
return v___x_2605_;
}
}
}
v___jp_2582_:
{
lean_object* v___x_2583_; 
lean_inc(v_a_2539_);
v___x_2583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2530_, v_val_2531_, v_a_2539_, v___x_2575_, v___x_2575_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
v___y_2552_ = v___x_2583_;
goto v___jp_2551_;
}
}
else
{
lean_object* v___x_2608_; 
v___x_2608_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2530_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
v___x_2610_ = lean_array_fget_borrowed(v_args_2533_, v_a_2539_);
v___x_2611_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2531_, v_a_2539_, v_next_2535_, v_a_2609_);
lean_dec(v_a_2609_);
if (lean_obj_tag(v___x_2611_) == 1)
{
lean_object* v_val_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2708_; 
v_val_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2708_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_val_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2708_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; uint8_t v_foApprox_2617_; uint8_t v_ctxApprox_2618_; uint8_t v_quasiPatternApprox_2619_; uint8_t v_constApprox_2620_; uint8_t v_isDefEqStuckEx_2621_; uint8_t v_unificationHints_2622_; uint8_t v_assignSyntheticOpaque_2623_; uint8_t v_offsetCnstrs_2624_; uint8_t v_transparency_2625_; uint8_t v_etaStruct_2626_; uint8_t v_univApprox_2627_; uint8_t v_iota_2628_; uint8_t v_beta_2629_; uint8_t v_proj_2630_; uint8_t v_zeta_2631_; uint8_t v_zetaDelta_2632_; uint8_t v_zetaUnused_2633_; uint8_t v_zetaHave_2634_; uint8_t v_canUnfoldPredicateConfig_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2707_; 
v___x_2616_ = l_Lean_Meta_Context_config(v___y_2541_);
v_foApprox_2617_ = lean_ctor_get_uint8(v___x_2616_, 0);
v_ctxApprox_2618_ = lean_ctor_get_uint8(v___x_2616_, 1);
v_quasiPatternApprox_2619_ = lean_ctor_get_uint8(v___x_2616_, 2);
v_constApprox_2620_ = lean_ctor_get_uint8(v___x_2616_, 3);
v_isDefEqStuckEx_2621_ = lean_ctor_get_uint8(v___x_2616_, 4);
v_unificationHints_2622_ = lean_ctor_get_uint8(v___x_2616_, 5);
v_assignSyntheticOpaque_2623_ = lean_ctor_get_uint8(v___x_2616_, 7);
v_offsetCnstrs_2624_ = lean_ctor_get_uint8(v___x_2616_, 8);
v_transparency_2625_ = lean_ctor_get_uint8(v___x_2616_, 9);
v_etaStruct_2626_ = lean_ctor_get_uint8(v___x_2616_, 10);
v_univApprox_2627_ = lean_ctor_get_uint8(v___x_2616_, 11);
v_iota_2628_ = lean_ctor_get_uint8(v___x_2616_, 12);
v_beta_2629_ = lean_ctor_get_uint8(v___x_2616_, 13);
v_proj_2630_ = lean_ctor_get_uint8(v___x_2616_, 14);
v_zeta_2631_ = lean_ctor_get_uint8(v___x_2616_, 15);
v_zetaDelta_2632_ = lean_ctor_get_uint8(v___x_2616_, 16);
v_zetaUnused_2633_ = lean_ctor_get_uint8(v___x_2616_, 17);
v_zetaHave_2634_ = lean_ctor_get_uint8(v___x_2616_, 18);
v_canUnfoldPredicateConfig_2635_ = lean_ctor_get_uint8(v___x_2616_, 19);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2637_ = v___x_2616_;
v_isShared_2638_ = v_isSharedCheck_2707_;
goto v_resetjp_2636_;
}
else
{
lean_dec(v___x_2616_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2707_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
uint8_t v_trackZetaDelta_2639_; lean_object* v_zetaDeltaSet_2640_; lean_object* v_lctx_2641_; lean_object* v_localInstances_2642_; lean_object* v_defEqCtx_x3f_2643_; lean_object* v_synthPendingDepth_2644_; lean_object* v_customCanUnfoldPredicate_x3f_2645_; uint8_t v_univApprox_2646_; uint8_t v_inTypeClassResolution_2647_; uint8_t v_cacheInferType_2648_; uint8_t v___x_2649_; lean_object* v___x_2651_; 
v_trackZetaDelta_2639_ = lean_ctor_get_uint8(v___y_2541_, sizeof(void*)*7);
v_zetaDeltaSet_2640_ = lean_ctor_get(v___y_2541_, 1);
v_lctx_2641_ = lean_ctor_get(v___y_2541_, 2);
v_localInstances_2642_ = lean_ctor_get(v___y_2541_, 3);
v_defEqCtx_x3f_2643_ = lean_ctor_get(v___y_2541_, 4);
v_synthPendingDepth_2644_ = lean_ctor_get(v___y_2541_, 5);
v_customCanUnfoldPredicate_x3f_2645_ = lean_ctor_get(v___y_2541_, 6);
v_univApprox_2646_ = lean_ctor_get_uint8(v___y_2541_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2647_ = lean_ctor_get_uint8(v___y_2541_, sizeof(void*)*7 + 2);
v_cacheInferType_2648_ = lean_ctor_get_uint8(v___y_2541_, sizeof(void*)*7 + 3);
v___x_2649_ = 0;
if (v_isShared_2638_ == 0)
{
v___x_2651_ = v___x_2637_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 0, v_foApprox_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 1, v_ctxApprox_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 2, v_quasiPatternApprox_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 3, v_constApprox_2620_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 4, v_isDefEqStuckEx_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 5, v_unificationHints_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 7, v_assignSyntheticOpaque_2623_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 8, v_offsetCnstrs_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 9, v_transparency_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 10, v_etaStruct_2626_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 11, v_univApprox_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 12, v_iota_2628_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 13, v_beta_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 14, v_proj_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 15, v_zeta_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 16, v_zetaDelta_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 17, v_zetaUnused_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 18, v_zetaHave_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2706_, 19, v_canUnfoldPredicateConfig_2635_);
v___x_2651_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
uint64_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_ctor_set_uint8(v___x_2651_, 6, v___x_2649_);
v___x_2652_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2651_);
v___x_2653_ = l_Lean_instInhabitedExpr;
v___x_2654_ = lean_array_get_borrowed(v___x_2653_, v_params_2536_, v_val_2612_);
lean_dec(v_val_2612_);
v___x_2655_ = 2;
v___x_2656_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2656_, 0, v___x_2651_);
lean_ctor_set_uint64(v___x_2656_, sizeof(void*)*1, v___x_2652_);
v___x_2657_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2655_, v___x_2656_);
lean_inc(v_customCanUnfoldPredicate_x3f_2645_);
lean_inc(v_synthPendingDepth_2644_);
lean_inc(v_defEqCtx_x3f_2643_);
lean_inc_ref(v_localInstances_2642_);
lean_inc_ref(v_lctx_2641_);
lean_inc(v_zetaDeltaSet_2640_);
v___x_2658_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v_zetaDeltaSet_2640_);
lean_ctor_set(v___x_2658_, 2, v_lctx_2641_);
lean_ctor_set(v___x_2658_, 3, v_localInstances_2642_);
lean_ctor_set(v___x_2658_, 4, v_defEqCtx_x3f_2643_);
lean_ctor_set(v___x_2658_, 5, v_synthPendingDepth_2644_);
lean_ctor_set(v___x_2658_, 6, v_customCanUnfoldPredicate_x3f_2645_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*7, v_trackZetaDelta_2639_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*7 + 1, v_univApprox_2646_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2647_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*7 + 3, v_cacheInferType_2648_);
lean_inc(v___x_2610_);
lean_inc(v___x_2654_);
v___x_2659_ = l_Lean_Meta_isExprDefEq(v___x_2654_, v___x_2610_, v___x_2658_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec_ref_known(v___x_2658_, 7);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; uint8_t v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = lean_unbox(v_a_2660_);
lean_dec(v_a_2660_);
if (v___x_2661_ == 0)
{
lean_object* v_options_2662_; lean_object* v_inheritedTraceOptions_2663_; uint8_t v_hasTrace_2664_; 
v_options_2662_ = lean_ctor_get(v___y_2543_, 2);
v_inheritedTraceOptions_2663_ = lean_ctor_get(v___y_2543_, 13);
v_hasTrace_2664_ = lean_ctor_get_uint8(v_options_2662_, sizeof(void*)*1);
if (v_hasTrace_2664_ == 0)
{
lean_del_object(v___x_2614_);
goto v___jp_2665_;
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2667_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2668_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2663_, v_options_2662_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_del_object(v___x_2614_);
goto v___jp_2665_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2670_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2531_);
v___x_2671_ = l_Nat_reprFast(v_val_2531_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set_tag(v___x_2614_, 3);
lean_ctor_set(v___x_2614_, 0, v___x_2671_);
v___x_2673_ = v___x_2614_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2674_ = l_Lean_MessageData_ofFormat(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2670_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2675_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
lean_inc(v_a_2539_);
v___x_2678_ = l_Nat_reprFast(v_a_2539_);
v___x_2679_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
v___x_2680_ = l_Lean_MessageData_ofFormat(v___x_2679_);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2677_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
lean_inc_ref(v_e_2534_);
v___x_2684_ = l_Lean_MessageData_ofExpr(v_e_2534_);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
lean_inc(v___x_2654_);
v___x_2688_ = l_Lean_MessageData_ofExpr(v___x_2654_);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2689_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
lean_inc(v___x_2610_);
v___x_2692_ = l_Lean_MessageData_ofExpr(v___x_2610_);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2667_, v___x_2693_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
lean_inc(v_a_2539_);
v___x_2696_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2530_, v_val_2531_, v_a_2539_, v___x_2575_, v_a_2695_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
v___y_2552_ = v___x_2696_;
goto v___jp_2551_;
}
else
{
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
return v___x_2694_;
}
}
}
}
v___jp_2665_:
{
lean_object* v___x_2666_; 
lean_inc(v_a_2539_);
v___x_2666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2530_, v_val_2531_, v_a_2539_, v___x_2575_, v___x_2575_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
v___y_2552_ = v___x_2666_;
goto v___jp_2551_;
}
}
else
{
lean_del_object(v___x_2614_);
v_a_2547_ = v___x_2575_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_del_object(v___x_2614_);
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
v_a_2698_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2659_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2659_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; 
lean_dec(v___x_2611_);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = 0;
lean_inc(v_a_2539_);
lean_inc(v___x_2610_);
v___x_2711_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v___x_2537_, v_val_2530_, v_next_2535_, v_params_2536_, v___x_2610_, v_val_2531_, v_a_2539_, v___x_2537_, v___x_2538_, v___x_2709_, v___x_2710_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; uint8_t v___x_2713_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = lean_unbox(v_a_2712_);
lean_dec(v_a_2712_);
if (v___x_2713_ == 0)
{
lean_object* v_options_2714_; lean_object* v_inheritedTraceOptions_2715_; uint8_t v_hasTrace_2716_; 
v_options_2714_ = lean_ctor_get(v___y_2543_, 2);
v_inheritedTraceOptions_2715_ = lean_ctor_get(v___y_2543_, 13);
v_hasTrace_2716_ = lean_ctor_get_uint8(v_options_2714_, sizeof(void*)*1);
if (v_hasTrace_2716_ == 0)
{
goto v___jp_2717_;
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2719_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2720_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2715_, v_options_2714_, v___x_2720_);
if (v___x_2721_ == 0)
{
goto v___jp_2717_;
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2722_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2531_);
v___x_2723_ = l_Nat_reprFast(v_val_2531_);
v___x_2724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
v___x_2725_ = l_Lean_MessageData_ofFormat(v___x_2724_);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2722_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
lean_inc(v_a_2539_);
v___x_2729_ = l_Nat_reprFast(v_a_2539_);
v___x_2730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
v___x_2731_ = l_Lean_MessageData_ofFormat(v___x_2730_);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2728_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
lean_inc_ref(v_e_2534_);
v___x_2735_ = l_Lean_MessageData_ofExpr(v_e_2534_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
lean_inc(v___x_2610_);
v___x_2739_ = l_Lean_MessageData_ofExpr(v___x_2610_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2719_, v___x_2742_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2745_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2743_, 1);
lean_inc(v_a_2539_);
v___x_2745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2530_, v_val_2531_, v_a_2539_, v___x_2575_, v_a_2744_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
v___y_2552_ = v___x_2745_;
goto v___jp_2551_;
}
else
{
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
return v___x_2743_;
}
}
}
v___jp_2717_:
{
lean_object* v___x_2718_; 
lean_inc(v_a_2539_);
v___x_2718_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2530_, v_val_2531_, v_a_2539_, v___x_2575_, v___x_2575_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
v___y_2552_ = v___x_2718_;
goto v___jp_2551_;
}
}
else
{
v_a_2547_ = v___x_2575_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
v_a_2746_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2711_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2711_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
v_a_2754_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2608_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2608_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
v_a_2762_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2573_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2573_);
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
v___jp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_add(v_a_2539_, v___x_2548_);
lean_dec(v_a_2539_);
v_a_2539_ = v___x_2549_;
v_b_2540_ = v_a_2547_;
goto _start;
}
v___jp_2551_:
{
if (lean_obj_tag(v___y_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2562_; 
v_a_2553_ = lean_ctor_get(v___y_2552_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___y_2552_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2555_ = v___y_2552_;
v_isShared_2556_ = v_isSharedCheck_2562_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___y_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2562_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
if (lean_obj_tag(v_a_2553_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
v_a_2557_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v_a_2553_, 1);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v_a_2557_);
v___x_2559_ = v___x_2555_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
else
{
lean_object* v_a_2561_; 
lean_del_object(v___x_2555_);
v_a_2561_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v_a_2553_, 1);
v_a_2547_ = v_a_2561_;
goto v___jp_2546_;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_e_2534_);
lean_dec(v_val_2531_);
v_a_2563_ = lean_ctor_get(v___y_2552_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___y_2552_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___y_2552_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___y_2552_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2770_, lean_object* v_val_2771_, lean_object* v_upperBound_2772_, lean_object* v_args_2773_, lean_object* v_e_2774_, lean_object* v_next_2775_, lean_object* v_params_2776_, lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v_a_2779_, lean_object* v_b_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2770_, v_val_2771_, v_upperBound_2772_, v_args_2773_, v_e_2774_, v_next_2775_, v_params_2776_, v___x_2777_, v___x_2778_, v_a_2779_, v_b_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___x_2778_);
lean_dec(v___x_2777_);
lean_dec_ref(v_params_2776_);
lean_dec(v_next_2775_);
lean_dec_ref(v_args_2773_);
lean_dec(v_upperBound_2772_);
lean_dec(v_val_2770_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2789_, lean_object* v___x_2790_, lean_object* v_val_2791_, lean_object* v_e_2792_, lean_object* v_next_2793_, lean_object* v_params_2794_, lean_object* v___x_2795_, lean_object* v___x_2796_, lean_object* v_x_2797_, lean_object* v_x_2798_, lean_object* v_x_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
if (lean_obj_tag(v_x_2797_) == 5)
{
lean_object* v_fn_2805_; lean_object* v_arg_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_fn_2805_ = lean_ctor_get(v_x_2797_, 0);
lean_inc_ref(v_fn_2805_);
v_arg_2806_ = lean_ctor_get(v_x_2797_, 1);
lean_inc_ref(v_arg_2806_);
lean_dec_ref_known(v_x_2797_, 2);
v___x_2807_ = lean_array_set(v_x_2798_, v_x_2799_, v_arg_2806_);
v___x_2808_ = lean_unsigned_to_nat(1u);
v___x_2809_ = lean_nat_sub(v_x_2799_, v___x_2808_);
lean_dec(v_x_2799_);
v_x_2797_ = v_fn_2805_;
v_x_2798_ = v___x_2807_;
v_x_2799_ = v___x_2809_;
goto _start;
}
else
{
uint8_t v___x_2811_; 
lean_dec(v_x_2799_);
v___x_2811_ = l_Lean_Expr_isConst(v_x_2797_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec_ref(v_x_2798_);
lean_dec_ref(v_x_2797_);
lean_dec_ref(v_e_2792_);
v___x_2812_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
return v___x_2813_;
}
else
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = l_Lean_Expr_constName_x21(v_x_2797_);
lean_dec_ref(v_x_2797_);
v___x_2815_ = lean_unsigned_to_nat(0u);
v___x_2816_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2814_, v_preDefs_2789_, v___x_2815_);
lean_dec(v___x_2814_);
if (lean_obj_tag(v___x_2816_) == 1)
{
lean_object* v_val_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_val_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_array_get_borrowed(v___x_2815_, v___x_2790_, v_val_2817_);
v___x_2820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2791_, v_val_2817_, v___x_2819_, v_x_2798_, v_e_2792_, v_next_2793_, v_params_2794_, v___x_2795_, v___x_2796_, v___x_2815_, v___x_2818_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec_ref(v_x_2798_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2828_; 
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2828_ == 0)
{
lean_object* v_unused_2829_; 
v_unused_2829_ = lean_ctor_get(v___x_2820_, 0);
lean_dec(v_unused_2829_);
v___x_2822_ = v___x_2820_;
v_isShared_2823_ = v_isSharedCheck_2828_;
goto v_resetjp_2821_;
}
else
{
lean_dec(v___x_2820_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2828_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v___x_2824_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
v_a_2830_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2820_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2820_);
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
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec(v___x_2816_);
lean_dec_ref(v_x_2798_);
lean_dec_ref(v_e_2792_);
v___x_2838_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2840_, lean_object* v___x_2841_, lean_object* v_val_2842_, lean_object* v_e_2843_, lean_object* v_next_2844_, lean_object* v_params_2845_, lean_object* v___x_2846_, lean_object* v___x_2847_, lean_object* v_x_2848_, lean_object* v_x_2849_, lean_object* v_x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2840_, v___x_2841_, v_val_2842_, v_e_2843_, v_next_2844_, v_params_2845_, v___x_2846_, v___x_2847_, v_x_2848_, v_x_2849_, v_x_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___x_2847_);
lean_dec(v___x_2846_);
lean_dec_ref(v_params_2845_);
lean_dec(v_next_2844_);
lean_dec(v_val_2842_);
lean_dec_ref(v___x_2841_);
lean_dec_ref(v_preDefs_2840_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2857_, lean_object* v___x_2858_, lean_object* v_val_2859_, lean_object* v_a_2860_, lean_object* v_params_2861_, lean_object* v___x_2862_, lean_object* v___x_2863_, lean_object* v_e_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_dummy_2870_; lean_object* v_nargs_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v_dummy_2870_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2871_ = l_Lean_Expr_getAppNumArgs(v_e_2864_);
lean_inc(v_nargs_2871_);
v___x_2872_ = lean_mk_array(v_nargs_2871_, v_dummy_2870_);
v___x_2873_ = lean_unsigned_to_nat(1u);
v___x_2874_ = lean_nat_sub(v_nargs_2871_, v___x_2873_);
lean_dec(v_nargs_2871_);
lean_inc_ref(v_e_2864_);
v___x_2875_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2857_, v___x_2858_, v_val_2859_, v_e_2864_, v_a_2860_, v_params_2861_, v___x_2862_, v___x_2863_, v_e_2864_, v___x_2872_, v___x_2874_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2876_, lean_object* v___x_2877_, lean_object* v_val_2878_, lean_object* v_a_2879_, lean_object* v_params_2880_, lean_object* v___x_2881_, lean_object* v___x_2882_, lean_object* v_e_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2876_, v___x_2877_, v_val_2878_, v_a_2879_, v_params_2880_, v___x_2881_, v___x_2882_, v_e_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___x_2882_);
lean_dec(v___x_2881_);
lean_dec_ref(v_params_2880_);
lean_dec(v_a_2879_);
lean_dec(v_val_2878_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v_preDefs_2876_);
return v_res_2889_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2893_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2894_ = lean_unsigned_to_nat(6u);
v___x_2895_ = lean_unsigned_to_nat(201u);
v___x_2896_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2897_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2898_ = l_mkPanicMessageWithDecl(v___x_2897_, v___x_2896_, v___x_2895_, v___x_2894_, v___x_2893_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2899_, lean_object* v___x_2900_, lean_object* v_a_2901_, lean_object* v_preDefs_2902_, lean_object* v_val_2903_, lean_object* v___f_2904_, lean_object* v___x_2905_, lean_object* v_params_2906_, lean_object* v_body_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v___x_2913_ = lean_array_get_size(v_params_2906_);
v___x_2914_ = lean_array_get(v___x_2899_, v___x_2900_, v_a_2901_);
v___x_2915_ = lean_nat_dec_eq(v___x_2913_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec(v___x_2914_);
lean_dec_ref(v_body_2907_);
lean_dec_ref(v_params_2906_);
lean_dec_ref(v___f_2904_);
lean_dec(v_val_2903_);
lean_dec_ref(v_preDefs_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v___x_2900_);
v___x_2916_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2917_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2916_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
return v___x_2917_;
}
else
{
lean_object* v___f_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; 
v___f_2918_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2918_, 0, v_preDefs_2902_);
lean_closure_set(v___f_2918_, 1, v___x_2900_);
lean_closure_set(v___f_2918_, 2, v_val_2903_);
lean_closure_set(v___f_2918_, 3, v_a_2901_);
lean_closure_set(v___f_2918_, 4, v_params_2906_);
lean_closure_set(v___f_2918_, 5, v___x_2913_);
lean_closure_set(v___f_2918_, 6, v___x_2914_);
v___x_2919_ = 0;
v___x_2920_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2907_, v___f_2918_, v___f_2904_, v___x_2919_, v___x_2915_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; 
v_unused_2928_ = lean_ctor_get(v___x_2920_, 0);
lean_dec(v_unused_2928_);
v___x_2922_ = v___x_2920_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v___x_2920_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v___x_2905_);
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2905_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
v_a_2929_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2920_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2920_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2937_, lean_object* v___x_2938_, lean_object* v_a_2939_, lean_object* v_preDefs_2940_, lean_object* v_val_2941_, lean_object* v___f_2942_, lean_object* v___x_2943_, lean_object* v_params_2944_, lean_object* v_body_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2937_, v___x_2938_, v_a_2939_, v_preDefs_2940_, v_val_2941_, v___f_2942_, v___x_2943_, v_params_2944_, v_body_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___x_2937_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v_e_2952_);
v___x_2959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v___x_2968_, lean_object* v_preDefs_2969_, lean_object* v_val_2970_, lean_object* v_upperBound_2971_, lean_object* v_a_2972_, lean_object* v_b_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v___x_2979_; 
v___x_2979_ = lean_nat_dec_lt(v_a_2972_, v_upperBound_2971_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_a_2972_);
lean_dec(v_val_2970_);
lean_dec_ref(v_preDefs_2969_);
lean_dec_ref(v___x_2968_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_b_2973_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v_value_2982_; lean_object* v___f_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___f_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; 
v___x_2981_ = lean_array_fget_borrowed(v_preDefs_2969_, v_a_2972_);
v_value_2982_ = lean_ctor_get(v___x_2981_, 7);
v___f_2983_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = lean_box(0);
lean_inc(v_val_2970_);
lean_inc_ref(v_preDefs_2969_);
lean_inc(v_a_2972_);
lean_inc_ref(v___x_2968_);
v___f_2986_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_2986_, 0, v___x_2984_);
lean_closure_set(v___f_2986_, 1, v___x_2968_);
lean_closure_set(v___f_2986_, 2, v_a_2972_);
lean_closure_set(v___f_2986_, 3, v_preDefs_2969_);
lean_closure_set(v___f_2986_, 4, v_val_2970_);
lean_closure_set(v___f_2986_, 5, v___f_2983_);
lean_closure_set(v___f_2986_, 6, v___x_2985_);
v___x_2987_ = 0;
lean_inc_ref(v_value_2982_);
v___x_2988_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_2982_, v___f_2986_, v___x_2987_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec_ref_known(v___x_2988_, 1);
v___x_2989_ = lean_unsigned_to_nat(1u);
v___x_2990_ = lean_nat_add(v_a_2972_, v___x_2989_);
lean_dec(v_a_2972_);
v_a_2972_ = v___x_2990_;
v_b_2973_ = v___x_2985_;
goto _start;
}
else
{
lean_dec(v_a_2972_);
lean_dec(v_val_2970_);
lean_dec_ref(v_preDefs_2969_);
lean_dec_ref(v___x_2968_);
return v___x_2988_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v___x_2992_, lean_object* v_preDefs_2993_, lean_object* v_val_2994_, lean_object* v_upperBound_2995_, lean_object* v_a_2996_, lean_object* v_b_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_2992_, v_preDefs_2993_, v_val_2994_, v_upperBound_2995_, v_a_2996_, v_b_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v_upperBound_2995_);
return v_res_3003_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3006_ = l_Lean_stringToMessageData(v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
size_t v_sz_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
v_sz_3013_ = lean_array_size(v_preDefs_3007_);
v___x_3014_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3007_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3013_, v___x_3014_, v_preDefs_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; size_t v_sz_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc_n(v_a_3016_, 2);
lean_dec_ref_known(v___x_3015_, 1);
v_sz_3017_ = lean_array_size(v_a_3016_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3017_, v___x_3014_, v_a_3016_);
v___x_3019_ = l_Lean_Elab_FixedParams_Info_init(v_a_3016_);
v___x_3020_ = lean_st_mk_ref(v___x_3019_);
v___x_3021_ = lean_st_ref_take(v___x_3020_);
v___x_3022_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3021_);
v___x_3023_ = lean_st_ref_put(v___x_3020_, v___x_3022_);
v___x_3024_ = lean_array_get_size(v_preDefs_3007_);
v___x_3025_ = lean_unsigned_to_nat(0u);
v___x_3026_ = lean_box(0);
lean_inc(v___x_3020_);
v___x_3027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3018_, v_preDefs_3007_, v___x_3020_, v___x_3024_, v___x_3025_, v___x_3026_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3066_; 
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v___x_3027_, 0);
lean_dec(v_unused_3067_);
v___x_3029_ = v___x_3027_;
v_isShared_3030_ = v_isSharedCheck_3066_;
goto v_resetjp_3028_;
}
else
{
lean_dec(v___x_3027_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3066_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v_options_3032_; uint8_t v_hasTrace_3033_; 
v___x_3031_ = lean_st_ref_get(v___x_3020_);
lean_dec(v___x_3020_);
v_options_3032_ = lean_ctor_get(v_a_3010_, 2);
v_hasTrace_3033_ = lean_ctor_get_uint8(v_options_3032_, sizeof(void*)*1);
if (v_hasTrace_3033_ == 0)
{
lean_object* v___x_3035_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3031_);
v___x_3035_ = v___x_3029_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3031_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v_inheritedTraceOptions_3037_ = lean_ctor_get(v_a_3010_, 13);
v___x_3038_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3039_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3037_, v_options_3032_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3042_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3031_);
v___x_3042_ = v___x_3029_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3031_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
else
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_del_object(v___x_3029_);
v___x_3044_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3031_);
v___x_3045_ = l_Lean_Elab_FixedParams_Info_format(v___x_3031_);
v___x_3046_ = l_Std_Format_indentD(v___x_3045_);
v___x_3047_ = l_Lean_MessageData_ofFormat(v___x_3046_);
v___x_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3044_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3038_, v___x_3048_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3049_, 0);
lean_dec(v_unused_3057_);
v___x_3051_ = v___x_3049_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_dec(v___x_3049_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3031_);
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3031_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v___x_3031_);
v_a_3058_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3049_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3049_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
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
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v___x_3020_);
v_a_3068_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3027_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3027_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref(v_preDefs_3007_);
v_a_3076_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3015_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3015_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_upperBound_3091_, lean_object* v_val_3092_, lean_object* v_next_3093_, lean_object* v_params_3094_, lean_object* v___x_3095_, lean_object* v_val_3096_, lean_object* v_next_3097_, lean_object* v___x_3098_, lean_object* v___x_3099_, lean_object* v_inst_3100_, lean_object* v_R_3101_, lean_object* v_a_3102_, uint8_t v_b_3103_, lean_object* v_c_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_3091_, v_val_3092_, v_next_3093_, v_params_3094_, v___x_3095_, v_val_3096_, v_next_3097_, v___x_3098_, v___x_3099_, v_a_3102_, v_b_3103_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3111_ = _args[0];
lean_object* v_val_3112_ = _args[1];
lean_object* v_next_3113_ = _args[2];
lean_object* v_params_3114_ = _args[3];
lean_object* v___x_3115_ = _args[4];
lean_object* v_val_3116_ = _args[5];
lean_object* v_next_3117_ = _args[6];
lean_object* v___x_3118_ = _args[7];
lean_object* v___x_3119_ = _args[8];
lean_object* v_inst_3120_ = _args[9];
lean_object* v_R_3121_ = _args[10];
lean_object* v_a_3122_ = _args[11];
lean_object* v_b_3123_ = _args[12];
lean_object* v_c_3124_ = _args[13];
lean_object* v___y_3125_ = _args[14];
lean_object* v___y_3126_ = _args[15];
lean_object* v___y_3127_ = _args[16];
lean_object* v___y_3128_ = _args[17];
lean_object* v___y_3129_ = _args[18];
_start:
{
uint8_t v_b_boxed_3130_; lean_object* v_res_3131_; 
v_b_boxed_3130_ = lean_unbox(v_b_3123_);
v_res_3131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_upperBound_3111_, v_val_3112_, v_next_3113_, v_params_3114_, v___x_3115_, v_val_3116_, v_next_3117_, v___x_3118_, v___x_3119_, v_inst_3120_, v_R_3121_, v_a_3122_, v_b_boxed_3130_, v_c_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___x_3119_);
lean_dec(v___x_3118_);
lean_dec(v_val_3116_);
lean_dec_ref(v_params_3114_);
lean_dec(v_next_3113_);
lean_dec(v_val_3112_);
lean_dec(v_upperBound_3111_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3132_, lean_object* v_val_3133_, lean_object* v_upperBound_3134_, lean_object* v_args_3135_, lean_object* v_e_3136_, lean_object* v_next_3137_, lean_object* v_params_3138_, lean_object* v___x_3139_, lean_object* v___x_3140_, lean_object* v_inst_3141_, lean_object* v_R_3142_, lean_object* v_a_3143_, lean_object* v_b_3144_, lean_object* v_c_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3132_, v_val_3133_, v_upperBound_3134_, v_args_3135_, v_e_3136_, v_next_3137_, v_params_3138_, v___x_3139_, v___x_3140_, v_a_3143_, v_b_3144_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3152_ = _args[0];
lean_object* v_val_3153_ = _args[1];
lean_object* v_upperBound_3154_ = _args[2];
lean_object* v_args_3155_ = _args[3];
lean_object* v_e_3156_ = _args[4];
lean_object* v_next_3157_ = _args[5];
lean_object* v_params_3158_ = _args[6];
lean_object* v___x_3159_ = _args[7];
lean_object* v___x_3160_ = _args[8];
lean_object* v_inst_3161_ = _args[9];
lean_object* v_R_3162_ = _args[10];
lean_object* v_a_3163_ = _args[11];
lean_object* v_b_3164_ = _args[12];
lean_object* v_c_3165_ = _args[13];
lean_object* v___y_3166_ = _args[14];
lean_object* v___y_3167_ = _args[15];
lean_object* v___y_3168_ = _args[16];
lean_object* v___y_3169_ = _args[17];
lean_object* v___y_3170_ = _args[18];
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3152_, v_val_3153_, v_upperBound_3154_, v_args_3155_, v_e_3156_, v_next_3157_, v_params_3158_, v___x_3159_, v___x_3160_, v_inst_3161_, v_R_3162_, v_a_3163_, v_b_3164_, v_c_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___x_3160_);
lean_dec(v___x_3159_);
lean_dec_ref(v_params_3158_);
lean_dec(v_next_3157_);
lean_dec_ref(v_args_3155_);
lean_dec(v_upperBound_3154_);
lean_dec(v_val_3152_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v___x_3172_, lean_object* v_preDefs_3173_, lean_object* v_val_3174_, lean_object* v_upperBound_3175_, lean_object* v_inst_3176_, lean_object* v_R_3177_, lean_object* v_a_3178_, lean_object* v_b_3179_, lean_object* v_c_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3172_, v_preDefs_3173_, v_val_3174_, v_upperBound_3175_, v_a_3178_, v_b_3179_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v___x_3187_, lean_object* v_preDefs_3188_, lean_object* v_val_3189_, lean_object* v_upperBound_3190_, lean_object* v_inst_3191_, lean_object* v_R_3192_, lean_object* v_a_3193_, lean_object* v_b_3194_, lean_object* v_c_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3187_, v_preDefs_3188_, v_val_3189_, v_upperBound_3190_, v_inst_3191_, v_R_3192_, v_a_3193_, v_b_3194_, v_c_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v_upperBound_3190_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3202_, lean_object* v___x_3203_, lean_object* v_pre_3204_, lean_object* v_post_3205_, uint8_t v_usedLetOnly_3206_, uint8_t v_skipConstInApp_3207_, uint8_t v_skipInstances_3208_, lean_object* v___x_3209_, lean_object* v_inst_3210_, lean_object* v_R_3211_, lean_object* v_a_3212_, lean_object* v_b_3213_, lean_object* v_c_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3202_, v___x_3203_, v_pre_3204_, v_post_3205_, v_usedLetOnly_3206_, v_skipConstInApp_3207_, v_skipInstances_3208_, v_a_3212_, v_b_3213_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3222_ = _args[0];
lean_object* v___x_3223_ = _args[1];
lean_object* v_pre_3224_ = _args[2];
lean_object* v_post_3225_ = _args[3];
lean_object* v_usedLetOnly_3226_ = _args[4];
lean_object* v_skipConstInApp_3227_ = _args[5];
lean_object* v_skipInstances_3228_ = _args[6];
lean_object* v___x_3229_ = _args[7];
lean_object* v_inst_3230_ = _args[8];
lean_object* v_R_3231_ = _args[9];
lean_object* v_a_3232_ = _args[10];
lean_object* v_b_3233_ = _args[11];
lean_object* v_c_3234_ = _args[12];
lean_object* v___y_3235_ = _args[13];
lean_object* v___y_3236_ = _args[14];
lean_object* v___y_3237_ = _args[15];
lean_object* v___y_3238_ = _args[16];
lean_object* v___y_3239_ = _args[17];
lean_object* v___y_3240_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3241_; uint8_t v_skipConstInApp_boxed_3242_; uint8_t v_skipInstances_boxed_3243_; lean_object* v_res_3244_; 
v_usedLetOnly_boxed_3241_ = lean_unbox(v_usedLetOnly_3226_);
v_skipConstInApp_boxed_3242_ = lean_unbox(v_skipConstInApp_3227_);
v_skipInstances_boxed_3243_ = lean_unbox(v_skipInstances_3228_);
v_res_3244_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3222_, v___x_3223_, v_pre_3224_, v_post_3225_, v_usedLetOnly_boxed_3241_, v_skipConstInApp_boxed_3242_, v_skipInstances_boxed_3243_, v___x_3229_, v_inst_3230_, v_R_3231_, v_a_3232_, v_b_3233_, v_c_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec(v___x_3229_);
lean_dec_ref(v___x_3223_);
lean_dec(v_upperBound_3222_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3245_, lean_object* v_m_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3246_, v_a_3247_);
return v___x_3248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3249_, lean_object* v_m_3250_, lean_object* v_a_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3249_, v_m_3250_, v_a_3251_);
lean_dec_ref(v_a_3251_);
lean_dec_ref(v_m_3250_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3253_, lean_object* v_name_3254_, uint8_t v_bi_3255_, lean_object* v_type_3256_, lean_object* v_k_3257_, uint8_t v_kind_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3254_, v_bi_3255_, v_type_3256_, v_k_3257_, v_kind_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3266_, lean_object* v_name_3267_, lean_object* v_bi_3268_, lean_object* v_type_3269_, lean_object* v_k_3270_, lean_object* v_kind_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
uint8_t v_bi_boxed_3278_; uint8_t v_kind_boxed_3279_; lean_object* v_res_3280_; 
v_bi_boxed_3278_ = lean_unbox(v_bi_3268_);
v_kind_boxed_3279_ = lean_unbox(v_kind_3271_);
v_res_3280_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3266_, v_name_3267_, v_bi_boxed_3278_, v_type_3269_, v_k_3270_, v_kind_boxed_3279_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3281_, lean_object* v_name_3282_, lean_object* v_type_3283_, lean_object* v_val_3284_, lean_object* v_k_3285_, uint8_t v_nondep_3286_, uint8_t v_kind_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3282_, v_type_3283_, v_val_3284_, v_k_3285_, v_nondep_3286_, v_kind_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3295_, lean_object* v_name_3296_, lean_object* v_type_3297_, lean_object* v_val_3298_, lean_object* v_k_3299_, lean_object* v_nondep_3300_, lean_object* v_kind_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
uint8_t v_nondep_boxed_3308_; uint8_t v_kind_boxed_3309_; lean_object* v_res_3310_; 
v_nondep_boxed_3308_ = lean_unbox(v_nondep_3300_);
v_kind_boxed_3309_ = lean_unbox(v_kind_3301_);
v_res_3310_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3295_, v_name_3296_, v_type_3297_, v_val_3298_, v_k_3299_, v_nondep_boxed_3308_, v_kind_boxed_3309_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3311_, lean_object* v_ref_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3312_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3319_, lean_object* v_ref_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3319_, v_ref_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3327_, lean_object* v_x_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3336_, lean_object* v_x_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3336_, v_x_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3345_, lean_object* v_m_3346_, lean_object* v_a_3347_, lean_object* v_b_3348_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3346_, v_a_3347_, v_b_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3350_, lean_object* v_a_3351_, lean_object* v_x_3352_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3351_, v_x_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3354_, lean_object* v_a_3355_, lean_object* v_x_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3354_, v_a_3355_, v_x_3356_);
lean_dec(v_x_3356_);
lean_dec_ref(v_a_3355_);
return v_res_3357_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3358_, lean_object* v_a_3359_, lean_object* v_x_3360_){
_start:
{
uint8_t v___x_3361_; 
v___x_3361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3359_, v_x_3360_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3362_, lean_object* v_a_3363_, lean_object* v_x_3364_){
_start:
{
uint8_t v_res_3365_; lean_object* v_r_3366_; 
v_res_3365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3362_, v_a_3363_, v_x_3364_);
lean_dec(v_x_3364_);
lean_dec_ref(v_a_3363_);
v_r_3366_ = lean_box(v_res_3365_);
return v_r_3366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3367_, lean_object* v_data_3368_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3370_, lean_object* v_a_3371_, lean_object* v_b_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3371_, v_b_3372_, v_x_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3375_, lean_object* v_i_3376_, lean_object* v_source_3377_, lean_object* v_target_3378_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3376_, v_source_3377_, v_target_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3380_, lean_object* v_x_3381_, lean_object* v_x_3382_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3381_, v_x_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3397_, lean_object* v_x_3398_){
_start:
{
if (lean_obj_tag(v_x_3397_) == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3399_;
}
else
{
lean_object* v_val_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3411_; 
v_val_3400_ = lean_ctor_get(v_x_3397_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v_x_3397_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3402_ = v_x_3397_;
v_isShared_3403_ = v_isSharedCheck_3411_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_val_3400_);
lean_dec(v_x_3397_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3411_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3404_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3405_ = l_Nat_reprFast(v_val_3400_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set_tag(v___x_3402_, 3);
lean_ctor_set(v___x_3402_, 0, v___x_3405_);
v___x_3407_ = v___x_3402_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3404_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = l_Repr_addAppParen(v___x_3408_, v_x_3398_);
return v___x_3409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3412_, lean_object* v_x_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3412_, v_x_3413_);
lean_dec(v_x_3413_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3415_, lean_object* v_x_3416_, lean_object* v_x_3417_){
_start:
{
if (lean_obj_tag(v_x_3417_) == 0)
{
lean_dec(v_x_3415_);
return v_x_3416_;
}
else
{
lean_object* v_head_3418_; lean_object* v_tail_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3430_; 
v_head_3418_ = lean_ctor_get(v_x_3417_, 0);
v_tail_3419_ = lean_ctor_get(v_x_3417_, 1);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_x_3417_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3421_ = v_x_3417_;
v_isShared_3422_ = v_isSharedCheck_3430_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_tail_3419_);
lean_inc(v_head_3418_);
lean_dec(v_x_3417_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3430_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
lean_inc(v_x_3415_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set_tag(v___x_3421_, 5);
lean_ctor_set(v___x_3421_, 1, v_x_3415_);
lean_ctor_set(v___x_3421_, 0, v_x_3416_);
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_x_3416_);
lean_ctor_set(v_reuseFailAlloc_3429_, 1, v_x_3415_);
v___x_3424_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3418_, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3424_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v_x_3416_ = v___x_3427_;
v_x_3417_ = v_tail_3419_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3431_, lean_object* v_x_3432_, lean_object* v_x_3433_){
_start:
{
if (lean_obj_tag(v_x_3433_) == 0)
{
lean_dec(v_x_3431_);
return v_x_3432_;
}
else
{
lean_object* v_head_3434_; lean_object* v_tail_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3446_; 
v_head_3434_ = lean_ctor_get(v_x_3433_, 0);
v_tail_3435_ = lean_ctor_get(v_x_3433_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_x_3433_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3437_ = v_x_3433_;
v_isShared_3438_ = v_isSharedCheck_3446_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_tail_3435_);
lean_inc(v_head_3434_);
lean_dec(v_x_3433_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3446_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
lean_inc(v_x_3431_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set_tag(v___x_3437_, 5);
lean_ctor_set(v___x_3437_, 1, v_x_3431_);
lean_ctor_set(v___x_3437_, 0, v_x_3432_);
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_x_3432_);
lean_ctor_set(v_reuseFailAlloc_3445_, 1, v_x_3431_);
v___x_3440_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3441_ = lean_unsigned_to_nat(0u);
v___x_3442_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3434_, v___x_3441_);
v___x_3443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3440_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3431_, v___x_3443_, v_tail_3435_);
return v___x_3444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3447_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = lean_unsigned_to_nat(0u);
v___x_3449_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3447_, v___x_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3450_, lean_object* v_x_3451_){
_start:
{
if (lean_obj_tag(v_x_3450_) == 0)
{
lean_object* v___x_3452_; 
lean_dec(v_x_3451_);
v___x_3452_ = lean_box(0);
return v___x_3452_;
}
else
{
lean_object* v_tail_3453_; 
v_tail_3453_ = lean_ctor_get(v_x_3450_, 1);
if (lean_obj_tag(v_tail_3453_) == 0)
{
lean_object* v_head_3454_; lean_object* v___x_3455_; 
lean_dec(v_x_3451_);
v_head_3454_ = lean_ctor_get(v_x_3450_, 0);
lean_inc(v_head_3454_);
lean_dec_ref_known(v_x_3450_, 2);
v___x_3455_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3454_);
return v___x_3455_;
}
else
{
lean_object* v_head_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_inc(v_tail_3453_);
v_head_3456_ = lean_ctor_get(v_x_3450_, 0);
lean_inc(v_head_3456_);
lean_dec_ref_known(v_x_3450_, 2);
v___x_3457_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3456_);
v___x_3458_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3451_, v___x_3457_, v_tail_3453_);
return v___x_3458_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3467_ = lean_string_length(v___x_3466_);
return v___x_3467_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3469_ = lean_nat_to_int(v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3475_){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3476_ = lean_array_get_size(v_xs_3475_);
v___x_3477_ = lean_unsigned_to_nat(0u);
v___x_3478_ = lean_nat_dec_eq(v___x_3476_, v___x_3477_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3479_ = lean_array_to_list(v_xs_3475_);
v___x_3480_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3481_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3479_, v___x_3480_);
v___x_3482_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3483_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
lean_ctor_set(v___x_3484_, 1, v___x_3481_);
v___x_3485_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3486_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3482_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Std_Format_fill(v___x_3487_);
return v___x_3488_;
}
else
{
lean_object* v___x_3489_; 
lean_dec_ref(v_xs_3475_);
v___x_3489_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3490_, lean_object* v_x_3491_, lean_object* v_x_3492_){
_start:
{
if (lean_obj_tag(v_x_3492_) == 0)
{
lean_dec(v_x_3490_);
return v_x_3491_;
}
else
{
lean_object* v_head_3493_; lean_object* v_tail_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3504_; 
v_head_3493_ = lean_ctor_get(v_x_3492_, 0);
v_tail_3494_ = lean_ctor_get(v_x_3492_, 1);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_x_3492_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3496_ = v_x_3492_;
v_isShared_3497_ = v_isSharedCheck_3504_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_tail_3494_);
lean_inc(v_head_3493_);
lean_dec(v_x_3492_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3504_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
lean_inc(v_x_3490_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set_tag(v___x_3496_, 5);
lean_ctor_set(v___x_3496_, 1, v_x_3490_);
lean_ctor_set(v___x_3496_, 0, v_x_3491_);
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_x_3491_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_x_3490_);
v___x_3499_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3493_);
v___x_3501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3499_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
v_x_3491_ = v___x_3501_;
v_x_3492_ = v_tail_3494_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3505_, lean_object* v_x_3506_){
_start:
{
if (lean_obj_tag(v_x_3505_) == 0)
{
lean_object* v___x_3507_; 
lean_dec(v_x_3506_);
v___x_3507_ = lean_box(0);
return v___x_3507_;
}
else
{
lean_object* v_tail_3508_; 
v_tail_3508_ = lean_ctor_get(v_x_3505_, 1);
if (lean_obj_tag(v_tail_3508_) == 0)
{
lean_object* v_head_3509_; lean_object* v___x_3510_; 
lean_dec(v_x_3506_);
v_head_3509_ = lean_ctor_get(v_x_3505_, 0);
lean_inc(v_head_3509_);
lean_dec_ref_known(v_x_3505_, 2);
v___x_3510_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3509_);
return v___x_3510_;
}
else
{
lean_object* v_head_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_inc(v_tail_3508_);
v_head_3511_ = lean_ctor_get(v_x_3505_, 0);
lean_inc(v_head_3511_);
lean_dec_ref_known(v_x_3505_, 2);
v___x_3512_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3511_);
v___x_3513_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3506_, v___x_3512_, v_tail_3508_);
return v___x_3513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3514_){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3515_ = lean_array_get_size(v_xs_3514_);
v___x_3516_ = lean_unsigned_to_nat(0u);
v___x_3517_ = lean_nat_dec_eq(v___x_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3518_ = lean_array_to_list(v_xs_3514_);
v___x_3519_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3520_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3518_, v___x_3519_);
v___x_3521_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3522_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v___x_3520_);
v___x_3524_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3523_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3521_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = l_Std_Format_fill(v___x_3526_);
return v___x_3527_;
}
else
{
lean_object* v___x_3528_; 
lean_dec_ref(v_xs_3514_);
v___x_3528_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3528_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3529_, lean_object* v_x_3530_, lean_object* v_x_3531_){
_start:
{
if (lean_obj_tag(v_x_3531_) == 0)
{
lean_dec(v_x_3529_);
return v_x_3530_;
}
else
{
lean_object* v_head_3532_; lean_object* v_tail_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3544_; 
v_head_3532_ = lean_ctor_get(v_x_3531_, 0);
v_tail_3533_ = lean_ctor_get(v_x_3531_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_x_3531_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3535_ = v_x_3531_;
v_isShared_3536_ = v_isSharedCheck_3544_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_tail_3533_);
lean_inc(v_head_3532_);
lean_dec(v_x_3531_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3544_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
lean_inc(v_x_3529_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set_tag(v___x_3535_, 5);
lean_ctor_set(v___x_3535_, 1, v_x_3529_);
lean_ctor_set(v___x_3535_, 0, v_x_3530_);
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_x_3530_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_x_3529_);
v___x_3538_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = l_Nat_reprFast(v_head_3532_);
v___x_3540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
v___x_3541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3538_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v_x_3530_ = v___x_3541_;
v_x_3531_ = v_tail_3533_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3545_, lean_object* v_x_3546_, lean_object* v_x_3547_){
_start:
{
if (lean_obj_tag(v_x_3547_) == 0)
{
lean_dec(v_x_3545_);
return v_x_3546_;
}
else
{
lean_object* v_head_3548_; lean_object* v_tail_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3560_; 
v_head_3548_ = lean_ctor_get(v_x_3547_, 0);
v_tail_3549_ = lean_ctor_get(v_x_3547_, 1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_x_3547_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3551_ = v_x_3547_;
v_isShared_3552_ = v_isSharedCheck_3560_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_tail_3549_);
lean_inc(v_head_3548_);
lean_dec(v_x_3547_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3560_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
lean_inc(v_x_3545_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set_tag(v___x_3551_, 5);
lean_ctor_set(v___x_3551_, 1, v_x_3545_);
lean_ctor_set(v___x_3551_, 0, v_x_3546_);
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_x_3546_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_x_3545_);
v___x_3554_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3555_ = l_Nat_reprFast(v_head_3548_);
v___x_3556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
v___x_3557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3554_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3545_, v___x_3557_, v_tail_3549_);
return v___x_3558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = l_Nat_reprFast(v___y_3561_);
v___x_3563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3564_, lean_object* v_x_3565_){
_start:
{
if (lean_obj_tag(v_x_3564_) == 0)
{
lean_object* v___x_3566_; 
lean_dec(v_x_3565_);
v___x_3566_ = lean_box(0);
return v___x_3566_;
}
else
{
lean_object* v_tail_3567_; 
v_tail_3567_ = lean_ctor_get(v_x_3564_, 1);
if (lean_obj_tag(v_tail_3567_) == 0)
{
lean_object* v_head_3568_; lean_object* v___x_3569_; 
lean_dec(v_x_3565_);
v_head_3568_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_head_3568_);
lean_dec_ref_known(v_x_3564_, 2);
v___x_3569_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3568_);
return v___x_3569_;
}
else
{
lean_object* v_head_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_inc(v_tail_3567_);
v_head_3570_ = lean_ctor_get(v_x_3564_, 0);
lean_inc(v_head_3570_);
lean_dec_ref_known(v_x_3564_, 2);
v___x_3571_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3570_);
v___x_3572_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3565_, v___x_3571_, v_tail_3567_);
return v___x_3572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3573_){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3574_ = lean_array_get_size(v_xs_3573_);
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = lean_nat_dec_eq(v___x_3574_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3577_ = lean_array_to_list(v_xs_3573_);
v___x_3578_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3579_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3577_, v___x_3578_);
v___x_3580_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3581_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
lean_ctor_set(v___x_3582_, 1, v___x_3579_);
v___x_3583_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3580_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = l_Std_Format_fill(v___x_3585_);
return v___x_3586_;
}
else
{
lean_object* v___x_3587_; 
lean_dec_ref(v_xs_3573_);
v___x_3587_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
if (lean_obj_tag(v_x_3590_) == 0)
{
lean_dec(v_x_3588_);
return v_x_3589_;
}
else
{
lean_object* v_head_3591_; lean_object* v_tail_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3602_; 
v_head_3591_ = lean_ctor_get(v_x_3590_, 0);
v_tail_3592_ = lean_ctor_get(v_x_3590_, 1);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_x_3590_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3594_ = v_x_3590_;
v_isShared_3595_ = v_isSharedCheck_3602_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_tail_3592_);
lean_inc(v_head_3591_);
lean_dec(v_x_3590_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3602_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
lean_inc(v_x_3588_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set_tag(v___x_3594_, 5);
lean_ctor_set(v___x_3594_, 1, v_x_3588_);
lean_ctor_set(v___x_3594_, 0, v_x_3589_);
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_x_3589_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_x_3588_);
v___x_3597_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3591_);
v___x_3599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v_x_3589_ = v___x_3599_;
v_x_3590_ = v_tail_3592_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
if (lean_obj_tag(v_x_3603_) == 0)
{
lean_object* v___x_3605_; 
lean_dec(v_x_3604_);
v___x_3605_ = lean_box(0);
return v___x_3605_;
}
else
{
lean_object* v_tail_3606_; 
v_tail_3606_ = lean_ctor_get(v_x_3603_, 1);
if (lean_obj_tag(v_tail_3606_) == 0)
{
lean_object* v_head_3607_; lean_object* v___x_3608_; 
lean_dec(v_x_3604_);
v_head_3607_ = lean_ctor_get(v_x_3603_, 0);
lean_inc(v_head_3607_);
lean_dec_ref_known(v_x_3603_, 2);
v___x_3608_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3607_);
return v___x_3608_;
}
else
{
lean_object* v_head_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
lean_inc(v_tail_3606_);
v_head_3609_ = lean_ctor_get(v_x_3603_, 0);
lean_inc(v_head_3609_);
lean_dec_ref_known(v_x_3603_, 2);
v___x_3610_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3609_);
v___x_3611_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3604_, v___x_3610_, v_tail_3606_);
return v___x_3611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3612_){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
v___x_3613_ = lean_array_get_size(v_xs_3612_);
v___x_3614_ = lean_unsigned_to_nat(0u);
v___x_3615_ = lean_nat_dec_eq(v___x_3613_, v___x_3614_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3616_ = lean_array_to_list(v_xs_3612_);
v___x_3617_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3618_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3616_, v___x_3617_);
v___x_3619_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3620_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v___x_3618_);
v___x_3622_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3621_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3619_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Std_Format_fill(v___x_3624_);
return v___x_3625_;
}
else
{
lean_object* v___x_3626_; 
lean_dec_ref(v_xs_3612_);
v___x_3626_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3626_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_){
_start:
{
if (lean_obj_tag(v_x_3629_) == 0)
{
lean_dec(v_x_3627_);
return v_x_3628_;
}
else
{
lean_object* v_head_3630_; lean_object* v_tail_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3641_; 
v_head_3630_ = lean_ctor_get(v_x_3629_, 0);
v_tail_3631_ = lean_ctor_get(v_x_3629_, 1);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_x_3629_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3633_ = v_x_3629_;
v_isShared_3634_ = v_isSharedCheck_3641_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_tail_3631_);
lean_inc(v_head_3630_);
lean_dec(v_x_3629_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3641_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
lean_inc(v_x_3627_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set_tag(v___x_3633_, 5);
lean_ctor_set(v___x_3633_, 1, v_x_3627_);
lean_ctor_set(v___x_3633_, 0, v_x_3628_);
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_x_3628_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_x_3627_);
v___x_3636_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3630_);
v___x_3638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3636_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v_x_3628_ = v___x_3638_;
v_x_3629_ = v_tail_3631_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3642_, lean_object* v_x_3643_){
_start:
{
if (lean_obj_tag(v_x_3642_) == 0)
{
lean_object* v___x_3644_; 
lean_dec(v_x_3643_);
v___x_3644_ = lean_box(0);
return v___x_3644_;
}
else
{
lean_object* v_tail_3645_; 
v_tail_3645_ = lean_ctor_get(v_x_3642_, 1);
if (lean_obj_tag(v_tail_3645_) == 0)
{
lean_object* v_head_3646_; lean_object* v___x_3647_; 
lean_dec(v_x_3643_);
v_head_3646_ = lean_ctor_get(v_x_3642_, 0);
lean_inc(v_head_3646_);
lean_dec_ref_known(v_x_3642_, 2);
v___x_3647_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3646_);
return v___x_3647_;
}
else
{
lean_object* v_head_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_inc(v_tail_3645_);
v_head_3648_ = lean_ctor_get(v_x_3642_, 0);
lean_inc(v_head_3648_);
lean_dec_ref_known(v_x_3642_, 2);
v___x_3649_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3648_);
v___x_3650_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3643_, v___x_3649_, v_tail_3645_);
return v___x_3650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3651_){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3652_ = lean_array_get_size(v_xs_3651_);
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = lean_nat_dec_eq(v___x_3652_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3655_ = lean_array_to_list(v_xs_3651_);
v___x_3656_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3657_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3655_, v___x_3656_);
v___x_3658_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3659_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
lean_ctor_set(v___x_3660_, 1, v___x_3657_);
v___x_3661_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3658_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = l_Std_Format_fill(v___x_3663_);
return v___x_3664_;
}
else
{
lean_object* v___x_3665_; 
lean_dec_ref(v_xs_3651_);
v___x_3665_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3665_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_unsigned_to_nat(12u);
v___x_3680_ = lean_nat_to_int(v___x_3679_);
return v___x_3680_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_unsigned_to_nat(9u);
v___x_3685_ = lean_nat_to_int(v___x_3684_);
return v___x_3685_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_unsigned_to_nat(11u);
v___x_3690_ = lean_nat_to_int(v___x_3689_);
return v___x_3690_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3693_ = lean_string_length(v___x_3692_);
return v___x_3693_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3695_ = lean_nat_to_int(v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3700_){
_start:
{
lean_object* v_numFixed_3701_; lean_object* v_perms_3702_; lean_object* v_revDeps_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_numFixed_3701_ = lean_ctor_get(v_x_3700_, 0);
lean_inc(v_numFixed_3701_);
v_perms_3702_ = lean_ctor_get(v_x_3700_, 1);
lean_inc_ref(v_perms_3702_);
v_revDeps_3703_ = lean_ctor_get(v_x_3700_, 2);
lean_inc_ref(v_revDeps_3703_);
lean_dec_ref(v_x_3700_);
v___x_3704_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3705_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3706_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3707_ = l_Nat_reprFast(v_numFixed_3701_);
v___x_3708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
v___x_3709_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3706_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = 0;
v___x_3711_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set_uint8(v___x_3711_, sizeof(void*)*1, v___x_3710_);
v___x_3712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3705_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_box(1);
v___x_3716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
lean_ctor_set(v___x_3719_, 1, v___x_3704_);
v___x_3720_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3721_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3702_);
v___x_3722_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3720_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set_uint8(v___x_3723_, sizeof(void*)*1, v___x_3710_);
v___x_3724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3719_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
lean_ctor_set(v___x_3725_, 1, v___x_3713_);
v___x_3726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
lean_ctor_set(v___x_3726_, 1, v___x_3715_);
v___x_3727_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
lean_ctor_set(v___x_3729_, 1, v___x_3704_);
v___x_3730_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3731_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3703_);
v___x_3732_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set_uint8(v___x_3733_, sizeof(void*)*1, v___x_3710_);
v___x_3734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3729_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3736_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3734_);
v___x_3738_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3735_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
lean_ctor_set_uint8(v___x_3741_, sizeof(void*)*1, v___x_3710_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3742_, lean_object* v_prec_3743_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3742_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3745_, lean_object* v_prec_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3745_, v_prec_3746_);
lean_dec(v_prec_3746_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v___f_3756_; lean_object* v___x_5728__overap_3757_; lean_object* v___x_3758_; 
v___f_3756_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5728__overap_3757_ = lean_panic_fn_borrowed(v___f_3756_, v_msg_3750_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
v___x_3758_ = lean_apply_5(v___x_5728__overap_3757_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, lean_box(0));
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___f_3772_; lean_object* v___x_5738__overap_3773_; lean_object* v___x_3774_; 
v___f_3772_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5738__overap_3773_ = lean_panic_fn_borrowed(v___f_3772_, v_msg_3766_);
lean_inc(v___y_3770_);
lean_inc_ref(v___y_3769_);
lean_inc(v___y_3768_);
lean_inc_ref(v___y_3767_);
v___x_3774_ = lean_apply_5(v___x_5738__overap_3773_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, lean_box(0));
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v___f_3788_; lean_object* v___x_5748__overap_3789_; lean_object* v___x_3790_; 
v___f_3788_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5748__overap_3789_ = lean_panic_fn_borrowed(v___f_3788_, v_msg_3782_);
lean_inc(v___y_3786_);
lean_inc_ref(v___y_3785_);
lean_inc(v___y_3784_);
lean_inc_ref(v___y_3783_);
v___x_3790_ = lean_apply_5(v___x_5748__overap_3789_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, lean_box(0));
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
return v_res_3797_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3801_ = lean_unsigned_to_nat(12u);
v___x_3802_ = lean_unsigned_to_nat(294u);
v___x_3803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3804_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3805_ = l_mkPanicMessageWithDecl(v___x_3804_, v___x_3803_, v___x_3802_, v___x_3801_, v___x_3800_);
return v___x_3805_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3808_ = lean_unsigned_to_nat(12u);
v___x_3809_ = lean_unsigned_to_nat(297u);
v___x_3810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3811_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3812_ = l_mkPanicMessageWithDecl(v___x_3811_, v___x_3810_, v___x_3809_, v___x_3808_, v___x_3807_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3813_, lean_object* v_as_3814_, size_t v_sz_3815_, size_t v_i_3816_, lean_object* v_b_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_a_3824_; uint8_t v___x_3828_; 
v___x_3828_ = lean_usize_dec_lt(v_i_3816_, v_sz_3815_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_b_3817_);
return v___x_3829_;
}
else
{
lean_object* v_a_3830_; 
v_a_3830_ = lean_array_uget_borrowed(v_as_3814_, v_i_3816_);
if (lean_obj_tag(v_a_3830_) == 1)
{
lean_object* v_val_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v_val_3831_ = lean_ctor_get(v_a_3830_, 0);
v___x_3832_ = lean_box(0);
v___x_3833_ = lean_unsigned_to_nat(0u);
v___x_3834_ = lean_array_get_borrowed(v___x_3832_, v_val_3831_, v___x_3833_);
if (lean_obj_tag(v___x_3834_) == 1)
{
lean_object* v_val_3835_; lean_object* v___x_3836_; 
v_val_3835_ = lean_ctor_get(v___x_3834_, 0);
v___x_3836_ = lean_array_get_borrowed(v___x_3832_, v___x_3813_, v_val_3835_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
lean_dec_ref(v_b_3817_);
v___x_3837_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3838_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3837_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3848_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3841_ = v___x_3838_;
v_isShared_3842_ = v_isSharedCheck_3848_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3838_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3848_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
if (lean_obj_tag(v_a_3839_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; 
v_a_3843_ = lean_ctor_get(v_a_3839_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v_a_3839_, 1);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v_a_3843_);
v___x_3845_ = v___x_3841_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
else
{
lean_object* v_a_3847_; 
lean_del_object(v___x_3841_);
v_a_3847_ = lean_ctor_get(v_a_3839_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v_a_3839_, 1);
v_a_3824_ = v_a_3847_;
goto v___jp_3823_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_a_3849_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3838_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3838_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
else
{
lean_object* v___x_3857_; 
lean_inc_ref(v___x_3836_);
v___x_3857_ = lean_array_push(v_b_3817_, v___x_3836_);
v_a_3824_ = v___x_3857_;
goto v___jp_3823_;
}
}
else
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3859_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3858_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_dec_ref_known(v___x_3859_, 1);
v_a_3824_ = v_b_3817_;
goto v___jp_3823_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v_b_3817_);
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_box(0);
v___x_3869_ = lean_array_push(v_b_3817_, v___x_3868_);
v_a_3824_ = v___x_3869_;
goto v___jp_3823_;
}
}
v___jp_3823_:
{
size_t v___x_3825_; size_t v___x_3826_; 
v___x_3825_ = ((size_t)1ULL);
v___x_3826_ = lean_usize_add(v_i_3816_, v___x_3825_);
v_i_3816_ = v___x_3826_;
v_b_3817_ = v_a_3824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3870_, lean_object* v_as_3871_, lean_object* v_sz_3872_, lean_object* v_i_3873_, lean_object* v_b_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
size_t v_sz_boxed_3880_; size_t v_i_boxed_3881_; lean_object* v_res_3882_; 
v_sz_boxed_3880_ = lean_unbox_usize(v_sz_3872_);
lean_dec(v_sz_3872_);
v_i_boxed_3881_ = lean_unbox_usize(v_i_3873_);
lean_dec(v_i_3873_);
v_res_3882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3870_, v_as_3871_, v_sz_boxed_3880_, v_i_boxed_3881_, v_b_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v_as_3871_);
lean_dec_ref(v___x_3870_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3885_, lean_object* v___x_3886_, lean_object* v___x_3887_, lean_object* v_a_3888_, lean_object* v_b_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
uint8_t v___x_3895_; 
v___x_3895_ = lean_nat_dec_lt(v_a_3888_, v_upperBound_3885_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; 
lean_dec(v_a_3888_);
v___x_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3896_, 0, v_b_3889_);
return v___x_3896_;
}
else
{
lean_object* v___x_3897_; lean_object* v___x_3898_; size_t v_sz_3899_; size_t v___x_3900_; lean_object* v___x_3901_; 
v___x_3897_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3898_ = lean_array_fget_borrowed(v___x_3886_, v_a_3888_);
v_sz_3899_ = lean_array_size(v___x_3898_);
v___x_3900_ = ((size_t)0ULL);
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3887_, v___x_3898_, v_sz_3899_, v___x_3900_, v___x_3897_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v___x_3901_, 1);
v___x_3903_ = lean_array_push(v_b_3889_, v_a_3902_);
v___x_3904_ = lean_unsigned_to_nat(1u);
v___x_3905_ = lean_nat_add(v_a_3888_, v___x_3904_);
lean_dec(v_a_3888_);
v_a_3888_ = v___x_3905_;
v_b_3889_ = v___x_3903_;
goto _start;
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec_ref(v_b_3889_);
lean_dec(v_a_3888_);
v_a_3907_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3901_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3901_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3915_, lean_object* v___x_3916_, lean_object* v___x_3917_, lean_object* v_a_3918_, lean_object* v_b_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3915_, v___x_3916_, v___x_3917_, v_a_3918_, v_b_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec_ref(v___x_3917_);
lean_dec_ref(v___x_3916_);
lean_dec(v_upperBound_3915_);
return v_res_3925_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3927_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3928_ = lean_unsigned_to_nat(8u);
v___x_3929_ = lean_unsigned_to_nat(281u);
v___x_3930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3931_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3932_ = l_mkPanicMessageWithDecl(v___x_3931_, v___x_3930_, v___x_3929_, v___x_3928_, v___x_3927_);
return v___x_3932_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3933_, lean_object* v_a_3934_, lean_object* v_b_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_a_3942_; uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_lt(v_a_3934_, v_upperBound_3933_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
lean_dec(v_a_3934_);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v_b_3935_);
return v___x_3947_;
}
else
{
lean_object* v_snd_3948_; lean_object* v_snd_3949_; lean_object* v_snd_3950_; lean_object* v_fst_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_4075_; 
v_snd_3948_ = lean_ctor_get(v_b_3935_, 1);
lean_inc(v_snd_3948_);
v_snd_3949_ = lean_ctor_get(v_snd_3948_, 1);
lean_inc(v_snd_3949_);
v_snd_3950_ = lean_ctor_get(v_snd_3949_, 1);
lean_inc(v_snd_3950_);
v_fst_3951_ = lean_ctor_get(v_b_3935_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_b_3935_);
if (v_isSharedCheck_4075_ == 0)
{
lean_object* v_unused_4076_; 
v_unused_4076_ = lean_ctor_get(v_b_3935_, 1);
lean_dec(v_unused_4076_);
v___x_3953_ = v_b_3935_;
v_isShared_3954_ = v_isSharedCheck_4075_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_fst_3951_);
lean_dec(v_b_3935_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_4075_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v_fst_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_4073_; 
v_fst_3955_ = lean_ctor_get(v_snd_3948_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_snd_3948_);
if (v_isSharedCheck_4073_ == 0)
{
lean_object* v_unused_4074_; 
v_unused_4074_ = lean_ctor_get(v_snd_3948_, 1);
lean_dec(v_unused_4074_);
v___x_3957_ = v_snd_3948_;
v_isShared_3958_ = v_isSharedCheck_4073_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_fst_3955_);
lean_dec(v_snd_3948_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_4073_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v_fst_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_4071_; 
v_fst_3959_ = lean_ctor_get(v_snd_3949_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v_snd_3949_);
if (v_isSharedCheck_4071_ == 0)
{
lean_object* v_unused_4072_; 
v_unused_4072_ = lean_ctor_get(v_snd_3949_, 1);
lean_dec(v_unused_4072_);
v___x_3961_ = v_snd_3949_;
v_isShared_3962_ = v_isSharedCheck_4071_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_fst_3959_);
lean_dec(v_snd_3949_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_4071_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v_array_3963_; lean_object* v_start_3964_; lean_object* v_stop_3965_; uint8_t v___x_3966_; 
v_array_3963_ = lean_ctor_get(v_snd_3950_, 0);
v_start_3964_ = lean_ctor_get(v_snd_3950_, 1);
v_stop_3965_ = lean_ctor_get(v_snd_3950_, 2);
v___x_3966_ = lean_nat_dec_lt(v_start_3964_, v_stop_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3968_; 
lean_dec(v_a_3934_);
if (v_isShared_3962_ == 0)
{
v___x_3968_ = v___x_3961_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_fst_3959_);
lean_ctor_set(v_reuseFailAlloc_3976_, 1, v_snd_3950_);
v___x_3968_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
lean_object* v___x_3970_; 
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 1, v___x_3968_);
v___x_3970_ = v___x_3957_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_fst_3955_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3968_);
v___x_3970_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v___x_3972_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 1, v___x_3970_);
v___x_3972_ = v___x_3953_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_fst_3951_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v___x_3970_);
v___x_3972_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
return v___x_3973_;
}
}
}
}
else
{
lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_4067_; 
lean_inc(v_stop_3965_);
lean_inc(v_start_3964_);
lean_inc_ref(v_array_3963_);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_snd_3950_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; lean_object* v_unused_4069_; lean_object* v_unused_4070_; 
v_unused_4068_ = lean_ctor_get(v_snd_3950_, 2);
lean_dec(v_unused_4068_);
v_unused_4069_ = lean_ctor_get(v_snd_3950_, 1);
lean_dec(v_unused_4069_);
v_unused_4070_ = lean_ctor_get(v_snd_3950_, 0);
lean_dec(v_unused_4070_);
v___x_3978_ = v_snd_3950_;
v_isShared_3979_ = v_isSharedCheck_4067_;
goto v_resetjp_3977_;
}
else
{
lean_dec(v_snd_3950_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_4067_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v_array_3980_; lean_object* v_start_3981_; lean_object* v_stop_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3987_; 
v_array_3980_ = lean_ctor_get(v_fst_3959_, 0);
v_start_3981_ = lean_ctor_get(v_fst_3959_, 1);
v_stop_3982_ = lean_ctor_get(v_fst_3959_, 2);
v___x_3983_ = lean_array_fget(v_array_3963_, v_start_3964_);
v___x_3984_ = lean_unsigned_to_nat(1u);
v___x_3985_ = lean_nat_add(v_start_3964_, v___x_3984_);
lean_dec(v_start_3964_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_3985_);
v___x_3987_ = v___x_3978_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_array_3963_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_4066_, 2, v_stop_3965_);
v___x_3987_ = v_reuseFailAlloc_4066_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_nat_dec_lt(v_start_3981_, v_stop_3982_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3990_; 
lean_dec(v___x_3983_);
lean_dec(v_a_3934_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v___x_3987_);
v___x_3990_ = v___x_3961_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_fst_3959_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v___x_3987_);
v___x_3990_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3992_; 
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 1, v___x_3990_);
v___x_3992_ = v___x_3957_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_fst_3955_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3994_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 1, v___x_3992_);
v___x_3994_ = v___x_3953_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_fst_3951_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
return v___x_3995_;
}
}
}
}
else
{
lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4062_; 
lean_inc(v_stop_3982_);
lean_inc(v_start_3981_);
lean_inc_ref(v_array_3980_);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_fst_3959_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; lean_object* v_unused_4064_; lean_object* v_unused_4065_; 
v_unused_4063_ = lean_ctor_get(v_fst_3959_, 2);
lean_dec(v_unused_4063_);
v_unused_4064_ = lean_ctor_get(v_fst_3959_, 1);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_fst_3959_, 0);
lean_dec(v_unused_4065_);
v___x_4000_ = v_fst_3959_;
v_isShared_4001_ = v_isSharedCheck_4062_;
goto v_resetjp_3999_;
}
else
{
lean_dec(v_fst_3959_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4062_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4002_; lean_object* v___x_4004_; 
v___x_4002_ = lean_nat_add(v_start_3981_, v___x_3984_);
lean_dec(v_start_3981_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 1, v___x_4002_);
v___x_4004_ = v___x_4000_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_array_3980_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v___x_4002_);
lean_ctor_set(v_reuseFailAlloc_4061_, 2, v_stop_3982_);
v___x_4004_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
if (lean_obj_tag(v___x_3983_) == 1)
{
lean_object* v_val_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4049_; 
v_val_4005_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4007_ = v___x_3983_;
v_isShared_4008_ = v_isSharedCheck_4049_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_val_4005_);
lean_dec(v___x_3983_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4049_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4009_ = lean_box(0);
v___x_4010_ = lean_unsigned_to_nat(0u);
v___x_4011_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4012_ = lean_array_get(v___x_4009_, v_val_4005_, v___x_4010_);
lean_dec(v_val_4005_);
lean_inc(v_a_3934_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v_a_3934_);
v___x_4014_ = v___x_4007_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_3934_);
v___x_4014_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
uint8_t v___x_4015_; 
v___x_4015_ = l_Option_instDecidableEq___redArg(v___x_4011_, v___x_4012_, v___x_4014_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_dec_ref(v___x_4004_);
lean_dec_ref(v___x_3987_);
lean_del_object(v___x_3961_);
lean_del_object(v___x_3957_);
lean_dec(v_fst_3955_);
lean_del_object(v___x_3953_);
lean_dec(v_fst_3951_);
v___x_4016_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4017_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4016_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4027_; 
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4020_ = v___x_4017_;
v_isShared_4021_ = v_isSharedCheck_4027_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4027_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
if (lean_obj_tag(v_a_4018_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; 
lean_dec(v_a_3934_);
v_a_4022_ = lean_ctor_get(v_a_4018_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v_a_4018_, 1);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v_a_4022_);
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
else
{
lean_object* v_a_4026_; 
lean_del_object(v___x_4020_);
v_a_4026_ = lean_ctor_get(v_a_4018_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v_a_4018_, 1);
v_a_3942_ = v_a_4026_;
goto v___jp_3941_;
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec(v_a_3934_);
v_a_4028_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4017_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4017_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
else
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
lean_inc(v_fst_3955_);
v___x_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_fst_3955_);
v___x_4037_ = lean_array_push(v_fst_3951_, v___x_4036_);
v___x_4038_ = lean_nat_add(v_fst_3955_, v___x_3984_);
lean_dec(v_fst_3955_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v___x_3987_);
lean_ctor_set(v___x_3961_, 0, v___x_4004_);
v___x_4040_ = v___x_3961_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_3987_);
v___x_4040_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
lean_object* v___x_4042_; 
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 1, v___x_4040_);
lean_ctor_set(v___x_3957_, 0, v___x_4038_);
v___x_4042_ = v___x_3957_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4044_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 1, v___x_4042_);
lean_ctor_set(v___x_3953_, 0, v___x_4037_);
v___x_4044_ = v___x_3953_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
v_a_3942_ = v___x_4044_;
goto v___jp_3941_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4053_; 
lean_dec(v___x_3983_);
v___x_4050_ = lean_box(0);
v___x_4051_ = lean_array_push(v_fst_3951_, v___x_4050_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v___x_3987_);
lean_ctor_set(v___x_3961_, 0, v___x_4004_);
v___x_4053_ = v___x_3961_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_3987_);
v___x_4053_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
lean_object* v___x_4055_; 
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 1, v___x_4053_);
v___x_4055_ = v___x_3957_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_fst_3955_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4057_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 1, v___x_4055_);
lean_ctor_set(v___x_3953_, 0, v___x_4051_);
v___x_4057_ = v___x_3953_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4051_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
v_a_3942_ = v___x_4057_;
goto v___jp_3941_;
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
v___jp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = lean_unsigned_to_nat(1u);
v___x_3944_ = lean_nat_add(v_a_3934_, v___x_3943_);
lean_dec(v_a_3934_);
v_a_3934_ = v___x_3944_;
v_b_3935_ = v_a_3942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4077_, lean_object* v_a_4078_, lean_object* v_b_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4077_, v_a_4078_, v_b_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v_upperBound_4077_);
return v_res_4085_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4087_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4088_ = lean_unsigned_to_nat(4u);
v___x_4089_ = lean_unsigned_to_nat(275u);
v___x_4090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4091_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4092_ = l_mkPanicMessageWithDecl(v___x_4091_, v___x_4090_, v___x_4089_, v___x_4088_, v___x_4087_);
return v___x_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4093_, lean_object* v___x_4094_, lean_object* v___x_4095_, lean_object* v_xs_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_graph_4103_; lean_object* v_revDeps_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4157_; 
v_graph_4103_ = lean_ctor_get(v_a_4093_, 0);
v_revDeps_4104_ = lean_ctor_get(v_a_4093_, 1);
v_isSharedCheck_4157_ = !lean_is_exclusive(v_a_4093_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4106_ = v_a_4093_;
v_isShared_4107_ = v_isSharedCheck_4157_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_revDeps_4104_);
lean_inc(v_graph_4103_);
lean_dec(v_a_4093_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4157_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; 
v___x_4108_ = lean_array_get_borrowed(v___x_4094_, v_graph_4103_, v___x_4095_);
v___x_4109_ = lean_array_get_size(v_xs_4096_);
v___x_4110_ = lean_array_get_size(v___x_4108_);
v___x_4111_ = lean_nat_dec_eq(v___x_4109_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_del_object(v___x_4106_);
lean_dec_ref(v_revDeps_4104_);
lean_dec_ref(v_graph_4103_);
lean_dec_ref(v_xs_4096_);
lean_dec(v___x_4095_);
v___x_4112_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4113_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4112_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
return v___x_4113_;
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4118_; 
v___x_4114_ = lean_mk_empty_array_with_capacity(v___x_4095_);
lean_inc_n(v___x_4095_, 2);
v___x_4115_ = l_Array_toSubarray___redArg(v_xs_4096_, v___x_4095_, v___x_4109_);
lean_inc(v___x_4108_);
v___x_4116_ = l_Array_toSubarray___redArg(v___x_4108_, v___x_4095_, v___x_4110_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 1, v___x_4116_);
lean_ctor_set(v___x_4106_, 0, v___x_4115_);
v___x_4118_ = v___x_4106_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4115_);
lean_ctor_set(v_reuseFailAlloc_4156_, 1, v___x_4116_);
v___x_4118_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
lean_inc(v___x_4095_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4095_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4114_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4109_, v___x_4095_, v___x_4120_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v_snd_4123_; lean_object* v_fst_4124_; lean_object* v_fst_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_a_4122_);
lean_dec_ref_known(v___x_4121_, 1);
v_snd_4123_ = lean_ctor_get(v_a_4122_, 1);
lean_inc(v_snd_4123_);
v_fst_4124_ = lean_ctor_get(v_a_4122_, 0);
lean_inc_n(v_fst_4124_, 2);
lean_dec(v_a_4122_);
v_fst_4125_ = lean_ctor_get(v_snd_4123_, 0);
lean_inc(v_fst_4125_);
lean_dec(v_snd_4123_);
v___x_4126_ = lean_unsigned_to_nat(1u);
v___x_4127_ = lean_array_get_size(v_graph_4103_);
v___x_4128_ = lean_mk_empty_array_with_capacity(v___x_4126_);
v___x_4129_ = lean_array_push(v___x_4128_, v_fst_4124_);
v___x_4130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4127_, v_graph_4103_, v_fst_4124_, v___x_4126_, v___x_4129_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v_fst_4124_);
lean_dec_ref(v_graph_4103_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4139_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4133_ = v___x_4130_;
v_isShared_4134_ = v_isSharedCheck_4139_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4130_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4139_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; lean_object* v___x_4137_; 
v___x_4135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4135_, 0, v_fst_4125_);
lean_ctor_set(v___x_4135_, 1, v_a_4131_);
lean_ctor_set(v___x_4135_, 2, v_revDeps_4104_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4135_);
v___x_4137_ = v___x_4133_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4147_; 
lean_dec(v_fst_4125_);
lean_dec_ref(v_revDeps_4104_);
v_a_4140_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4142_ = v___x_4130_;
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v___x_4130_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4147_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4145_; 
if (v_isShared_4143_ == 0)
{
v___x_4145_ = v___x_4142_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4155_; 
lean_dec_ref(v_revDeps_4104_);
lean_dec_ref(v_graph_4103_);
v_a_4148_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4150_ = v___x_4121_;
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4121_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4155_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4158_, lean_object* v___x_4159_, lean_object* v___x_4160_, lean_object* v_xs_4161_, lean_object* v_x_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4158_, v___x_4159_, v___x_4160_, v_xs_4161_, v_x_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec_ref(v_x_4162_);
lean_dec_ref(v___x_4159_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v___x_4175_; 
lean_inc_ref(v_preDefs_4169_);
v___x_4175_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v_value_4180_; lean_object* v___x_4181_; lean_object* v___f_4182_; uint8_t v___x_4183_; lean_object* v___x_4184_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4175_, 1);
v___x_4177_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4178_ = lean_unsigned_to_nat(0u);
v___x_4179_ = lean_array_get(v___x_4177_, v_preDefs_4169_, v___x_4178_);
lean_dec_ref(v_preDefs_4169_);
v_value_4180_ = lean_ctor_get(v___x_4179_, 7);
lean_inc_ref(v_value_4180_);
lean_dec(v___x_4179_);
v___x_4181_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4182_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4182_, 0, v_a_4176_);
lean_closure_set(v___f_4182_, 1, v___x_4181_);
lean_closure_set(v___f_4182_, 2, v___x_4178_);
v___x_4183_ = 0;
v___x_4184_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4180_, v___f_4182_, v___x_4183_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
return v___x_4184_;
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec_ref(v_preDefs_4169_);
v_a_4185_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4175_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4175_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4200_, lean_object* v___x_4201_, lean_object* v___x_4202_, lean_object* v_inst_4203_, lean_object* v_R_4204_, lean_object* v_a_4205_, lean_object* v_b_4206_, lean_object* v_c_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4200_, v___x_4201_, v___x_4202_, v_a_4205_, v_b_4206_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4214_, lean_object* v___x_4215_, lean_object* v___x_4216_, lean_object* v_inst_4217_, lean_object* v_R_4218_, lean_object* v_a_4219_, lean_object* v_b_4220_, lean_object* v_c_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4214_, v___x_4215_, v___x_4216_, v_inst_4217_, v_R_4218_, v_a_4219_, v_b_4220_, v_c_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec_ref(v___x_4216_);
lean_dec_ref(v___x_4215_);
lean_dec(v_upperBound_4214_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4228_, lean_object* v_inst_4229_, lean_object* v_R_4230_, lean_object* v_a_4231_, lean_object* v_b_4232_, lean_object* v_c_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4228_, v_a_4231_, v_b_4232_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4240_, lean_object* v_inst_4241_, lean_object* v_R_4242_, lean_object* v_a_4243_, lean_object* v_b_4244_, lean_object* v_c_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4240_, v_inst_4241_, v_R_4242_, v_a_4243_, v_b_4244_, v_c_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v_upperBound_4240_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4252_, size_t v_i_4253_, size_t v_stop_4254_, lean_object* v_b_4255_){
_start:
{
uint8_t v___x_4256_; 
v___x_4256_ = lean_usize_dec_eq(v_i_4253_, v_stop_4254_);
if (v___x_4256_ == 0)
{
size_t v___x_4257_; size_t v___x_4258_; lean_object* v___x_4259_; 
v___x_4257_ = ((size_t)1ULL);
v___x_4258_ = lean_usize_sub(v_i_4253_, v___x_4257_);
v___x_4259_ = lean_array_uget_borrowed(v_as_4252_, v___x_4258_);
if (lean_obj_tag(v___x_4259_) == 0)
{
v_i_4253_ = v___x_4258_;
goto _start;
}
else
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4261_ = lean_unsigned_to_nat(1u);
v___x_4262_ = lean_nat_add(v_b_4255_, v___x_4261_);
lean_dec(v_b_4255_);
v_i_4253_ = v___x_4258_;
v_b_4255_ = v___x_4262_;
goto _start;
}
}
else
{
return v_b_4255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4264_, lean_object* v_i_4265_, lean_object* v_stop_4266_, lean_object* v_b_4267_){
_start:
{
size_t v_i_boxed_4268_; size_t v_stop_boxed_4269_; lean_object* v_res_4270_; 
v_i_boxed_4268_ = lean_unbox_usize(v_i_4265_);
lean_dec(v_i_4265_);
v_stop_boxed_4269_ = lean_unbox_usize(v_stop_4266_);
lean_dec(v_stop_4266_);
v_res_4270_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4264_, v_i_boxed_4268_, v_stop_boxed_4269_, v_b_4267_);
lean_dec_ref(v_as_4264_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4271_){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; 
v___x_4272_ = lean_unsigned_to_nat(0u);
v___x_4273_ = lean_array_get_size(v_perm_4271_);
v___x_4274_ = lean_nat_dec_lt(v___x_4272_, v___x_4273_);
if (v___x_4274_ == 0)
{
return v___x_4272_;
}
else
{
size_t v___x_4275_; size_t v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = lean_usize_of_nat(v___x_4273_);
v___x_4276_ = ((size_t)0ULL);
v___x_4277_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4271_, v___x_4275_, v___x_4276_, v___x_4272_);
return v___x_4277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4278_);
lean_dec_ref(v_perm_4278_);
return v_res_4279_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4280_, lean_object* v_i_4281_){
_start:
{
lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4282_ = lean_array_get_size(v_perm_4280_);
v___x_4283_ = lean_nat_dec_lt(v_i_4281_, v___x_4282_);
if (v___x_4283_ == 0)
{
return v___x_4283_;
}
else
{
lean_object* v___x_4284_; 
v___x_4284_ = lean_array_fget_borrowed(v_perm_4280_, v_i_4281_);
if (lean_obj_tag(v___x_4284_) == 0)
{
uint8_t v___x_4285_; 
v___x_4285_ = 0;
return v___x_4285_;
}
else
{
return v___x_4283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4286_, lean_object* v_i_4287_){
_start:
{
uint8_t v_res_4288_; lean_object* v_r_4289_; 
v_res_4288_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4286_, v_i_4287_);
lean_dec(v_i_4287_);
lean_dec_ref(v_perm_4286_);
v_r_4289_ = lean_box(v_res_4288_);
return v_r_4289_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v___f_4296_; lean_object* v___x_907__overap_4297_; lean_object* v___x_4298_; 
v___f_4296_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_907__overap_4297_ = lean_panic_fn_borrowed(v___f_4296_, v_msg_4290_);
lean_inc(v___y_4294_);
lean_inc_ref(v___y_4293_);
lean_inc(v___y_4292_);
lean_inc_ref(v___y_4291_);
v___x_4298_ = lean_apply_5(v___x_907__overap_4297_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, lean_box(0));
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4306_, lean_object* v_msg_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4314_, lean_object* v_msg_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4314_, v_msg_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4322_, lean_object* v_maxFVars_x3f_4323_, lean_object* v_k_4324_, uint8_t v_cleanupAnnotations_4325_, uint8_t v_whnfType_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v___f_4332_; lean_object* v___x_4333_; 
v___f_4332_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4332_, 0, v_k_4324_);
v___x_4333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4322_, v_maxFVars_x3f_4323_, v___f_4332_, v_cleanupAnnotations_4325_, v_whnfType_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
v_a_4342_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4333_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4333_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4350_, lean_object* v_maxFVars_x3f_4351_, lean_object* v_k_4352_, lean_object* v_cleanupAnnotations_4353_, lean_object* v_whnfType_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4360_; uint8_t v_whnfType_boxed_4361_; lean_object* v_res_4362_; 
v_cleanupAnnotations_boxed_4360_ = lean_unbox(v_cleanupAnnotations_4353_);
v_whnfType_boxed_4361_ = lean_unbox(v_whnfType_4354_);
v_res_4362_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4350_, v_maxFVars_x3f_4351_, v_k_4352_, v_cleanupAnnotations_boxed_4360_, v_whnfType_boxed_4361_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4363_, lean_object* v_type_4364_, lean_object* v_maxFVars_x3f_4365_, lean_object* v_k_4366_, uint8_t v_cleanupAnnotations_4367_, uint8_t v_whnfType_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4364_, v_maxFVars_x3f_4365_, v_k_4366_, v_cleanupAnnotations_4367_, v_whnfType_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4375_, lean_object* v_type_4376_, lean_object* v_maxFVars_x3f_4377_, lean_object* v_k_4378_, lean_object* v_cleanupAnnotations_4379_, lean_object* v_whnfType_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4386_; uint8_t v_whnfType_boxed_4387_; lean_object* v_res_4388_; 
v_cleanupAnnotations_boxed_4386_ = lean_unbox(v_cleanupAnnotations_4379_);
v_whnfType_boxed_4387_ = lean_unbox(v_whnfType_4380_);
v_res_4388_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4375_, v_type_4376_, v_maxFVars_x3f_4377_, v_k_4378_, v_cleanupAnnotations_boxed_4386_, v_whnfType_boxed_4387_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
return v_res_4388_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4391_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4392_ = lean_unsigned_to_nat(6u);
v___x_4393_ = lean_unsigned_to_nat(329u);
v___x_4394_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4395_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4396_ = l_mkPanicMessageWithDecl(v___x_4395_, v___x_4394_, v___x_4393_, v___x_4392_, v___x_4391_);
return v___x_4396_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4400_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4401_ = lean_unsigned_to_nat(8u);
v___x_4402_ = lean_unsigned_to_nat(322u);
v___x_4403_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4404_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4405_ = l_mkPanicMessageWithDecl(v___x_4404_, v___x_4403_, v___x_4402_, v___x_4401_, v___x_4400_);
return v___x_4405_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4407_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4408_ = lean_unsigned_to_nat(8u);
v___x_4409_ = lean_unsigned_to_nat(325u);
v___x_4410_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4411_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4412_ = l_mkPanicMessageWithDecl(v___x_4411_, v___x_4410_, v___x_4409_, v___x_4408_, v___x_4407_);
return v___x_4412_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4414_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4415_ = lean_unsigned_to_nat(8u);
v___x_4416_ = lean_unsigned_to_nat(324u);
v___x_4417_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4418_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4419_ = l_mkPanicMessageWithDecl(v___x_4418_, v___x_4417_, v___x_4416_, v___x_4415_, v___x_4414_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4420_, lean_object* v___x_4421_, lean_object* v_xs_4422_, lean_object* v_val_4423_, lean_object* v_i_4424_, lean_object* v_perm_4425_, lean_object* v_k_4426_, lean_object* v_xs_x27_4427_, lean_object* v_type_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4434_ = lean_array_get_size(v_xs_x27_4427_);
v___x_4435_ = lean_nat_dec_eq(v___x_4434_, v___x_4420_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
lean_dec_ref(v_type_4428_);
lean_dec_ref(v_k_4426_);
lean_dec_ref(v_perm_4425_);
lean_dec_ref(v_xs_4422_);
v___x_4436_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4437_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4436_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4437_;
}
else
{
lean_object* v___x_4438_; lean_object* v_x_4439_; lean_object* v___x_4440_; 
v___x_4438_ = lean_unsigned_to_nat(0u);
v_x_4439_ = lean_array_get_borrowed(v___x_4421_, v_xs_x27_4427_, v___x_4438_);
lean_inc(v___y_4432_);
lean_inc_ref(v___y_4431_);
lean_inc(v___y_4430_);
lean_inc_ref(v___y_4429_);
lean_inc(v_x_4439_);
v___x_4440_ = lean_infer_type(v_x_4439_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; uint8_t v___x_4442_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v___x_4442_ = l_Lean_Expr_hasLooseBVars(v_a_4441_);
lean_dec(v_a_4441_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; uint8_t v___x_4444_; 
v___x_4443_ = lean_array_get_size(v_xs_4422_);
v___x_4444_ = lean_nat_dec_lt(v_val_4423_, v___x_4443_);
if (v___x_4444_ == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
lean_dec_ref(v_type_4428_);
lean_dec_ref(v_k_4426_);
lean_dec_ref(v_perm_4425_);
lean_dec_ref(v_xs_4422_);
v___x_4445_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4446_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4445_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4446_;
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4447_ = lean_nat_add(v_i_4424_, v___x_4420_);
lean_inc(v_x_4439_);
v___x_4448_ = lean_array_set(v_xs_4422_, v_val_4423_, v_x_4439_);
v___x_4449_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4425_, v_k_4426_, v___x_4447_, v_type_4428_, v___x_4448_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4449_;
}
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_dec_ref(v_type_4428_);
lean_dec_ref(v_k_4426_);
lean_dec_ref(v_perm_4425_);
lean_dec_ref(v_xs_4422_);
v___x_4450_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4451_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4450_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
return v___x_4451_;
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec_ref(v_type_4428_);
lean_dec_ref(v_k_4426_);
lean_dec_ref(v_perm_4425_);
lean_dec_ref(v_xs_4422_);
v_a_4452_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4440_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4440_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4460_, lean_object* v___x_4461_, lean_object* v_xs_4462_, lean_object* v_val_4463_, lean_object* v_i_4464_, lean_object* v_perm_4465_, lean_object* v_k_4466_, lean_object* v_xs_x27_4467_, lean_object* v_type_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4460_, v___x_4461_, v_xs_4462_, v_val_4463_, v_i_4464_, v_perm_4465_, v_k_4466_, v_xs_x27_4467_, v_type_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec_ref(v_xs_x27_4467_);
lean_dec(v_i_4464_);
lean_dec(v_val_4463_);
lean_dec_ref(v___x_4461_);
lean_dec(v___x_4460_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4475_, lean_object* v_k_4476_, lean_object* v_i_4477_, lean_object* v_type_4478_, lean_object* v_xs_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_){
_start:
{
lean_object* v___x_4485_; uint8_t v___x_4486_; 
v___x_4485_ = lean_array_get_size(v_perm_4475_);
v___x_4486_ = lean_nat_dec_lt(v_i_4477_, v___x_4485_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; 
lean_dec_ref(v_type_4478_);
lean_dec(v_i_4477_);
lean_dec_ref(v_perm_4475_);
lean_inc(v_a_4483_);
lean_inc_ref(v_a_4482_);
lean_inc(v_a_4481_);
lean_inc_ref(v_a_4480_);
v___x_4487_ = lean_apply_6(v_k_4476_, v_xs_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, lean_box(0));
return v___x_4487_;
}
else
{
lean_object* v___x_4488_; 
v___x_4488_ = lean_array_fget_borrowed(v_perm_4475_, v_i_4477_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v___x_4489_; 
lean_inc(v_a_4483_);
lean_inc_ref(v_a_4482_);
lean_inc(v_a_4481_);
lean_inc_ref(v_a_4480_);
v___x_4489_ = lean_whnf(v_type_4478_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; uint8_t v___x_4491_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___x_4491_ = l_Lean_Expr_isForall(v_a_4490_);
if (v___x_4491_ == 0)
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
lean_dec(v_a_4490_);
lean_dec_ref(v_xs_4479_);
lean_dec(v_i_4477_);
lean_dec_ref(v_k_4476_);
lean_dec_ref(v_perm_4475_);
v___x_4492_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4493_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4492_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_);
return v___x_4493_;
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = lean_unsigned_to_nat(1u);
v___x_4495_ = lean_nat_add(v_i_4477_, v___x_4494_);
lean_dec(v_i_4477_);
v___x_4496_ = l_Lean_Expr_bindingBody_x21(v_a_4490_);
lean_dec(v_a_4490_);
v_i_4477_ = v___x_4495_;
v_type_4478_ = v___x_4496_;
goto _start;
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec_ref(v_xs_4479_);
lean_dec(v_i_4477_);
lean_dec_ref(v_k_4476_);
lean_dec_ref(v_perm_4475_);
v_a_4498_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4489_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4489_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
else
{
lean_object* v_val_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___f_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; lean_object* v___x_4512_; 
v_val_4506_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_val_4506_);
v___x_4507_ = l_Lean_instInhabitedExpr;
v___x_4508_ = lean_unsigned_to_nat(1u);
v___f_4509_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4509_, 0, v___x_4508_);
lean_closure_set(v___f_4509_, 1, v___x_4507_);
lean_closure_set(v___f_4509_, 2, v_xs_4479_);
lean_closure_set(v___f_4509_, 3, v_val_4506_);
lean_closure_set(v___f_4509_, 4, v_i_4477_);
lean_closure_set(v___f_4509_, 5, v_perm_4475_);
lean_closure_set(v___f_4509_, 6, v_k_4476_);
v___x_4510_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4511_ = 0;
v___x_4512_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4478_, v___x_4510_, v___f_4509_, v___x_4486_, v___x_4511_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_);
return v___x_4512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4513_, lean_object* v_k_4514_, lean_object* v_i_4515_, lean_object* v_type_4516_, lean_object* v_xs_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4513_, v_k_4514_, v_i_4515_, v_type_4516_, v_xs_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4524_, lean_object* v_perm_4525_, lean_object* v_k_4526_, lean_object* v_i_4527_, lean_object* v_type_4528_, lean_object* v_xs_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4525_, v_k_4526_, v_i_4527_, v_type_4528_, v_xs_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
return v___x_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4536_, lean_object* v_perm_4537_, lean_object* v_k_4538_, lean_object* v_i_4539_, lean_object* v_type_4540_, lean_object* v_xs_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4536_, v_perm_4537_, v_k_4538_, v_i_4539_, v_type_4540_, v_xs_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
return v_res_4547_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = lean_unsigned_to_nat(0u);
v___x_4549_ = l_Lean_Level_ofNat(v___x_4548_);
return v___x_4549_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
v___x_4550_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4551_ = l_Lean_mkSort(v___x_4550_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4552_, lean_object* v_type_4553_, lean_object* v_k_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4560_ = lean_unsigned_to_nat(0u);
v___x_4561_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4552_);
v___x_4562_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4563_ = lean_mk_array(v___x_4561_, v___x_4562_);
v___x_4564_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4552_, v_k_4554_, v___x_4560_, v_type_4553_, v___x_4563_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4565_, lean_object* v_type_4566_, lean_object* v_k_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4565_, v_type_4566_, v_k_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
lean_dec(v_a_4571_);
lean_dec_ref(v_a_4570_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4574_, lean_object* v_perm_4575_, lean_object* v_type_4576_, lean_object* v_k_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v___x_4583_; 
v___x_4583_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4575_, v_type_4576_, v_k_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4584_, lean_object* v_perm_4585_, lean_object* v_type_4586_, lean_object* v_k_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4584_, v_perm_4585_, v_type_4586_, v_k_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4594_, lean_object* v_runInBase_4595_, lean_object* v_b_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = lean_apply_1(v_k_4594_, v_b_4596_);
lean_inc(v___y_4600_);
lean_inc_ref(v___y_4599_);
lean_inc(v___y_4598_);
lean_inc_ref(v___y_4597_);
v___x_4603_ = lean_apply_7(v_runInBase_4595_, lean_box(0), v___x_4602_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, lean_box(0));
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4604_, lean_object* v_runInBase_4605_, lean_object* v_b_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4604_, v_runInBase_4605_, v_b_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4613_, lean_object* v_perm_4614_, lean_object* v_type_4615_, lean_object* v_runInBase_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v___f_4622_; lean_object* v___x_4623_; 
v___f_4622_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4622_, 0, v_k_4613_);
lean_closure_set(v___f_4622_, 1, v_runInBase_4616_);
v___x_4623_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4614_, v_type_4615_, v___f_4622_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4624_, lean_object* v_perm_4625_, lean_object* v_type_4626_, lean_object* v_runInBase_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4624_, v_perm_4625_, v_type_4626_, v_runInBase_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4634_, lean_object* v_inst_4635_, lean_object* v_perm_4636_, lean_object* v_type_4637_, lean_object* v_k_4638_){
_start:
{
lean_object* v_toBind_4639_; lean_object* v_liftWith_4640_; lean_object* v_restoreM_4641_; lean_object* v___f_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v_toBind_4639_ = lean_ctor_get(v_inst_4635_, 1);
lean_inc(v_toBind_4639_);
lean_dec_ref(v_inst_4635_);
v_liftWith_4640_ = lean_ctor_get(v_inst_4634_, 0);
lean_inc(v_liftWith_4640_);
v_restoreM_4641_ = lean_ctor_get(v_inst_4634_, 1);
lean_inc(v_restoreM_4641_);
lean_dec_ref(v_inst_4634_);
v___f_4642_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4642_, 0, v_k_4638_);
lean_closure_set(v___f_4642_, 1, v_perm_4636_);
lean_closure_set(v___f_4642_, 2, v_type_4637_);
v___x_4643_ = lean_apply_2(v_liftWith_4640_, lean_box(0), v___f_4642_);
v___x_4644_ = lean_apply_1(v_restoreM_4641_, lean_box(0));
v___x_4645_ = lean_apply_4(v_toBind_4639_, lean_box(0), lean_box(0), v___x_4643_, v___x_4644_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4646_, lean_object* v_00_u03b1_4647_, lean_object* v_inst_4648_, lean_object* v_inst_4649_, lean_object* v_perm_4650_, lean_object* v_type_4651_, lean_object* v_k_4652_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4648_, v_inst_4649_, v_perm_4650_, v_type_4651_, v_k_4652_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v___f_4660_; lean_object* v___x_598__overap_4661_; lean_object* v___x_4662_; 
v___f_4660_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_598__overap_4661_ = lean_panic_fn_borrowed(v___f_4660_, v_msg_4654_);
lean_inc(v___y_4658_);
lean_inc_ref(v___y_4657_);
lean_inc(v___y_4656_);
lean_inc_ref(v___y_4655_);
v___x_4662_ = lean_apply_5(v___x_598__overap_4661_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, lean_box(0));
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
return v_res_4669_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4672_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4673_ = lean_unsigned_to_nat(10u);
v___x_4674_ = lean_unsigned_to_nat(353u);
v___x_4675_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4676_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4677_ = l_mkPanicMessageWithDecl(v___x_4676_, v___x_4675_, v___x_4674_, v___x_4673_, v___x_4672_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4678_, lean_object* v_xs_4679_, lean_object* v_tail_4680_, lean_object* v_ys_4681_, lean_object* v_type_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4678_, v_xs_4679_, v_tail_4680_, v_ys_4681_, v_type_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec_ref(v_ys_4681_);
lean_dec(v___x_4678_);
return v_res_4688_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4689_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4690_ = lean_unsigned_to_nat(8u);
v___x_4691_ = lean_unsigned_to_nat(349u);
v___x_4692_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4693_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4694_ = l_mkPanicMessageWithDecl(v___x_4693_, v___x_4692_, v___x_4691_, v___x_4690_, v___x_4689_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4695_, lean_object* v_x_4696_, lean_object* v_x_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_){
_start:
{
if (lean_obj_tag(v_x_4696_) == 0)
{
lean_object* v___x_4703_; 
lean_dec_ref(v_xs_4695_);
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v_x_4697_);
return v___x_4703_;
}
else
{
lean_object* v_head_4704_; 
v_head_4704_ = lean_ctor_get(v_x_4696_, 0);
if (lean_obj_tag(v_head_4704_) == 0)
{
lean_object* v_tail_4705_; lean_object* v___x_4706_; lean_object* v___f_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; lean_object* v___x_4710_; 
v_tail_4705_ = lean_ctor_get(v_x_4696_, 1);
lean_inc(v_tail_4705_);
lean_dec_ref_known(v_x_4696_, 2);
v___x_4706_ = lean_unsigned_to_nat(1u);
v___f_4707_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4707_, 0, v___x_4706_);
lean_closure_set(v___f_4707_, 1, v_xs_4695_);
lean_closure_set(v___f_4707_, 2, v_tail_4705_);
v___x_4708_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4709_ = 0;
v___x_4710_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4697_, v___x_4708_, v___f_4707_, v___x_4709_, v___x_4709_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
return v___x_4710_;
}
else
{
lean_object* v_tail_4711_; lean_object* v_val_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
lean_inc_ref(v_head_4704_);
v_tail_4711_ = lean_ctor_get(v_x_4696_, 1);
lean_inc(v_tail_4711_);
lean_dec_ref_known(v_x_4696_, 2);
v_val_4712_ = lean_ctor_get(v_head_4704_, 0);
lean_inc(v_val_4712_);
lean_dec_ref_known(v_head_4704_, 1);
v___x_4713_ = lean_array_get_size(v_xs_4695_);
v___x_4714_ = lean_nat_dec_lt(v_val_4712_, v___x_4713_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4715_; lean_object* v___x_4716_; 
lean_dec(v_val_4712_);
lean_dec(v_tail_4711_);
lean_dec_ref(v_x_4697_);
lean_dec_ref(v_xs_4695_);
v___x_4715_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4716_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4715_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
return v___x_4716_;
}
else
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4717_ = l_Lean_instInhabitedExpr;
v___x_4718_ = lean_array_get_borrowed(v___x_4717_, v_xs_4695_, v_val_4712_);
lean_dec(v_val_4712_);
v___x_4719_ = lean_unsigned_to_nat(1u);
v___x_4720_ = lean_mk_empty_array_with_capacity(v___x_4719_);
lean_inc(v___x_4718_);
v___x_4721_ = lean_array_push(v___x_4720_, v___x_4718_);
v___x_4722_ = l_Lean_Meta_instantiateForall(v_x_4697_, v___x_4721_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
lean_dec_ref(v___x_4721_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4722_, 1);
v_x_4696_ = v_tail_4711_;
v_x_4697_ = v_a_4723_;
goto _start;
}
else
{
lean_dec(v_tail_4711_);
lean_dec_ref(v_xs_4695_);
return v___x_4722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4725_, lean_object* v_xs_4726_, lean_object* v_tail_4727_, lean_object* v_ys_4728_, lean_object* v_type_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v___x_4735_; uint8_t v___x_4736_; 
v___x_4735_ = lean_array_get_size(v_ys_4728_);
v___x_4736_ = lean_nat_dec_eq(v___x_4735_, v___x_4725_);
if (v___x_4736_ == 0)
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
lean_dec_ref(v_type_4729_);
lean_dec(v_tail_4727_);
lean_dec_ref(v_xs_4726_);
v___x_4737_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4738_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4737_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
return v___x_4738_;
}
else
{
lean_object* v___x_4739_; 
v___x_4739_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4726_, v_tail_4727_, v_type_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; uint8_t v___x_4741_; uint8_t v___x_4742_; lean_object* v___x_4743_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
lean_inc(v_a_4740_);
lean_dec_ref_known(v___x_4739_, 1);
v___x_4741_ = 0;
v___x_4742_ = 1;
v___x_4743_ = l_Lean_Meta_mkForallFVars(v_ys_4728_, v_a_4740_, v___x_4741_, v___x_4736_, v___x_4736_, v___x_4742_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
return v___x_4743_;
}
else
{
return v___x_4739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4744_, lean_object* v_x_4745_, lean_object* v_x_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4744_, v_x_4745_, v_x_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec_ref(v_a_4747_);
return v_res_4752_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4755_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4756_ = lean_unsigned_to_nat(2u);
v___x_4757_ = lean_unsigned_to_nat(343u);
v___x_4758_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4759_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4760_ = l_mkPanicMessageWithDecl(v___x_4759_, v___x_4758_, v___x_4757_, v___x_4756_, v___x_4755_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4761_, lean_object* v_type_u2080_4762_, lean_object* v_xs_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___x_4769_; lean_object* v___x_4770_; uint8_t v___x_4771_; 
v___x_4769_ = lean_array_get_size(v_xs_4763_);
v___x_4770_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4761_);
v___x_4771_ = lean_nat_dec_eq(v___x_4769_, v___x_4770_);
lean_dec(v___x_4770_);
if (v___x_4771_ == 0)
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
lean_dec_ref(v_xs_4763_);
lean_dec_ref(v_type_u2080_4762_);
lean_dec_ref(v_perm_4761_);
v___x_4772_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4773_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4772_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
return v___x_4773_;
}
else
{
lean_object* v_mask_4774_; lean_object* v___x_4775_; 
v_mask_4774_ = lean_array_to_list(v_perm_4761_);
v___x_4775_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4763_, v_mask_4774_, v_type_u2080_4762_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
return v___x_4775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4776_, lean_object* v_type_u2080_4777_, lean_object* v_xs_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4776_, v_type_u2080_4777_, v_xs_4778_, v_a_4779_, v_a_4780_, v_a_4781_, v_a_4782_);
lean_dec(v_a_4782_);
lean_dec_ref(v_a_4781_);
lean_dec(v_a_4780_);
lean_dec_ref(v_a_4779_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4785_, lean_object* v_maxFVars_4786_, lean_object* v_k_4787_, uint8_t v_cleanupAnnotations_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___f_4794_; uint8_t v___x_4795_; uint8_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___f_4794_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4794_, 0, v_k_4787_);
v___x_4795_ = 1;
v___x_4796_ = 0;
v___x_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4797_, 0, v_maxFVars_4786_);
v___x_4798_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4785_, v___x_4795_, v___x_4796_, v___x_4795_, v___x_4796_, v___x_4797_, v___f_4794_, v_cleanupAnnotations_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec_ref_known(v___x_4797_, 1);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4798_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4798_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
v_a_4807_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4798_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4798_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4815_, lean_object* v_maxFVars_4816_, lean_object* v_k_4817_, lean_object* v_cleanupAnnotations_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4824_; lean_object* v_res_4825_; 
v_cleanupAnnotations_boxed_4824_ = lean_unbox(v_cleanupAnnotations_4818_);
v_res_4825_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4815_, v_maxFVars_4816_, v_k_4817_, v_cleanupAnnotations_boxed_4824_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4826_, lean_object* v_e_4827_, lean_object* v_maxFVars_4828_, lean_object* v_k_4829_, uint8_t v_cleanupAnnotations_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4827_, v_maxFVars_4828_, v_k_4829_, v_cleanupAnnotations_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4837_, lean_object* v_e_4838_, lean_object* v_maxFVars_4839_, lean_object* v_k_4840_, lean_object* v_cleanupAnnotations_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4847_; lean_object* v_res_4848_; 
v_cleanupAnnotations_boxed_4847_ = lean_unbox(v_cleanupAnnotations_4841_);
v_res_4848_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4837_, v_e_4838_, v_maxFVars_4839_, v_k_4840_, v_cleanupAnnotations_boxed_4847_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
return v_res_4848_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4849_){
_start:
{
if (lean_obj_tag(v_x_4849_) == 0)
{
uint8_t v___x_4850_; 
v___x_4850_ = 1;
return v___x_4850_;
}
else
{
lean_object* v_head_4851_; 
v_head_4851_ = lean_ctor_get(v_x_4849_, 0);
if (lean_obj_tag(v_head_4851_) == 0)
{
lean_object* v_tail_4852_; 
v_tail_4852_ = lean_ctor_get(v_x_4849_, 1);
v_x_4849_ = v_tail_4852_;
goto _start;
}
else
{
uint8_t v___x_4854_; 
v___x_4854_ = 0;
return v___x_4854_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4855_){
_start:
{
uint8_t v_res_4856_; lean_object* v_r_4857_; 
v_res_4856_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4855_);
lean_dec(v_x_4855_);
v_r_4857_ = lean_box(v_res_4856_);
return v_r_4857_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4860_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4861_ = lean_unsigned_to_nat(12u);
v___x_4862_ = lean_unsigned_to_nat(376u);
v___x_4863_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4864_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4865_ = l_mkPanicMessageWithDecl(v___x_4864_, v___x_4863_, v___x_4862_, v___x_4861_, v___x_4860_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4866_, lean_object* v_xs_4867_, lean_object* v_tail_4868_, lean_object* v___x_4869_, lean_object* v___x_4870_, lean_object* v_ys_4871_, lean_object* v_value_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
uint8_t v___x_1213__boxed_4878_; uint8_t v___x_1214__boxed_4879_; lean_object* v_res_4880_; 
v___x_1213__boxed_4878_ = lean_unbox(v___x_4869_);
v___x_1214__boxed_4879_ = lean_unbox(v___x_4870_);
v_res_4880_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4866_, v_xs_4867_, v_tail_4868_, v___x_1213__boxed_4878_, v___x_1214__boxed_4879_, v_ys_4871_, v_value_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec_ref(v_ys_4871_);
lean_dec(v___x_4866_);
return v_res_4880_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4881_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4882_ = lean_unsigned_to_nat(8u);
v___x_4883_ = lean_unsigned_to_nat(368u);
v___x_4884_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4885_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4886_ = l_mkPanicMessageWithDecl(v___x_4885_, v___x_4884_, v___x_4883_, v___x_4882_, v___x_4881_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4887_, lean_object* v_x_4888_, lean_object* v_x_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
if (lean_obj_tag(v_x_4888_) == 0)
{
lean_object* v___x_4895_; 
lean_dec_ref(v_xs_4887_);
v___x_4895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4895_, 0, v_x_4889_);
return v___x_4895_;
}
else
{
lean_object* v_head_4896_; 
v_head_4896_ = lean_ctor_get(v_x_4888_, 0);
if (lean_obj_tag(v_head_4896_) == 0)
{
lean_object* v_tail_4897_; uint8_t v___x_4898_; 
v_tail_4897_ = lean_ctor_get(v_x_4888_, 1);
lean_inc(v_tail_4897_);
lean_dec_ref_known(v_x_4888_, 2);
v___x_4898_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4897_);
if (v___x_4898_ == 0)
{
uint8_t v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___f_4903_; lean_object* v___x_4904_; 
v___x_4899_ = 1;
v___x_4900_ = lean_unsigned_to_nat(1u);
v___x_4901_ = lean_box(v___x_4898_);
v___x_4902_ = lean_box(v___x_4899_);
v___f_4903_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4903_, 0, v___x_4900_);
lean_closure_set(v___f_4903_, 1, v_xs_4887_);
lean_closure_set(v___f_4903_, 2, v_tail_4897_);
lean_closure_set(v___f_4903_, 3, v___x_4901_);
lean_closure_set(v___f_4903_, 4, v___x_4902_);
v___x_4904_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4889_, v___x_4900_, v___f_4903_, v___x_4898_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
return v___x_4904_;
}
else
{
lean_object* v___x_4905_; 
lean_dec(v_tail_4897_);
lean_dec_ref(v_xs_4887_);
v___x_4905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4905_, 0, v_x_4889_);
return v___x_4905_;
}
}
else
{
lean_object* v_tail_4906_; lean_object* v_val_4907_; lean_object* v___x_4908_; uint8_t v___x_4909_; 
lean_inc_ref(v_head_4896_);
v_tail_4906_ = lean_ctor_get(v_x_4888_, 1);
lean_inc(v_tail_4906_);
lean_dec_ref_known(v_x_4888_, 2);
v_val_4907_ = lean_ctor_get(v_head_4896_, 0);
lean_inc(v_val_4907_);
lean_dec_ref_known(v_head_4896_, 1);
v___x_4908_ = lean_array_get_size(v_xs_4887_);
v___x_4909_ = lean_nat_dec_lt(v_val_4907_, v___x_4908_);
if (v___x_4909_ == 0)
{
lean_object* v___x_4910_; lean_object* v___x_4911_; 
lean_dec(v_val_4907_);
lean_dec(v_tail_4906_);
lean_dec_ref(v_x_4889_);
lean_dec_ref(v_xs_4887_);
v___x_4910_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4911_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4910_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
return v___x_4911_;
}
else
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; 
v___x_4912_ = l_Lean_instInhabitedExpr;
v___x_4913_ = lean_array_get_borrowed(v___x_4912_, v_xs_4887_, v_val_4907_);
lean_dec(v_val_4907_);
v___x_4914_ = lean_unsigned_to_nat(1u);
v___x_4915_ = lean_mk_empty_array_with_capacity(v___x_4914_);
lean_inc(v___x_4913_);
v___x_4916_ = lean_array_push(v___x_4915_, v___x_4913_);
v___x_4917_ = l_Lean_Meta_instantiateLambda(v_x_4889_, v___x_4916_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
lean_dec_ref(v___x_4916_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4918_);
lean_dec_ref_known(v___x_4917_, 1);
v_x_4888_ = v_tail_4906_;
v_x_4889_ = v_a_4918_;
goto _start;
}
else
{
lean_dec(v_tail_4906_);
lean_dec_ref(v_xs_4887_);
return v___x_4917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4920_, lean_object* v_xs_4921_, lean_object* v_tail_4922_, uint8_t v___x_4923_, uint8_t v___x_4924_, lean_object* v_ys_4925_, lean_object* v_value_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v___x_4932_; uint8_t v___x_4933_; 
v___x_4932_ = lean_array_get_size(v_ys_4925_);
v___x_4933_ = lean_nat_dec_eq(v___x_4932_, v___x_4920_);
if (v___x_4933_ == 0)
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_dec_ref(v_value_4926_);
lean_dec(v_tail_4922_);
lean_dec_ref(v_xs_4921_);
v___x_4934_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4935_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4934_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
return v___x_4935_;
}
else
{
lean_object* v___x_4936_; 
v___x_4936_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4921_, v_tail_4922_, v_value_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; uint8_t v___x_4938_; lean_object* v___x_4939_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v___x_4938_ = 1;
v___x_4939_ = l_Lean_Meta_mkLambdaFVars(v_ys_4925_, v_a_4937_, v___x_4923_, v___x_4924_, v___x_4923_, v___x_4924_, v___x_4938_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
return v___x_4939_;
}
else
{
return v___x_4936_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4940_, lean_object* v_x_4941_, lean_object* v_x_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4940_, v_x_4941_, v_x_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
return v_res_4948_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4950_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4951_ = lean_unsigned_to_nat(2u);
v___x_4952_ = lean_unsigned_to_nat(362u);
v___x_4953_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_4954_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4955_ = l_mkPanicMessageWithDecl(v___x_4954_, v___x_4953_, v___x_4952_, v___x_4951_, v___x_4950_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_4956_, lean_object* v_value_u2080_4957_, lean_object* v_xs_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_){
_start:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; uint8_t v___x_4966_; 
v___x_4964_ = lean_array_get_size(v_xs_4958_);
v___x_4965_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4956_);
v___x_4966_ = lean_nat_dec_eq(v___x_4964_, v___x_4965_);
lean_dec(v___x_4965_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; lean_object* v___x_4968_; 
lean_dec_ref(v_xs_4958_);
lean_dec_ref(v_value_u2080_4957_);
lean_dec_ref(v_perm_4956_);
v___x_4967_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_4968_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4967_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
return v___x_4968_;
}
else
{
lean_object* v_mask_4969_; lean_object* v___x_4970_; 
v_mask_4969_ = lean_array_to_list(v_perm_4956_);
v___x_4970_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4958_, v_mask_4969_, v_value_u2080_4957_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
return v___x_4970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_4971_, lean_object* v_value_u2080_4972_, lean_object* v_xs_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_4971_, v_value_u2080_4972_, v_xs_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
return v_res_4979_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_4987_; 
v___x_4987_ = l_Array_instInhabited(lean_box(0));
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_4988_){
_start:
{
lean_object* v___f_4989_; lean_object* v___f_4990_; lean_object* v___f_4991_; lean_object* v___f_4992_; lean_object* v___f_4993_; lean_object* v___f_4994_; lean_object* v___f_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___f_4989_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_4990_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_4991_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_4992_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_4993_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_4994_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_4995_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4996_, 0, v___f_4989_);
lean_ctor_set(v___x_4996_, 1, v___f_4990_);
v___x_4997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4996_);
lean_ctor_set(v___x_4997_, 1, v___f_4991_);
lean_ctor_set(v___x_4997_, 2, v___f_4992_);
lean_ctor_set(v___x_4997_, 3, v___f_4993_);
lean_ctor_set(v___x_4997_, 4, v___f_4994_);
v___x_4998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4997_);
lean_ctor_set(v___x_4998_, 1, v___f_4995_);
v___x_4999_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5000_ = l_instInhabitedOfMonad___redArg(v___x_4998_, v___x_4999_);
v___x_5001_ = lean_panic_fn_borrowed(v___x_5000_, v_msg_4988_);
lean_dec(v___x_5000_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5002_, lean_object* v_msg_5003_){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5003_);
return v___x_5004_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5007_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5008_ = lean_unsigned_to_nat(8u);
v___x_5009_ = lean_unsigned_to_nat(394u);
v___x_5010_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5011_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5012_ = l_mkPanicMessageWithDecl(v___x_5011_, v___x_5010_, v___x_5009_, v___x_5008_, v___x_5007_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5013_, lean_object* v_x_5014_){
_start:
{
if (lean_obj_tag(v_x_5013_) == 0)
{
return v_x_5014_;
}
else
{
lean_object* v_head_5015_; lean_object* v_fst_5016_; 
v_head_5015_ = lean_ctor_get(v_x_5013_, 0);
v_fst_5016_ = lean_ctor_get(v_head_5015_, 0);
if (lean_obj_tag(v_fst_5016_) == 0)
{
lean_object* v_tail_5017_; 
v_tail_5017_ = lean_ctor_get(v_x_5013_, 1);
lean_inc(v_tail_5017_);
lean_dec_ref_known(v_x_5013_, 2);
v_x_5013_ = v_tail_5017_;
goto _start;
}
else
{
lean_object* v_tail_5019_; lean_object* v_snd_5020_; lean_object* v_val_5021_; lean_object* v___x_5022_; uint8_t v___x_5023_; 
lean_inc_ref(v_fst_5016_);
lean_inc(v_head_5015_);
v_tail_5019_ = lean_ctor_get(v_x_5013_, 1);
lean_inc(v_tail_5019_);
lean_dec_ref_known(v_x_5013_, 2);
v_snd_5020_ = lean_ctor_get(v_head_5015_, 1);
lean_inc(v_snd_5020_);
lean_dec(v_head_5015_);
v_val_5021_ = lean_ctor_get(v_fst_5016_, 0);
lean_inc(v_val_5021_);
lean_dec_ref_known(v_fst_5016_, 1);
v___x_5022_ = lean_array_get_size(v_x_5014_);
v___x_5023_ = lean_nat_dec_lt(v_val_5021_, v___x_5022_);
if (v___x_5023_ == 0)
{
lean_object* v___x_5024_; lean_object* v___x_5025_; 
lean_dec(v_val_5021_);
lean_dec(v_snd_5020_);
lean_dec(v_tail_5019_);
lean_dec_ref(v_x_5014_);
v___x_5024_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5025_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5024_);
return v___x_5025_;
}
else
{
lean_object* v___x_5026_; 
v___x_5026_ = lean_array_set(v_x_5014_, v_val_5021_, v_snd_5020_);
lean_dec(v_val_5021_);
v_x_5013_ = v_tail_5019_;
v_x_5014_ = v___x_5026_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5028_, lean_object* v_x_5029_, lean_object* v_x_5030_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5029_, v_x_5030_);
return v___x_5031_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5034_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5035_ = lean_unsigned_to_nat(2u);
v___x_5036_ = lean_unsigned_to_nat(384u);
v___x_5037_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5038_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5039_ = l_mkPanicMessageWithDecl(v___x_5038_, v___x_5037_, v___x_5036_, v___x_5035_, v___x_5034_);
return v___x_5039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5042_, lean_object* v_xs_5043_){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; uint8_t v___x_5046_; 
v___x_5044_ = lean_array_get_size(v_xs_5043_);
v___x_5045_ = lean_array_get_size(v_perm_5042_);
v___x_5046_ = lean_nat_dec_eq(v___x_5044_, v___x_5045_);
if (v___x_5046_ == 0)
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5048_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5047_);
return v___x_5048_;
}
else
{
lean_object* v___x_5049_; uint8_t v___x_5050_; 
v___x_5049_ = lean_unsigned_to_nat(0u);
v___x_5050_ = lean_nat_dec_eq(v___x_5044_, v___x_5049_);
if (v___x_5050_ == 0)
{
lean_object* v_dummy_5051_; lean_object* v___x_5052_; lean_object* v_ys_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v_dummy_5051_ = lean_array_fget_borrowed(v_xs_5043_, v___x_5049_);
v___x_5052_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5042_);
lean_inc(v_dummy_5051_);
v_ys_5053_ = lean_mk_array(v___x_5052_, v_dummy_5051_);
v___x_5054_ = l_Array_zip___redArg(v_perm_5042_, v_xs_5043_);
v___x_5055_ = lean_array_to_list(v___x_5054_);
v___x_5056_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5055_, v_ys_5053_);
return v___x_5056_;
}
else
{
lean_object* v___x_5057_; 
v___x_5057_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5058_, lean_object* v_xs_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5058_, v_xs_5059_);
lean_dec_ref(v_xs_5059_);
lean_dec_ref(v_perm_5058_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5061_, lean_object* v_perm_5062_, lean_object* v_xs_5063_){
_start:
{
lean_object* v___x_5064_; 
v___x_5064_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5062_, v_xs_5063_);
return v___x_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5065_, lean_object* v_perm_5066_, lean_object* v_xs_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5065_, v_perm_5066_, v_xs_5067_);
lean_dec_ref(v_xs_5067_);
lean_dec_ref(v_perm_5066_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5069_, lean_object* v_upperBound_5070_, lean_object* v_perm_5071_, lean_object* v_a_5072_, lean_object* v_b_5073_){
_start:
{
lean_object* v_a_5075_; uint8_t v___x_5082_; 
v___x_5082_ = lean_nat_dec_lt(v_a_5072_, v_upperBound_5070_);
if (v___x_5082_ == 0)
{
lean_dec(v_a_5072_);
return v_b_5073_;
}
else
{
lean_object* v___x_5083_; uint8_t v___x_5084_; 
v___x_5083_ = lean_array_get_size(v_perm_5071_);
v___x_5084_ = lean_nat_dec_lt(v_a_5072_, v___x_5083_);
if (v___x_5084_ == 0)
{
goto v___jp_5079_;
}
else
{
lean_object* v___x_5085_; 
v___x_5085_ = lean_array_fget_borrowed(v_perm_5071_, v_a_5072_);
if (lean_obj_tag(v___x_5085_) == 0)
{
goto v___jp_5079_;
}
else
{
v_a_5075_ = v_b_5073_;
goto v___jp_5074_;
}
}
}
v___jp_5074_:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = lean_unsigned_to_nat(1u);
v___x_5077_ = lean_nat_add(v_a_5072_, v___x_5076_);
lean_dec(v_a_5072_);
v_a_5072_ = v___x_5077_;
v_b_5073_ = v_a_5075_;
goto _start;
}
v___jp_5079_:
{
lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5080_ = lean_array_fget_borrowed(v_xs_5069_, v_a_5072_);
lean_inc(v___x_5080_);
v___x_5081_ = lean_array_push(v_b_5073_, v___x_5080_);
v_a_5075_ = v___x_5081_;
goto v___jp_5074_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5086_, lean_object* v_upperBound_5087_, lean_object* v_perm_5088_, lean_object* v_a_5089_, lean_object* v_b_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5086_, v_upperBound_5087_, v_perm_5088_, v_a_5089_, v_b_5090_);
lean_dec_ref(v_perm_5088_);
lean_dec(v_upperBound_5087_);
lean_dec_ref(v_xs_5086_);
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5092_, lean_object* v_xs_5093_){
_start:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v_ys_5096_; lean_object* v___x_5097_; 
v___x_5094_ = lean_array_get_size(v_xs_5093_);
v___x_5095_ = lean_unsigned_to_nat(0u);
v_ys_5096_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5093_, v___x_5094_, v_perm_5092_, v___x_5095_, v_ys_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5098_, lean_object* v_xs_5099_){
_start:
{
lean_object* v_res_5100_; 
v_res_5100_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5098_, v_xs_5099_);
lean_dec_ref(v_xs_5099_);
lean_dec_ref(v_perm_5098_);
return v_res_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5101_, lean_object* v_perm_5102_, lean_object* v_xs_5103_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5102_, v_xs_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5105_, lean_object* v_perm_5106_, lean_object* v_xs_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5105_, v_perm_5106_, v_xs_5107_);
lean_dec_ref(v_xs_5107_);
lean_dec_ref(v_perm_5106_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5109_, lean_object* v_xs_5110_, lean_object* v_upperBound_5111_, lean_object* v_perm_5112_, lean_object* v_inst_5113_, lean_object* v_R_5114_, lean_object* v_a_5115_, lean_object* v_b_5116_, lean_object* v_c_5117_){
_start:
{
lean_object* v___x_5118_; 
v___x_5118_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5110_, v_upperBound_5111_, v_perm_5112_, v_a_5115_, v_b_5116_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5119_, lean_object* v_xs_5120_, lean_object* v_upperBound_5121_, lean_object* v_perm_5122_, lean_object* v_inst_5123_, lean_object* v_R_5124_, lean_object* v_a_5125_, lean_object* v_b_5126_, lean_object* v_c_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5119_, v_xs_5120_, v_upperBound_5121_, v_perm_5122_, v_inst_5123_, v_R_5124_, v_a_5125_, v_b_5126_, v_c_5127_);
lean_dec_ref(v_perm_5122_);
lean_dec(v_upperBound_5121_);
lean_dec_ref(v_xs_5120_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5129_){
_start:
{
lean_object* v___x_5130_; lean_object* v___x_5131_; 
v___x_5130_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5131_ = lean_panic_fn_borrowed(v___x_5130_, v_msg_5129_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5132_, lean_object* v_msg_5133_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5133_);
return v___x_5134_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5135_, lean_object* v___x_5136_, lean_object* v_i_5137_, lean_object* v___x_5138_, lean_object* v_as_5139_, size_t v_i_5140_, size_t v_stop_5141_){
_start:
{
uint8_t v___x_5142_; 
v___x_5142_ = lean_usize_dec_eq(v_i_5140_, v_stop_5141_);
if (v___x_5142_ == 0)
{
uint8_t v___x_5143_; uint8_t v___y_5145_; lean_object* v___x_5149_; 
v___x_5143_ = 1;
v___x_5149_ = lean_array_uget_borrowed(v_as_5139_, v_i_5140_);
if (lean_obj_tag(v___x_5149_) == 0)
{
uint8_t v___x_5150_; 
v___x_5150_ = lean_nat_dec_lt(v_j_5135_, v___x_5136_);
v___y_5145_ = v___x_5150_;
goto v___jp_5144_;
}
else
{
uint8_t v___x_5151_; 
v___x_5151_ = lean_nat_dec_lt(v_i_5137_, v___x_5138_);
v___y_5145_ = v___x_5151_;
goto v___jp_5144_;
}
v___jp_5144_:
{
if (v___y_5145_ == 0)
{
size_t v___x_5146_; size_t v___x_5147_; 
v___x_5146_ = ((size_t)1ULL);
v___x_5147_ = lean_usize_add(v_i_5140_, v___x_5146_);
v_i_5140_ = v___x_5147_;
goto _start;
}
else
{
return v___x_5143_;
}
}
}
else
{
uint8_t v___x_5152_; 
v___x_5152_ = 0;
return v___x_5152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5153_, lean_object* v___x_5154_, lean_object* v_i_5155_, lean_object* v___x_5156_, lean_object* v_as_5157_, lean_object* v_i_5158_, lean_object* v_stop_5159_){
_start:
{
size_t v_i_boxed_5160_; size_t v_stop_boxed_5161_; uint8_t v_res_5162_; lean_object* v_r_5163_; 
v_i_boxed_5160_ = lean_unbox_usize(v_i_5158_);
lean_dec(v_i_5158_);
v_stop_boxed_5161_ = lean_unbox_usize(v_stop_5159_);
lean_dec(v_stop_5159_);
v_res_5162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5153_, v___x_5154_, v_i_5155_, v___x_5156_, v_as_5157_, v_i_boxed_5160_, v_stop_boxed_5161_);
lean_dec_ref(v_as_5157_);
lean_dec(v___x_5156_);
lean_dec(v_i_5155_);
lean_dec(v___x_5154_);
lean_dec(v_j_5153_);
v_r_5163_ = lean_box(v_res_5162_);
return v_r_5163_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; 
v___x_5166_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5167_ = lean_unsigned_to_nat(10u);
v___x_5168_ = lean_unsigned_to_nat(425u);
v___x_5169_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5170_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5171_ = l_mkPanicMessageWithDecl(v___x_5170_, v___x_5169_, v___x_5168_, v___x_5167_, v___x_5166_);
return v___x_5171_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; 
v___x_5173_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5174_ = lean_unsigned_to_nat(12u);
v___x_5175_ = lean_unsigned_to_nat(433u);
v___x_5176_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5177_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5178_ = l_mkPanicMessageWithDecl(v___x_5177_, v___x_5176_, v___x_5175_, v___x_5174_, v___x_5173_);
return v___x_5178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5179_, lean_object* v_fixedArgs_5180_, lean_object* v_varyingArgs_5181_, lean_object* v_i_5182_, lean_object* v_j_5183_, lean_object* v_xs_5184_){
_start:
{
lean_object* v_lower_5186_; lean_object* v_upper_5187_; lean_object* v___x_5191_; uint8_t v___x_5192_; 
v___x_5191_ = lean_array_get_size(v_perm_5179_);
v___x_5192_ = lean_nat_dec_lt(v_i_5182_, v___x_5191_);
if (v___x_5192_ == 0)
{
lean_object* v___x_5193_; lean_object* v___x_5194_; uint8_t v___x_5195_; 
lean_dec(v_i_5182_);
lean_dec_ref(v_perm_5179_);
v___x_5193_ = lean_unsigned_to_nat(0u);
v___x_5194_ = lean_array_get_size(v_varyingArgs_5181_);
v___x_5195_ = lean_nat_dec_le(v_j_5183_, v___x_5193_);
if (v___x_5195_ == 0)
{
v_lower_5186_ = v_j_5183_;
v_upper_5187_ = v___x_5194_;
goto v___jp_5185_;
}
else
{
lean_dec(v_j_5183_);
v_lower_5186_ = v___x_5193_;
v_upper_5187_ = v___x_5194_;
goto v___jp_5185_;
}
}
else
{
lean_object* v___x_5196_; 
v___x_5196_ = lean_array_fget_borrowed(v_perm_5179_, v_i_5182_);
if (lean_obj_tag(v___x_5196_) == 1)
{
lean_object* v_val_5197_; lean_object* v___x_5198_; uint8_t v___x_5199_; 
v_val_5197_ = lean_ctor_get(v___x_5196_, 0);
v___x_5198_ = lean_array_get_size(v_fixedArgs_5180_);
v___x_5199_ = lean_nat_dec_lt(v_val_5197_, v___x_5198_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; lean_object* v___x_5201_; 
lean_dec_ref(v_xs_5184_);
lean_dec(v_j_5183_);
lean_dec(v_i_5182_);
lean_dec_ref(v_varyingArgs_5181_);
lean_dec_ref(v_perm_5179_);
v___x_5200_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5201_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5200_);
return v___x_5201_;
}
else
{
lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; 
v___x_5202_ = lean_unsigned_to_nat(1u);
v___x_5203_ = lean_nat_add(v_i_5182_, v___x_5202_);
lean_dec(v_i_5182_);
v___x_5204_ = lean_array_fget_borrowed(v_fixedArgs_5180_, v_val_5197_);
lean_inc(v___x_5204_);
v___x_5205_ = lean_array_push(v_xs_5184_, v___x_5204_);
v_i_5182_ = v___x_5203_;
v_xs_5184_ = v___x_5205_;
goto _start;
}
}
else
{
lean_object* v___x_5207_; lean_object* v___y_5209_; lean_object* v___y_5210_; lean_object* v___y_5211_; lean_object* v_lower_5219_; lean_object* v_upper_5220_; uint8_t v___x_5228_; 
v___x_5207_ = lean_array_get_size(v_varyingArgs_5181_);
v___x_5228_ = lean_nat_dec_lt(v_j_5183_, v___x_5207_);
if (v___x_5228_ == 0)
{
lean_object* v___x_5229_; uint8_t v___x_5230_; 
lean_dec_ref(v_varyingArgs_5181_);
v___x_5229_ = lean_unsigned_to_nat(0u);
v___x_5230_ = lean_nat_dec_le(v_i_5182_, v___x_5229_);
if (v___x_5230_ == 0)
{
lean_inc(v_i_5182_);
v_lower_5219_ = v_i_5182_;
v_upper_5220_ = v___x_5191_;
goto v___jp_5218_;
}
else
{
v_lower_5219_ = v___x_5229_;
v_upper_5220_ = v___x_5191_;
goto v___jp_5218_;
}
}
else
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; 
v___x_5231_ = lean_unsigned_to_nat(1u);
v___x_5232_ = lean_nat_add(v_i_5182_, v___x_5231_);
lean_dec(v_i_5182_);
v___x_5233_ = lean_nat_add(v_j_5183_, v___x_5231_);
v___x_5234_ = lean_array_fget_borrowed(v_varyingArgs_5181_, v_j_5183_);
lean_dec(v_j_5183_);
lean_inc(v___x_5234_);
v___x_5235_ = lean_array_push(v_xs_5184_, v___x_5234_);
v_i_5182_ = v___x_5232_;
v_j_5183_ = v___x_5233_;
v_xs_5184_ = v___x_5235_;
goto _start;
}
v___jp_5208_:
{
uint8_t v___x_5212_; 
v___x_5212_ = lean_nat_dec_lt(v___y_5210_, v___y_5211_);
if (v___x_5212_ == 0)
{
lean_dec(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec(v_j_5183_);
lean_dec(v_i_5182_);
return v_xs_5184_;
}
else
{
size_t v___x_5213_; size_t v___x_5214_; uint8_t v___x_5215_; 
v___x_5213_ = lean_usize_of_nat(v___y_5210_);
lean_dec(v___y_5210_);
v___x_5214_ = lean_usize_of_nat(v___y_5211_);
lean_dec(v___y_5211_);
v___x_5215_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5183_, v___x_5207_, v_i_5182_, v___x_5191_, v___y_5209_, v___x_5213_, v___x_5214_);
lean_dec_ref(v___y_5209_);
lean_dec(v_i_5182_);
lean_dec(v_j_5183_);
if (v___x_5215_ == 0)
{
return v_xs_5184_;
}
else
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
lean_dec_ref(v_xs_5184_);
v___x_5216_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5217_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5216_);
return v___x_5217_;
}
}
}
v___jp_5218_:
{
lean_object* v___x_5221_; lean_object* v_array_5222_; lean_object* v_start_5223_; lean_object* v_stop_5224_; uint8_t v___x_5225_; 
v___x_5221_ = l_Array_toSubarray___redArg(v_perm_5179_, v_lower_5219_, v_upper_5220_);
v_array_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc_ref(v_array_5222_);
v_start_5223_ = lean_ctor_get(v___x_5221_, 1);
lean_inc(v_start_5223_);
v_stop_5224_ = lean_ctor_get(v___x_5221_, 2);
lean_inc(v_stop_5224_);
lean_dec_ref(v___x_5221_);
v___x_5225_ = lean_nat_dec_lt(v_start_5223_, v_stop_5224_);
if (v___x_5225_ == 0)
{
lean_dec(v_stop_5224_);
lean_dec(v_start_5223_);
lean_dec_ref(v_array_5222_);
lean_dec(v_j_5183_);
lean_dec(v_i_5182_);
return v_xs_5184_;
}
else
{
lean_object* v___x_5226_; uint8_t v___x_5227_; 
v___x_5226_ = lean_array_get_size(v_array_5222_);
v___x_5227_ = lean_nat_dec_le(v_stop_5224_, v___x_5226_);
if (v___x_5227_ == 0)
{
lean_dec(v_stop_5224_);
v___y_5209_ = v_array_5222_;
v___y_5210_ = v_start_5223_;
v___y_5211_ = v___x_5226_;
goto v___jp_5208_;
}
else
{
v___y_5209_ = v_array_5222_;
v___y_5210_ = v_start_5223_;
v___y_5211_ = v_stop_5224_;
goto v___jp_5208_;
}
}
}
}
}
v___jp_5185_:
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; 
v___x_5188_ = l_Array_toSubarray___redArg(v_varyingArgs_5181_, v_lower_5186_, v_upper_5187_);
v___x_5189_ = l_Subarray_copy___redArg(v___x_5188_);
v___x_5190_ = l_Array_append___redArg(v_xs_5184_, v___x_5189_);
lean_dec_ref(v___x_5189_);
return v___x_5190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5237_, lean_object* v_fixedArgs_5238_, lean_object* v_varyingArgs_5239_, lean_object* v_i_5240_, lean_object* v_j_5241_, lean_object* v_xs_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5237_, v_fixedArgs_5238_, v_varyingArgs_5239_, v_i_5240_, v_j_5241_, v_xs_5242_);
lean_dec_ref(v_fixedArgs_5238_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5244_, lean_object* v_perm_5245_, lean_object* v_fixedArgs_5246_, lean_object* v_varyingArgs_5247_, lean_object* v_i_5248_, lean_object* v_j_5249_, lean_object* v_xs_5250_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5245_, v_fixedArgs_5246_, v_varyingArgs_5247_, v_i_5248_, v_j_5249_, v_xs_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5252_, lean_object* v_perm_5253_, lean_object* v_fixedArgs_5254_, lean_object* v_varyingArgs_5255_, lean_object* v_i_5256_, lean_object* v_j_5257_, lean_object* v_xs_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5252_, v_perm_5253_, v_fixedArgs_5254_, v_varyingArgs_5255_, v_i_5256_, v_j_5257_, v_xs_5258_);
lean_dec_ref(v_fixedArgs_5254_);
return v_res_5259_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; 
v___x_5262_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5263_ = lean_unsigned_to_nat(2u);
v___x_5264_ = lean_unsigned_to_nat(416u);
v___x_5265_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5266_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5267_ = l_mkPanicMessageWithDecl(v___x_5266_, v___x_5265_, v___x_5264_, v___x_5263_, v___x_5262_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5268_, lean_object* v_fixedArgs_5269_, lean_object* v_varyingArgs_5270_){
_start:
{
lean_object* v___x_5271_; lean_object* v___x_5272_; uint8_t v___x_5273_; 
v___x_5271_ = lean_array_get_size(v_fixedArgs_5269_);
v___x_5272_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5268_);
v___x_5273_ = lean_nat_dec_eq(v___x_5271_, v___x_5272_);
lean_dec(v___x_5272_);
if (v___x_5273_ == 0)
{
lean_object* v___x_5274_; lean_object* v___x_5275_; 
lean_dec_ref(v_varyingArgs_5270_);
lean_dec_ref(v_perm_5268_);
v___x_5274_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5275_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5274_);
return v___x_5275_;
}
else
{
lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v___x_5276_ = lean_unsigned_to_nat(0u);
v___x_5277_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5278_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5268_, v_fixedArgs_5269_, v_varyingArgs_5270_, v___x_5276_, v___x_5276_, v___x_5277_);
return v___x_5278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5279_, lean_object* v_fixedArgs_5280_, lean_object* v_varyingArgs_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5279_, v_fixedArgs_5280_, v_varyingArgs_5281_);
lean_dec_ref(v_fixedArgs_5280_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5283_, lean_object* v_perm_5284_, lean_object* v_fixedArgs_5285_, lean_object* v_varyingArgs_5286_){
_start:
{
lean_object* v___x_5287_; 
v___x_5287_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5284_, v_fixedArgs_5285_, v_varyingArgs_5286_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5288_, lean_object* v_perm_5289_, lean_object* v_fixedArgs_5290_, lean_object* v_varyingArgs_5291_){
_start:
{
lean_object* v_res_5292_; 
v_res_5292_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5288_, v_perm_5289_, v_fixedArgs_5290_, v_varyingArgs_5291_);
lean_dec_ref(v_fixedArgs_5290_);
return v_res_5292_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5293_, lean_object* v_x_5294_){
_start:
{
if (lean_obj_tag(v_x_5293_) == 0)
{
if (lean_obj_tag(v_x_5294_) == 0)
{
uint8_t v___x_5295_; 
v___x_5295_ = 1;
return v___x_5295_;
}
else
{
uint8_t v___x_5296_; 
v___x_5296_ = 0;
return v___x_5296_;
}
}
else
{
if (lean_obj_tag(v_x_5294_) == 0)
{
uint8_t v___x_5297_; 
v___x_5297_ = 0;
return v___x_5297_;
}
else
{
lean_object* v_val_5298_; lean_object* v_val_5299_; uint8_t v___x_5300_; 
v_val_5298_ = lean_ctor_get(v_x_5293_, 0);
v_val_5299_ = lean_ctor_get(v_x_5294_, 0);
v___x_5300_ = lean_nat_dec_eq(v_val_5298_, v_val_5299_);
return v___x_5300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5301_, lean_object* v_x_5302_){
_start:
{
uint8_t v_res_5303_; lean_object* v_r_5304_; 
v_res_5303_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5301_, v_x_5302_);
lean_dec(v_x_5302_);
lean_dec(v_x_5301_);
v_r_5304_ = lean_box(v_res_5303_);
return v_r_5304_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5305_, lean_object* v_ys_5306_, lean_object* v_x_5307_){
_start:
{
lean_object* v_zero_5308_; uint8_t v_isZero_5309_; 
v_zero_5308_ = lean_unsigned_to_nat(0u);
v_isZero_5309_ = lean_nat_dec_eq(v_x_5307_, v_zero_5308_);
if (v_isZero_5309_ == 1)
{
lean_dec(v_x_5307_);
return v_isZero_5309_;
}
else
{
lean_object* v_one_5310_; lean_object* v_n_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; uint8_t v___x_5314_; 
v_one_5310_ = lean_unsigned_to_nat(1u);
v_n_5311_ = lean_nat_sub(v_x_5307_, v_one_5310_);
lean_dec(v_x_5307_);
v___x_5312_ = lean_array_fget_borrowed(v_xs_5305_, v_n_5311_);
v___x_5313_ = lean_array_fget_borrowed(v_ys_5306_, v_n_5311_);
v___x_5314_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5312_, v___x_5313_);
if (v___x_5314_ == 0)
{
lean_dec(v_n_5311_);
return v___x_5314_;
}
else
{
v_x_5307_ = v_n_5311_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5316_, lean_object* v_ys_5317_, lean_object* v_x_5318_){
_start:
{
uint8_t v_res_5319_; lean_object* v_r_5320_; 
v_res_5319_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5316_, v_ys_5317_, v_x_5318_);
lean_dec_ref(v_ys_5317_);
lean_dec_ref(v_xs_5316_);
v_r_5320_ = lean_box(v_res_5319_);
return v_r_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5321_, size_t v_i_5322_, lean_object* v_bs_5323_){
_start:
{
uint8_t v___x_5324_; 
v___x_5324_ = lean_usize_dec_lt(v_i_5322_, v_sz_5321_);
if (v___x_5324_ == 0)
{
return v_bs_5323_;
}
else
{
lean_object* v_v_5325_; lean_object* v___x_5326_; lean_object* v_bs_x27_5327_; lean_object* v___x_5328_; size_t v___x_5329_; size_t v___x_5330_; lean_object* v___x_5331_; 
v_v_5325_ = lean_array_uget(v_bs_5323_, v_i_5322_);
v___x_5326_ = lean_unsigned_to_nat(0u);
v_bs_x27_5327_ = lean_array_uset(v_bs_5323_, v_i_5322_, v___x_5326_);
v___x_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5328_, 0, v_v_5325_);
v___x_5329_ = ((size_t)1ULL);
v___x_5330_ = lean_usize_add(v_i_5322_, v___x_5329_);
v___x_5331_ = lean_array_uset(v_bs_x27_5327_, v_i_5322_, v___x_5328_);
v_i_5322_ = v___x_5330_;
v_bs_5323_ = v___x_5331_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5333_, lean_object* v_i_5334_, lean_object* v_bs_5335_){
_start:
{
size_t v_sz_boxed_5336_; size_t v_i_boxed_5337_; lean_object* v_res_5338_; 
v_sz_boxed_5336_ = lean_unbox_usize(v_sz_5333_);
lean_dec(v_sz_5333_);
v_i_boxed_5337_ = lean_unbox_usize(v_i_5334_);
lean_dec(v_i_5334_);
v_res_5338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5336_, v_i_boxed_5337_, v_bs_5335_);
return v_res_5338_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5339_, lean_object* v_as_5340_, size_t v_i_5341_, size_t v_stop_5342_){
_start:
{
uint8_t v___x_5343_; 
v___x_5343_ = lean_usize_dec_eq(v_i_5341_, v_stop_5342_);
if (v___x_5343_ == 0)
{
lean_object* v_numFixed_5344_; uint8_t v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; size_t v_sz_5348_; size_t v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; uint8_t v___x_5357_; 
v_numFixed_5344_ = lean_ctor_get(v_fixedParamPerms_5339_, 0);
v___x_5345_ = 1;
v___x_5346_ = lean_array_uget_borrowed(v_as_5340_, v_i_5341_);
lean_inc(v_numFixed_5344_);
v___x_5347_ = l_Array_range(v_numFixed_5344_);
v_sz_5348_ = lean_array_size(v___x_5347_);
v___x_5349_ = ((size_t)0ULL);
v___x_5350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5348_, v___x_5349_, v___x_5347_);
v___x_5351_ = lean_array_get_size(v___x_5346_);
v___x_5352_ = lean_nat_sub(v___x_5351_, v_numFixed_5344_);
v___x_5353_ = lean_box(0);
v___x_5354_ = lean_mk_array(v___x_5352_, v___x_5353_);
v___x_5355_ = l_Array_append___redArg(v___x_5350_, v___x_5354_);
lean_dec_ref(v___x_5354_);
v___x_5356_ = lean_array_get_size(v___x_5355_);
v___x_5357_ = lean_nat_dec_eq(v___x_5351_, v___x_5356_);
if (v___x_5357_ == 0)
{
lean_dec_ref(v___x_5355_);
lean_dec_ref(v_fixedParamPerms_5339_);
return v___x_5345_;
}
else
{
uint8_t v___x_5358_; 
v___x_5358_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5346_, v___x_5355_, v___x_5351_);
lean_dec_ref(v___x_5355_);
if (v___x_5358_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5339_);
return v___x_5345_;
}
else
{
size_t v___x_5359_; size_t v___x_5360_; 
v___x_5359_ = ((size_t)1ULL);
v___x_5360_ = lean_usize_add(v_i_5341_, v___x_5359_);
v_i_5341_ = v___x_5360_;
goto _start;
}
}
}
else
{
uint8_t v___x_5362_; 
lean_dec_ref(v_fixedParamPerms_5339_);
v___x_5362_ = 0;
return v___x_5362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5363_, lean_object* v_as_5364_, lean_object* v_i_5365_, lean_object* v_stop_5366_){
_start:
{
size_t v_i_boxed_5367_; size_t v_stop_boxed_5368_; uint8_t v_res_5369_; lean_object* v_r_5370_; 
v_i_boxed_5367_ = lean_unbox_usize(v_i_5365_);
lean_dec(v_i_5365_);
v_stop_boxed_5368_ = lean_unbox_usize(v_stop_5366_);
lean_dec(v_stop_5366_);
v_res_5369_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5363_, v_as_5364_, v_i_boxed_5367_, v_stop_boxed_5368_);
lean_dec_ref(v_as_5364_);
v_r_5370_ = lean_box(v_res_5369_);
return v_r_5370_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5371_){
_start:
{
lean_object* v_perms_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; uint8_t v___x_5375_; 
v_perms_5372_ = lean_ctor_get(v_fixedParamPerms_5371_, 1);
lean_inc_ref(v_perms_5372_);
v___x_5373_ = lean_unsigned_to_nat(0u);
v___x_5374_ = lean_array_get_size(v_perms_5372_);
v___x_5375_ = lean_nat_dec_lt(v___x_5373_, v___x_5374_);
if (v___x_5375_ == 0)
{
uint8_t v___x_5376_; 
lean_dec_ref(v_perms_5372_);
lean_dec_ref(v_fixedParamPerms_5371_);
v___x_5376_ = 1;
return v___x_5376_;
}
else
{
if (v___x_5375_ == 0)
{
lean_dec_ref(v_perms_5372_);
lean_dec_ref(v_fixedParamPerms_5371_);
return v___x_5375_;
}
else
{
size_t v___x_5377_; size_t v___x_5378_; uint8_t v___x_5379_; 
v___x_5377_ = ((size_t)0ULL);
v___x_5378_ = lean_usize_of_nat(v___x_5374_);
v___x_5379_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5371_, v_perms_5372_, v___x_5377_, v___x_5378_);
lean_dec_ref(v_perms_5372_);
if (v___x_5379_ == 0)
{
return v___x_5375_;
}
else
{
uint8_t v___x_5380_; 
v___x_5380_ = 0;
return v___x_5380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5381_){
_start:
{
uint8_t v_res_5382_; lean_object* v_r_5383_; 
v_res_5382_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5381_);
v_r_5383_ = lean_box(v_res_5382_);
return v_r_5383_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5384_, lean_object* v_ys_5385_, lean_object* v_hsz_5386_, lean_object* v_x_5387_, lean_object* v_x_5388_){
_start:
{
uint8_t v___x_5389_; 
v___x_5389_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5384_, v_ys_5385_, v_x_5387_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5390_, lean_object* v_ys_5391_, lean_object* v_hsz_5392_, lean_object* v_x_5393_, lean_object* v_x_5394_){
_start:
{
uint8_t v_res_5395_; lean_object* v_r_5396_; 
v_res_5395_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5390_, v_ys_5391_, v_hsz_5392_, v_x_5393_, v_x_5394_);
lean_dec_ref(v_ys_5391_);
lean_dec_ref(v_xs_5390_);
v_r_5396_ = lean_box(v_res_5395_);
return v_r_5396_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5397_; 
v___x_5397_ = l_Array_instInhabited(lean_box(0));
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5398_){
_start:
{
lean_object* v___f_5399_; lean_object* v___f_5400_; lean_object* v___f_5401_; lean_object* v___f_5402_; lean_object* v___f_5403_; lean_object* v___f_5404_; lean_object* v___f_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___f_5399_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5400_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5401_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5402_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5403_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5404_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5405_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5406_, 0, v___f_5399_);
lean_ctor_set(v___x_5406_, 1, v___f_5400_);
v___x_5407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5406_);
lean_ctor_set(v___x_5407_, 1, v___f_5401_);
lean_ctor_set(v___x_5407_, 2, v___f_5402_);
lean_ctor_set(v___x_5407_, 3, v___f_5403_);
lean_ctor_set(v___x_5407_, 4, v___f_5404_);
v___x_5408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5407_);
lean_ctor_set(v___x_5408_, 1, v___f_5405_);
v___x_5409_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5410_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5410_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5412_, 0, v___x_5409_);
lean_ctor_set(v___x_5412_, 1, v___x_5411_);
v___x_5413_ = l_instInhabitedOfMonad___redArg(v___x_5408_, v___x_5412_);
v___x_5414_ = lean_panic_fn_borrowed(v___x_5413_, v_msg_5398_);
lean_dec(v___x_5413_);
return v___x_5414_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5415_; 
v___x_5415_ = l_Array_instInhabited(lean_box(0));
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5416_){
_start:
{
lean_object* v___f_5417_; lean_object* v___f_5418_; lean_object* v___f_5419_; lean_object* v___f_5420_; lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___f_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___f_5417_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5418_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5419_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5420_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5421_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5422_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5423_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5424_, 0, v___f_5417_);
lean_ctor_set(v___x_5424_, 1, v___f_5418_);
v___x_5425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5425_, 0, v___x_5424_);
lean_ctor_set(v___x_5425_, 1, v___f_5419_);
lean_ctor_set(v___x_5425_, 2, v___f_5420_);
lean_ctor_set(v___x_5425_, 3, v___f_5421_);
lean_ctor_set(v___x_5425_, 4, v___f_5422_);
v___x_5426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5425_);
lean_ctor_set(v___x_5426_, 1, v___f_5423_);
v___x_5427_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5427_);
v___x_5429_ = l_instInhabitedOfMonad___redArg(v___x_5426_, v___x_5428_);
v___x_5430_ = lean_panic_fn_borrowed(v___x_5429_, v_msg_5416_);
lean_dec(v___x_5429_);
return v___x_5430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5431_, uint8_t v___x_5432_, lean_object* v___x_5433_, lean_object* v___x_5434_, lean_object* v_as_5435_, size_t v_sz_5436_, size_t v_i_5437_, lean_object* v_b_5438_){
_start:
{
lean_object* v_a_5440_; uint8_t v___x_5444_; 
v___x_5444_ = lean_usize_dec_lt(v_i_5437_, v_sz_5436_);
if (v___x_5444_ == 0)
{
return v_b_5438_;
}
else
{
lean_object* v_fst_5445_; lean_object* v_snd_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5468_; 
v_fst_5445_ = lean_ctor_get(v_b_5438_, 0);
v_snd_5446_ = lean_ctor_get(v_b_5438_, 1);
v_isSharedCheck_5468_ = !lean_is_exclusive(v_b_5438_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5448_ = v_b_5438_;
v_isShared_5449_ = v_isSharedCheck_5468_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_snd_5446_);
lean_inc(v_fst_5445_);
lean_dec(v_b_5438_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5468_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v___x_5454_; lean_object* v_a_5455_; lean_object* v___x_5456_; 
v___x_5454_ = lean_box(0);
v_a_5455_ = lean_array_uget_borrowed(v_as_5435_, v_i_5437_);
v___x_5456_ = lean_array_get_borrowed(v___x_5454_, v___x_5431_, v_a_5455_);
if (lean_obj_tag(v___x_5456_) == 1)
{
lean_object* v_val_5457_; uint8_t v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; uint8_t v___x_5461_; 
v_val_5457_ = lean_ctor_get(v___x_5456_, 0);
v___x_5458_ = 0;
v___x_5459_ = lean_box(v___x_5458_);
v___x_5460_ = lean_array_get(v___x_5459_, v_fst_5445_, v_val_5457_);
lean_dec(v___x_5459_);
v___x_5461_ = lean_unbox(v___x_5460_);
lean_dec(v___x_5460_);
if (v___x_5461_ == 0)
{
if (v___x_5432_ == 0)
{
goto v___jp_5450_;
}
else
{
uint8_t v_changed_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; 
lean_del_object(v___x_5448_);
lean_dec(v_snd_5446_);
v_changed_5462_ = lean_nat_dec_eq(v___x_5433_, v___x_5434_);
v___x_5463_ = lean_box(v_changed_5462_);
v___x_5464_ = lean_array_set(v_fst_5445_, v_val_5457_, v___x_5463_);
v___x_5465_ = lean_box(v_changed_5462_);
v___x_5466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5466_, 0, v___x_5464_);
lean_ctor_set(v___x_5466_, 1, v___x_5465_);
v_a_5440_ = v___x_5466_;
goto v___jp_5439_;
}
}
else
{
goto v___jp_5450_;
}
}
else
{
lean_object* v___x_5467_; 
lean_del_object(v___x_5448_);
v___x_5467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5467_, 0, v_fst_5445_);
lean_ctor_set(v___x_5467_, 1, v_snd_5446_);
v_a_5440_ = v___x_5467_;
goto v___jp_5439_;
}
v___jp_5450_:
{
lean_object* v___x_5452_; 
if (v_isShared_5449_ == 0)
{
v___x_5452_ = v___x_5448_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_fst_5445_);
lean_ctor_set(v_reuseFailAlloc_5453_, 1, v_snd_5446_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
v_a_5440_ = v___x_5452_;
goto v___jp_5439_;
}
}
}
}
v___jp_5439_:
{
size_t v___x_5441_; size_t v___x_5442_; 
v___x_5441_ = ((size_t)1ULL);
v___x_5442_ = lean_usize_add(v_i_5437_, v___x_5441_);
v_i_5437_ = v___x_5442_;
v_b_5438_ = v_a_5440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5469_, lean_object* v___x_5470_, lean_object* v___x_5471_, lean_object* v___x_5472_, lean_object* v_as_5473_, lean_object* v_sz_5474_, lean_object* v_i_5475_, lean_object* v_b_5476_){
_start:
{
uint8_t v___x_6987__boxed_5477_; size_t v_sz_boxed_5478_; size_t v_i_boxed_5479_; lean_object* v_res_5480_; 
v___x_6987__boxed_5477_ = lean_unbox(v___x_5470_);
v_sz_boxed_5478_ = lean_unbox_usize(v_sz_5474_);
lean_dec(v_sz_5474_);
v_i_boxed_5479_ = lean_unbox_usize(v_i_5475_);
lean_dec(v_i_5475_);
v_res_5480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5469_, v___x_6987__boxed_5477_, v___x_5471_, v___x_5472_, v_as_5473_, v_sz_boxed_5478_, v_i_boxed_5479_, v_b_5476_);
lean_dec_ref(v_as_5473_);
lean_dec(v___x_5472_);
lean_dec(v___x_5471_);
lean_dec_ref(v___x_5469_);
return v_res_5480_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5481_; 
v___x_5481_ = l_Array_instInhabited(lean_box(0));
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object* v_upperBound_5482_, lean_object* v___x_5483_, lean_object* v_fixedParamPerms_5484_, lean_object* v_next_5485_, lean_object* v___x_5486_, lean_object* v___x_5487_, lean_object* v_a_5488_, lean_object* v_b_5489_){
_start:
{
lean_object* v_a_5491_; uint8_t v___x_5495_; 
v___x_5495_ = lean_nat_dec_lt(v_a_5488_, v_upperBound_5482_);
if (v___x_5495_ == 0)
{
lean_dec(v_a_5488_);
return v_b_5489_;
}
else
{
lean_object* v_fst_5496_; lean_object* v_snd_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5533_; 
v_fst_5496_ = lean_ctor_get(v_b_5489_, 0);
v_snd_5497_ = lean_ctor_get(v_b_5489_, 1);
v_isSharedCheck_5533_ = !lean_is_exclusive(v_b_5489_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5499_ = v_b_5489_;
v_isShared_5500_ = v_isSharedCheck_5533_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_snd_5497_);
lean_inc(v_fst_5496_);
lean_dec(v_b_5489_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5533_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5501_; 
v___x_5501_ = lean_array_fget_borrowed(v___x_5483_, v_a_5488_);
if (lean_obj_tag(v___x_5501_) == 1)
{
lean_object* v_val_5502_; uint8_t v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; uint8_t v___x_5506_; 
v_val_5502_ = lean_ctor_get(v___x_5501_, 0);
v___x_5503_ = 0;
v___x_5504_ = lean_box(v___x_5503_);
v___x_5505_ = lean_array_get(v___x_5504_, v_fst_5496_, v_val_5502_);
lean_dec(v___x_5504_);
v___x_5506_ = lean_unbox(v___x_5505_);
if (v___x_5506_ == 0)
{
lean_object* v___x_5508_; 
lean_dec(v___x_5505_);
if (v_isShared_5500_ == 0)
{
v___x_5508_ = v___x_5499_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_fst_5496_);
lean_ctor_set(v_reuseFailAlloc_5509_, 1, v_snd_5497_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
v_a_5491_ = v___x_5508_;
goto v___jp_5490_;
}
}
else
{
lean_object* v_revDeps_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5515_; 
v_revDeps_5510_ = lean_ctor_get(v_fixedParamPerms_5484_, 2);
v___x_5511_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0);
v___x_5512_ = lean_array_get_borrowed(v___x_5511_, v_revDeps_5510_, v_next_5485_);
v___x_5513_ = lean_array_get_borrowed(v___x_5511_, v___x_5512_, v_a_5488_);
if (v_isShared_5500_ == 0)
{
v___x_5515_ = v___x_5499_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_fst_5496_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_snd_5497_);
v___x_5515_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
size_t v_sz_5516_; size_t v___x_5517_; uint8_t v___x_5518_; lean_object* v___x_5519_; lean_object* v_fst_5520_; lean_object* v_snd_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5528_; 
v_sz_5516_ = lean_array_size(v___x_5513_);
v___x_5517_ = ((size_t)0ULL);
v___x_5518_ = lean_unbox(v___x_5505_);
lean_dec(v___x_5505_);
v___x_5519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5483_, v___x_5518_, v___x_5486_, v___x_5487_, v___x_5513_, v_sz_5516_, v___x_5517_, v___x_5515_);
v_fst_5520_ = lean_ctor_get(v___x_5519_, 0);
v_snd_5521_ = lean_ctor_get(v___x_5519_, 1);
v_isSharedCheck_5528_ = !lean_is_exclusive(v___x_5519_);
if (v_isSharedCheck_5528_ == 0)
{
v___x_5523_ = v___x_5519_;
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_snd_5521_);
lean_inc(v_fst_5520_);
lean_dec(v___x_5519_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5526_; 
if (v_isShared_5524_ == 0)
{
v___x_5526_ = v___x_5523_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_fst_5520_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v_snd_5521_);
v___x_5526_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
v_a_5491_ = v___x_5526_;
goto v___jp_5490_;
}
}
}
}
}
else
{
lean_object* v___x_5531_; 
if (v_isShared_5500_ == 0)
{
v___x_5531_ = v___x_5499_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_fst_5496_);
lean_ctor_set(v_reuseFailAlloc_5532_, 1, v_snd_5497_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
v_a_5491_ = v___x_5531_;
goto v___jp_5490_;
}
}
}
}
v___jp_5490_:
{
lean_object* v___x_5492_; lean_object* v___x_5493_; 
v___x_5492_ = lean_unsigned_to_nat(1u);
v___x_5493_ = lean_nat_add(v_a_5488_, v___x_5492_);
lean_dec(v_a_5488_);
v_a_5488_ = v___x_5493_;
v_b_5489_ = v_a_5491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object* v_upperBound_5534_, lean_object* v___x_5535_, lean_object* v_fixedParamPerms_5536_, lean_object* v_next_5537_, lean_object* v___x_5538_, lean_object* v___x_5539_, lean_object* v_a_5540_, lean_object* v_b_5541_){
_start:
{
lean_object* v_res_5542_; 
v_res_5542_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5534_, v___x_5535_, v_fixedParamPerms_5536_, v_next_5537_, v___x_5538_, v___x_5539_, v_a_5540_, v_b_5541_);
lean_dec(v___x_5539_);
lean_dec(v___x_5538_);
lean_dec(v_next_5537_);
lean_dec_ref(v_fixedParamPerms_5536_);
lean_dec_ref(v___x_5535_);
lean_dec(v_upperBound_5534_);
return v_res_5542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5543_, lean_object* v___x_5544_, lean_object* v___x_5545_, lean_object* v___x_5546_, lean_object* v_fixedParamPerms_5547_, lean_object* v_next_5548_, lean_object* v_a_5549_, lean_object* v_b_5550_){
_start:
{
lean_object* v_a_5552_; uint8_t v___x_5556_; 
v___x_5556_ = lean_nat_dec_lt(v_a_5549_, v_upperBound_5543_);
if (v___x_5556_ == 0)
{
return v_b_5550_;
}
else
{
lean_object* v_fst_5557_; lean_object* v_snd_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5594_; 
v_fst_5557_ = lean_ctor_get(v_b_5550_, 0);
v_snd_5558_ = lean_ctor_get(v_b_5550_, 1);
v_isSharedCheck_5594_ = !lean_is_exclusive(v_b_5550_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5560_ = v_b_5550_;
v_isShared_5561_ = v_isSharedCheck_5594_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_snd_5558_);
lean_inc(v_fst_5557_);
lean_dec(v_b_5550_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5594_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v___x_5562_; 
v___x_5562_ = lean_array_fget_borrowed(v___x_5544_, v_a_5549_);
if (lean_obj_tag(v___x_5562_) == 1)
{
lean_object* v_val_5563_; uint8_t v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; uint8_t v___x_5567_; 
v_val_5563_ = lean_ctor_get(v___x_5562_, 0);
v___x_5564_ = 0;
v___x_5565_ = lean_box(v___x_5564_);
v___x_5566_ = lean_array_get(v___x_5565_, v_fst_5557_, v_val_5563_);
lean_dec(v___x_5565_);
v___x_5567_ = lean_unbox(v___x_5566_);
if (v___x_5567_ == 0)
{
lean_object* v___x_5569_; 
lean_dec(v___x_5566_);
if (v_isShared_5561_ == 0)
{
v___x_5569_ = v___x_5560_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_fst_5557_);
lean_ctor_set(v_reuseFailAlloc_5570_, 1, v_snd_5558_);
v___x_5569_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
v_a_5552_ = v___x_5569_;
goto v___jp_5551_;
}
}
else
{
lean_object* v_revDeps_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5576_; 
v_revDeps_5571_ = lean_ctor_get(v_fixedParamPerms_5547_, 2);
v___x_5572_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0);
v___x_5573_ = lean_array_get_borrowed(v___x_5572_, v_revDeps_5571_, v_next_5548_);
v___x_5574_ = lean_array_get_borrowed(v___x_5572_, v___x_5573_, v_a_5549_);
if (v_isShared_5561_ == 0)
{
v___x_5576_ = v___x_5560_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_fst_5557_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v_snd_5558_);
v___x_5576_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
size_t v_sz_5577_; size_t v___x_5578_; uint8_t v___x_5579_; lean_object* v___x_5580_; lean_object* v_fst_5581_; lean_object* v_snd_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5589_; 
v_sz_5577_ = lean_array_size(v___x_5574_);
v___x_5578_ = ((size_t)0ULL);
v___x_5579_ = lean_unbox(v___x_5566_);
lean_dec(v___x_5566_);
v___x_5580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5544_, v___x_5579_, v___x_5545_, v___x_5546_, v___x_5574_, v_sz_5577_, v___x_5578_, v___x_5576_);
v_fst_5581_ = lean_ctor_get(v___x_5580_, 0);
v_snd_5582_ = lean_ctor_get(v___x_5580_, 1);
v_isSharedCheck_5589_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5584_ = v___x_5580_;
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_snd_5582_);
lean_inc(v_fst_5581_);
lean_dec(v___x_5580_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5587_; 
if (v_isShared_5585_ == 0)
{
v___x_5587_ = v___x_5584_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_fst_5581_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v_snd_5582_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
v_a_5552_ = v___x_5587_;
goto v___jp_5551_;
}
}
}
}
}
else
{
lean_object* v___x_5592_; 
if (v_isShared_5561_ == 0)
{
v___x_5592_ = v___x_5560_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_fst_5557_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_snd_5558_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
v_a_5552_ = v___x_5592_;
goto v___jp_5551_;
}
}
}
}
v___jp_5551_:
{
lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; 
v___x_5553_ = lean_unsigned_to_nat(1u);
v___x_5554_ = lean_nat_add(v_a_5549_, v___x_5553_);
v___x_5555_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5543_, v___x_5544_, v_fixedParamPerms_5547_, v_next_5548_, v___x_5545_, v___x_5546_, v___x_5554_, v_a_5552_);
return v___x_5555_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5595_, lean_object* v___x_5596_, lean_object* v___x_5597_, lean_object* v___x_5598_, lean_object* v_fixedParamPerms_5599_, lean_object* v_next_5600_, lean_object* v_a_5601_, lean_object* v_b_5602_){
_start:
{
lean_object* v_res_5603_; 
v_res_5603_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5595_, v___x_5596_, v___x_5597_, v___x_5598_, v_fixedParamPerms_5599_, v_next_5600_, v_a_5601_, v_b_5602_);
lean_dec(v_a_5601_);
lean_dec(v_next_5600_);
lean_dec_ref(v_fixedParamPerms_5599_);
lean_dec(v___x_5598_);
lean_dec(v___x_5597_);
lean_dec_ref(v___x_5596_);
lean_dec(v_upperBound_5595_);
return v_res_5603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5604_, lean_object* v___x_5605_, lean_object* v___x_5606_, lean_object* v___x_5607_, lean_object* v_fixedParamPerms_5608_, lean_object* v_a_5609_, lean_object* v_b_5610_){
_start:
{
uint8_t v___x_5611_; 
v___x_5611_ = lean_nat_dec_lt(v_a_5609_, v_upperBound_5604_);
if (v___x_5611_ == 0)
{
lean_dec(v_a_5609_);
return v_b_5610_;
}
else
{
lean_object* v_fst_5612_; lean_object* v_snd_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5636_; 
v_fst_5612_ = lean_ctor_get(v_b_5610_, 0);
v_snd_5613_ = lean_ctor_get(v_b_5610_, 1);
v_isSharedCheck_5636_ = !lean_is_exclusive(v_b_5610_);
if (v_isSharedCheck_5636_ == 0)
{
v___x_5615_ = v_b_5610_;
v_isShared_5616_ = v_isSharedCheck_5636_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_snd_5613_);
lean_inc(v_fst_5612_);
lean_dec(v_b_5610_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5636_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5621_; 
v___x_5617_ = lean_array_fget_borrowed(v___x_5605_, v_a_5609_);
v___x_5618_ = lean_array_get_size(v___x_5617_);
v___x_5619_ = lean_unsigned_to_nat(0u);
if (v_isShared_5616_ == 0)
{
v___x_5621_ = v___x_5615_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_fst_5612_);
lean_ctor_set(v_reuseFailAlloc_5635_, 1, v_snd_5613_);
v___x_5621_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
lean_object* v___x_5622_; lean_object* v_fst_5623_; lean_object* v_snd_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5634_; 
v___x_5622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5618_, v___x_5617_, v___x_5606_, v___x_5607_, v_fixedParamPerms_5608_, v_a_5609_, v___x_5619_, v___x_5621_);
v_fst_5623_ = lean_ctor_get(v___x_5622_, 0);
v_snd_5624_ = lean_ctor_get(v___x_5622_, 1);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5622_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5626_ = v___x_5622_;
v_isShared_5627_ = v_isSharedCheck_5634_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_snd_5624_);
lean_inc(v_fst_5623_);
lean_dec(v___x_5622_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5634_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v___x_5629_; 
if (v_isShared_5627_ == 0)
{
v___x_5629_ = v___x_5626_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v_snd_5624_);
v___x_5629_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5630_ = lean_unsigned_to_nat(1u);
v___x_5631_ = lean_nat_add(v_a_5609_, v___x_5630_);
lean_dec(v_a_5609_);
v_a_5609_ = v___x_5631_;
v_b_5610_ = v___x_5629_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5637_, lean_object* v___x_5638_, lean_object* v___x_5639_, lean_object* v___x_5640_, lean_object* v_fixedParamPerms_5641_, lean_object* v_a_5642_, lean_object* v_b_5643_){
_start:
{
lean_object* v_res_5644_; 
v_res_5644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5637_, v___x_5638_, v___x_5639_, v___x_5640_, v_fixedParamPerms_5641_, v_a_5642_, v_b_5643_);
lean_dec_ref(v_fixedParamPerms_5641_);
lean_dec(v___x_5640_);
lean_dec(v___x_5639_);
lean_dec_ref(v___x_5638_);
lean_dec(v_upperBound_5637_);
return v_res_5644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5645_, lean_object* v___x_5646_, lean_object* v___x_5647_, lean_object* v_fixedParamPerms_5648_, lean_object* v_a_5649_){
_start:
{
lean_object* v_snd_5650_; uint8_t v___x_5651_; 
v_snd_5650_ = lean_ctor_get(v_a_5649_, 1);
v___x_5651_ = lean_unbox(v_snd_5650_);
if (v___x_5651_ == 0)
{
lean_object* v_fst_5652_; lean_object* v___x_5654_; uint8_t v_isShared_5655_; uint8_t v_isSharedCheck_5659_; 
lean_inc(v_snd_5650_);
v_fst_5652_ = lean_ctor_get(v_a_5649_, 0);
v_isSharedCheck_5659_ = !lean_is_exclusive(v_a_5649_);
if (v_isSharedCheck_5659_ == 0)
{
lean_object* v_unused_5660_; 
v_unused_5660_ = lean_ctor_get(v_a_5649_, 1);
lean_dec(v_unused_5660_);
v___x_5654_ = v_a_5649_;
v_isShared_5655_ = v_isSharedCheck_5659_;
goto v_resetjp_5653_;
}
else
{
lean_inc(v_fst_5652_);
lean_dec(v_a_5649_);
v___x_5654_ = lean_box(0);
v_isShared_5655_ = v_isSharedCheck_5659_;
goto v_resetjp_5653_;
}
v_resetjp_5653_:
{
lean_object* v___x_5657_; 
if (v_isShared_5655_ == 0)
{
v___x_5657_ = v___x_5654_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_fst_5652_);
lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_snd_5650_);
v___x_5657_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
return v___x_5657_;
}
}
}
else
{
lean_object* v_fst_5661_; lean_object* v___x_5663_; uint8_t v_isShared_5664_; uint8_t v_isSharedCheck_5682_; 
v_fst_5661_ = lean_ctor_get(v_a_5649_, 0);
v_isSharedCheck_5682_ = !lean_is_exclusive(v_a_5649_);
if (v_isSharedCheck_5682_ == 0)
{
lean_object* v_unused_5683_; 
v_unused_5683_ = lean_ctor_get(v_a_5649_, 1);
lean_dec(v_unused_5683_);
v___x_5663_ = v_a_5649_;
v_isShared_5664_ = v_isSharedCheck_5682_;
goto v_resetjp_5662_;
}
else
{
lean_inc(v_fst_5661_);
lean_dec(v_a_5649_);
v___x_5663_ = lean_box(0);
v_isShared_5664_ = v_isSharedCheck_5682_;
goto v_resetjp_5662_;
}
v_resetjp_5662_:
{
uint8_t v_changed_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5669_; 
v_changed_5665_ = 0;
v___x_5666_ = lean_unsigned_to_nat(0u);
v___x_5667_ = lean_box(v_changed_5665_);
if (v_isShared_5664_ == 0)
{
lean_ctor_set(v___x_5663_, 1, v___x_5667_);
v___x_5669_ = v___x_5663_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_fst_5661_);
lean_ctor_set(v_reuseFailAlloc_5681_, 1, v___x_5667_);
v___x_5669_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
lean_object* v___x_5670_; lean_object* v_fst_5671_; lean_object* v_snd_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5680_; 
v___x_5670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5645_, v___x_5646_, v___x_5647_, v___x_5645_, v_fixedParamPerms_5648_, v___x_5666_, v___x_5669_);
v_fst_5671_ = lean_ctor_get(v___x_5670_, 0);
v_snd_5672_ = lean_ctor_get(v___x_5670_, 1);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5674_ = v___x_5670_;
v_isShared_5675_ = v_isSharedCheck_5680_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_snd_5672_);
lean_inc(v_fst_5671_);
lean_dec(v___x_5670_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5680_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5677_; 
if (v_isShared_5675_ == 0)
{
v___x_5677_ = v___x_5674_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_fst_5671_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v_snd_5672_);
v___x_5677_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
v_a_5649_ = v___x_5677_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5684_, lean_object* v___x_5685_, lean_object* v___x_5686_, lean_object* v_fixedParamPerms_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5684_, v___x_5685_, v___x_5686_, v_fixedParamPerms_5687_, v_a_5688_);
lean_dec_ref(v_fixedParamPerms_5687_);
lean_dec(v___x_5686_);
lean_dec_ref(v___x_5685_);
lean_dec(v___x_5684_);
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
lean_object* v___x_5825_; uint8_t v___x_5826_; 
v___x_5825_ = lean_array_uget_borrowed(v_as_5821_, v_i_5822_);
v___x_5826_ = l_Lean_Expr_isFVar(v___x_5825_);
if (v___x_5826_ == 0)
{
uint8_t v___x_5827_; 
v___x_5827_ = 1;
return v___x_5827_;
}
else
{
size_t v___x_5828_; size_t v___x_5829_; 
v___x_5828_ = ((size_t)1ULL);
v___x_5829_ = lean_usize_add(v_i_5822_, v___x_5828_);
v_i_5822_ = v___x_5829_;
goto _start;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5839_, size_t v_sz_5840_, size_t v_i_5841_, lean_object* v_bs_5842_){
_start:
{
uint8_t v___x_5843_; 
v___x_5843_ = lean_usize_dec_lt(v_i_5841_, v_sz_5840_);
if (v___x_5843_ == 0)
{
return v_bs_5842_;
}
else
{
lean_object* v_v_5844_; lean_object* v___x_5845_; lean_object* v_bs_x27_5846_; lean_object* v___y_5848_; 
v_v_5844_ = lean_array_uget(v_bs_5842_, v_i_5841_);
v___x_5845_ = lean_unsigned_to_nat(0u);
v_bs_x27_5846_ = lean_array_uset(v_bs_5842_, v_i_5841_, v___x_5845_);
if (lean_obj_tag(v_v_5844_) == 0)
{
v___y_5848_ = v_v_5844_;
goto v___jp_5847_;
}
else
{
lean_object* v_val_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; 
v_val_5853_ = lean_ctor_get(v_v_5844_, 0);
lean_inc(v_val_5853_);
lean_dec_ref_known(v_v_5844_, 1);
v___x_5854_ = lean_box(0);
v___x_5855_ = lean_array_get_borrowed(v___x_5854_, v___x_5839_, v_val_5853_);
lean_dec(v_val_5853_);
lean_inc(v___x_5855_);
v___y_5848_ = v___x_5855_;
goto v___jp_5847_;
}
v___jp_5847_:
{
size_t v___x_5849_; size_t v___x_5850_; lean_object* v___x_5851_; 
v___x_5849_ = ((size_t)1ULL);
v___x_5850_ = lean_usize_add(v_i_5841_, v___x_5849_);
v___x_5851_ = lean_array_uset(v_bs_x27_5846_, v_i_5841_, v___y_5848_);
v_i_5841_ = v___x_5850_;
v_bs_5842_ = v___x_5851_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5856_, lean_object* v_sz_5857_, lean_object* v_i_5858_, lean_object* v_bs_5859_){
_start:
{
size_t v_sz_boxed_5860_; size_t v_i_boxed_5861_; lean_object* v_res_5862_; 
v_sz_boxed_5860_ = lean_unbox_usize(v_sz_5857_);
lean_dec(v_sz_5857_);
v_i_boxed_5861_ = lean_unbox_usize(v_i_5858_);
lean_dec(v_i_5858_);
v_res_5862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5856_, v_sz_boxed_5860_, v_i_boxed_5861_, v_bs_5859_);
lean_dec_ref(v___x_5856_);
return v_res_5862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5863_, size_t v_sz_5864_, size_t v_i_5865_, lean_object* v_bs_5866_){
_start:
{
uint8_t v___x_5867_; 
v___x_5867_ = lean_usize_dec_lt(v_i_5865_, v_sz_5864_);
if (v___x_5867_ == 0)
{
return v_bs_5866_;
}
else
{
lean_object* v_v_5868_; lean_object* v___x_5869_; lean_object* v_bs_x27_5870_; size_t v_sz_5871_; size_t v___x_5872_; lean_object* v___x_5873_; size_t v___x_5874_; size_t v___x_5875_; lean_object* v___x_5876_; 
v_v_5868_ = lean_array_uget(v_bs_5866_, v_i_5865_);
v___x_5869_ = lean_unsigned_to_nat(0u);
v_bs_x27_5870_ = lean_array_uset(v_bs_5866_, v_i_5865_, v___x_5869_);
v_sz_5871_ = lean_array_size(v_v_5868_);
v___x_5872_ = ((size_t)0ULL);
v___x_5873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5863_, v_sz_5871_, v___x_5872_, v_v_5868_);
v___x_5874_ = ((size_t)1ULL);
v___x_5875_ = lean_usize_add(v_i_5865_, v___x_5874_);
v___x_5876_ = lean_array_uset(v_bs_x27_5870_, v_i_5865_, v___x_5873_);
v_i_5865_ = v___x_5875_;
v_bs_5866_ = v___x_5876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5878_, lean_object* v_sz_5879_, lean_object* v_i_5880_, lean_object* v_bs_5881_){
_start:
{
size_t v_sz_boxed_5882_; size_t v_i_boxed_5883_; lean_object* v_res_5884_; 
v_sz_boxed_5882_ = lean_unbox_usize(v_sz_5879_);
lean_dec(v_sz_5879_);
v_i_boxed_5883_ = lean_unbox_usize(v_i_5880_);
lean_dec(v_i_5880_);
v_res_5884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5878_, v_sz_boxed_5882_, v_i_boxed_5883_, v_bs_5881_);
lean_dec_ref(v___x_5878_);
return v_res_5884_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v___x_5887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5888_ = lean_unsigned_to_nat(6u);
v___x_5889_ = lean_unsigned_to_nat(463u);
v___x_5890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5892_ = l_mkPanicMessageWithDecl(v___x_5891_, v___x_5890_, v___x_5889_, v___x_5888_, v___x_5887_);
return v___x_5892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5893_, lean_object* v___x_5894_, lean_object* v___x_5895_, lean_object* v_as_5896_, size_t v_sz_5897_, size_t v_i_5898_, lean_object* v_b_5899_){
_start:
{
lean_object* v_a_5901_; uint8_t v___x_5905_; 
v___x_5905_ = lean_usize_dec_lt(v_i_5898_, v_sz_5897_);
if (v___x_5905_ == 0)
{
return v_b_5899_;
}
else
{
lean_object* v_a_5906_; lean_object* v___x_5907_; uint8_t v___x_5908_; 
v_a_5906_ = lean_array_uget_borrowed(v_as_5896_, v_i_5898_);
v___x_5907_ = lean_array_get_size(v___x_5893_);
v___x_5908_ = lean_nat_dec_lt(v_a_5906_, v___x_5907_);
if (v___x_5908_ == 0)
{
lean_object* v___x_5909_; lean_object* v___x_5910_; 
lean_dec_ref(v_b_5899_);
v___x_5909_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5910_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5909_);
if (lean_obj_tag(v___x_5910_) == 0)
{
lean_object* v_a_5911_; 
v_a_5911_ = lean_ctor_get(v___x_5910_, 0);
lean_inc(v_a_5911_);
lean_dec_ref_known(v___x_5910_, 1);
return v_a_5911_;
}
else
{
lean_object* v_a_5912_; 
v_a_5912_ = lean_ctor_get(v___x_5910_, 0);
lean_inc(v_a_5912_);
lean_dec_ref_known(v___x_5910_, 1);
v_a_5901_ = v_a_5912_;
goto v___jp_5900_;
}
}
else
{
lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5913_ = lean_box(0);
v___x_5914_ = lean_array_get_borrowed(v___x_5913_, v___x_5893_, v_a_5906_);
if (lean_obj_tag(v___x_5914_) == 1)
{
lean_object* v_val_5915_; uint8_t v_changed_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; 
v_val_5915_ = lean_ctor_get(v___x_5914_, 0);
v_changed_5916_ = lean_nat_dec_eq(v___x_5894_, v___x_5895_);
v___x_5917_ = lean_box(v_changed_5916_);
v___x_5918_ = lean_array_set(v_b_5899_, v_val_5915_, v___x_5917_);
v_a_5901_ = v___x_5918_;
goto v___jp_5900_;
}
else
{
v_a_5901_ = v_b_5899_;
goto v___jp_5900_;
}
}
}
v___jp_5900_:
{
size_t v___x_5902_; size_t v___x_5903_; 
v___x_5902_ = ((size_t)1ULL);
v___x_5903_ = lean_usize_add(v_i_5898_, v___x_5902_);
v_i_5898_ = v___x_5903_;
v_b_5899_ = v_a_5901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5919_, lean_object* v___x_5920_, lean_object* v___x_5921_, lean_object* v_as_5922_, lean_object* v_sz_5923_, lean_object* v_i_5924_, lean_object* v_b_5925_){
_start:
{
size_t v_sz_boxed_5926_; size_t v_i_boxed_5927_; lean_object* v_res_5928_; 
v_sz_boxed_5926_ = lean_unbox_usize(v_sz_5923_);
lean_dec(v_sz_5923_);
v_i_boxed_5927_ = lean_unbox_usize(v_i_5924_);
lean_dec(v_i_5924_);
v_res_5928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5919_, v___x_5920_, v___x_5921_, v_as_5922_, v_sz_boxed_5926_, v_i_boxed_5927_, v_b_5925_);
lean_dec_ref(v_as_5922_);
lean_dec(v___x_5921_);
lean_dec(v___x_5920_);
lean_dec_ref(v___x_5919_);
return v_res_5928_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5929_, lean_object* v___x_5930_, lean_object* v___x_5931_, lean_object* v_a_5932_, lean_object* v_b_5933_){
_start:
{
uint8_t v___x_5934_; 
v___x_5934_ = lean_nat_dec_lt(v_a_5932_, v_upperBound_5929_);
if (v___x_5934_ == 0)
{
lean_dec(v_a_5932_);
return v_b_5933_;
}
else
{
lean_object* v_snd_5935_; lean_object* v_snd_5936_; lean_object* v_fst_5937_; lean_object* v___x_5939_; uint8_t v_isShared_5940_; uint8_t v_isSharedCheck_6003_; 
v_snd_5935_ = lean_ctor_get(v_b_5933_, 1);
lean_inc(v_snd_5935_);
v_snd_5936_ = lean_ctor_get(v_snd_5935_, 1);
lean_inc(v_snd_5936_);
v_fst_5937_ = lean_ctor_get(v_b_5933_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v_b_5933_);
if (v_isSharedCheck_6003_ == 0)
{
lean_object* v_unused_6004_; 
v_unused_6004_ = lean_ctor_get(v_b_5933_, 1);
lean_dec(v_unused_6004_);
v___x_5939_ = v_b_5933_;
v_isShared_5940_ = v_isSharedCheck_6003_;
goto v_resetjp_5938_;
}
else
{
lean_inc(v_fst_5937_);
lean_dec(v_b_5933_);
v___x_5939_ = lean_box(0);
v_isShared_5940_ = v_isSharedCheck_6003_;
goto v_resetjp_5938_;
}
v_resetjp_5938_:
{
lean_object* v_fst_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_6001_; 
v_fst_5941_ = lean_ctor_get(v_snd_5935_, 0);
v_isSharedCheck_6001_ = !lean_is_exclusive(v_snd_5935_);
if (v_isSharedCheck_6001_ == 0)
{
lean_object* v_unused_6002_; 
v_unused_6002_ = lean_ctor_get(v_snd_5935_, 1);
lean_dec(v_unused_6002_);
v___x_5943_ = v_snd_5935_;
v_isShared_5944_ = v_isSharedCheck_6001_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_fst_5941_);
lean_dec(v_snd_5935_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_6001_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
lean_object* v_array_5945_; lean_object* v_start_5946_; lean_object* v_stop_5947_; uint8_t v___x_5948_; 
v_array_5945_ = lean_ctor_get(v_snd_5936_, 0);
v_start_5946_ = lean_ctor_get(v_snd_5936_, 1);
v_stop_5947_ = lean_ctor_get(v_snd_5936_, 2);
v___x_5948_ = lean_nat_dec_lt(v_start_5946_, v_stop_5947_);
if (v___x_5948_ == 0)
{
lean_object* v___x_5950_; 
lean_dec(v_a_5932_);
if (v_isShared_5944_ == 0)
{
v___x_5950_ = v___x_5943_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_fst_5941_);
lean_ctor_set(v_reuseFailAlloc_5954_, 1, v_snd_5936_);
v___x_5950_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
lean_object* v___x_5952_; 
if (v_isShared_5940_ == 0)
{
lean_ctor_set(v___x_5939_, 1, v___x_5950_);
v___x_5952_ = v___x_5939_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v_fst_5937_);
lean_ctor_set(v_reuseFailAlloc_5953_, 1, v___x_5950_);
v___x_5952_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
return v___x_5952_;
}
}
}
else
{
lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_5997_; 
lean_inc(v_stop_5947_);
lean_inc(v_start_5946_);
lean_inc_ref(v_array_5945_);
v_isSharedCheck_5997_ = !lean_is_exclusive(v_snd_5936_);
if (v_isSharedCheck_5997_ == 0)
{
lean_object* v_unused_5998_; lean_object* v_unused_5999_; lean_object* v_unused_6000_; 
v_unused_5998_ = lean_ctor_get(v_snd_5936_, 2);
lean_dec(v_unused_5998_);
v_unused_5999_ = lean_ctor_get(v_snd_5936_, 1);
lean_dec(v_unused_5999_);
v_unused_6000_ = lean_ctor_get(v_snd_5936_, 0);
lean_dec(v_unused_6000_);
v___x_5956_ = v_snd_5936_;
v_isShared_5957_ = v_isSharedCheck_5997_;
goto v_resetjp_5955_;
}
else
{
lean_dec(v_snd_5936_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_5997_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
lean_object* v_array_5958_; lean_object* v_start_5959_; lean_object* v_stop_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5965_; 
v_array_5958_ = lean_ctor_get(v_fst_5941_, 0);
v_start_5959_ = lean_ctor_get(v_fst_5941_, 1);
v_stop_5960_ = lean_ctor_get(v_fst_5941_, 2);
v___x_5961_ = lean_array_fget(v_array_5945_, v_start_5946_);
v___x_5962_ = lean_unsigned_to_nat(1u);
v___x_5963_ = lean_nat_add(v_start_5946_, v___x_5962_);
lean_dec(v_start_5946_);
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 1, v___x_5963_);
v___x_5965_ = v___x_5956_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5996_; 
v_reuseFailAlloc_5996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5996_, 0, v_array_5945_);
lean_ctor_set(v_reuseFailAlloc_5996_, 1, v___x_5963_);
lean_ctor_set(v_reuseFailAlloc_5996_, 2, v_stop_5947_);
v___x_5965_ = v_reuseFailAlloc_5996_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
uint8_t v___x_5966_; 
v___x_5966_ = lean_nat_dec_lt(v_start_5959_, v_stop_5960_);
if (v___x_5966_ == 0)
{
lean_object* v___x_5968_; 
lean_dec(v___x_5961_);
lean_dec(v_a_5932_);
if (v_isShared_5944_ == 0)
{
lean_ctor_set(v___x_5943_, 1, v___x_5965_);
v___x_5968_ = v___x_5943_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_fst_5941_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___x_5965_);
v___x_5968_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
lean_object* v___x_5970_; 
if (v_isShared_5940_ == 0)
{
lean_ctor_set(v___x_5939_, 1, v___x_5968_);
v___x_5970_ = v___x_5939_;
goto v_reusejp_5969_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_fst_5937_);
lean_ctor_set(v_reuseFailAlloc_5971_, 1, v___x_5968_);
v___x_5970_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5969_;
}
v_reusejp_5969_:
{
return v___x_5970_;
}
}
}
else
{
lean_object* v___x_5974_; uint8_t v_isShared_5975_; uint8_t v_isSharedCheck_5992_; 
lean_inc(v_stop_5960_);
lean_inc(v_start_5959_);
lean_inc_ref(v_array_5958_);
v_isSharedCheck_5992_ = !lean_is_exclusive(v_fst_5941_);
if (v_isSharedCheck_5992_ == 0)
{
lean_object* v_unused_5993_; lean_object* v_unused_5994_; lean_object* v_unused_5995_; 
v_unused_5993_ = lean_ctor_get(v_fst_5941_, 2);
lean_dec(v_unused_5993_);
v_unused_5994_ = lean_ctor_get(v_fst_5941_, 1);
lean_dec(v_unused_5994_);
v_unused_5995_ = lean_ctor_get(v_fst_5941_, 0);
lean_dec(v_unused_5995_);
v___x_5974_ = v_fst_5941_;
v_isShared_5975_ = v_isSharedCheck_5992_;
goto v_resetjp_5973_;
}
else
{
lean_dec(v_fst_5941_);
v___x_5974_ = lean_box(0);
v_isShared_5975_ = v_isSharedCheck_5992_;
goto v_resetjp_5973_;
}
v_resetjp_5973_:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5979_; 
v___x_5976_ = lean_array_fget(v_array_5958_, v_start_5959_);
v___x_5977_ = lean_nat_add(v_start_5959_, v___x_5962_);
lean_dec(v_start_5959_);
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 1, v___x_5977_);
v___x_5979_ = v___x_5974_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_array_5958_);
lean_ctor_set(v_reuseFailAlloc_5991_, 1, v___x_5977_);
lean_ctor_set(v_reuseFailAlloc_5991_, 2, v_stop_5960_);
v___x_5979_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
size_t v_sz_5980_; size_t v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5984_; 
v_sz_5980_ = lean_array_size(v___x_5976_);
v___x_5981_ = ((size_t)0ULL);
v___x_5982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5961_, v___x_5930_, v___x_5931_, v___x_5976_, v_sz_5980_, v___x_5981_, v_fst_5937_);
lean_dec(v___x_5976_);
lean_dec(v___x_5961_);
if (v_isShared_5944_ == 0)
{
lean_ctor_set(v___x_5943_, 1, v___x_5965_);
lean_ctor_set(v___x_5943_, 0, v___x_5979_);
v___x_5984_ = v___x_5943_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5965_);
v___x_5984_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
lean_object* v___x_5986_; 
if (v_isShared_5940_ == 0)
{
lean_ctor_set(v___x_5939_, 1, v___x_5984_);
lean_ctor_set(v___x_5939_, 0, v___x_5982_);
v___x_5986_ = v___x_5939_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5982_);
lean_ctor_set(v_reuseFailAlloc_5989_, 1, v___x_5984_);
v___x_5986_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
lean_object* v___x_5987_; 
v___x_5987_ = lean_nat_add(v_a_5932_, v___x_5962_);
lean_dec(v_a_5932_);
v_a_5932_ = v___x_5987_;
v_b_5933_ = v___x_5986_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6005_, lean_object* v___x_6006_, lean_object* v___x_6007_, lean_object* v_a_6008_, lean_object* v_b_6009_){
_start:
{
lean_object* v_res_6010_; 
v_res_6010_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6005_, v___x_6006_, v___x_6007_, v_a_6008_, v_b_6009_);
lean_dec(v___x_6007_);
lean_dec(v___x_6006_);
lean_dec(v_upperBound_6005_);
return v_res_6010_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6012_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6013_ = lean_unsigned_to_nat(2u);
v___x_6014_ = lean_unsigned_to_nat(457u);
v___x_6015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6016_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6017_ = l_mkPanicMessageWithDecl(v___x_6016_, v___x_6015_, v___x_6014_, v___x_6013_, v___x_6012_);
return v___x_6017_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; 
v___x_6019_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6020_ = lean_unsigned_to_nat(2u);
v___x_6021_ = lean_unsigned_to_nat(458u);
v___x_6022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6023_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6024_ = l_mkPanicMessageWithDecl(v___x_6023_, v___x_6022_, v___x_6021_, v___x_6020_, v___x_6019_);
return v___x_6024_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; 
v___x_6026_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6027_ = lean_unsigned_to_nat(2u);
v___x_6028_ = lean_unsigned_to_nat(456u);
v___x_6029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6030_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6031_ = l_mkPanicMessageWithDecl(v___x_6030_, v___x_6029_, v___x_6028_, v___x_6027_, v___x_6026_);
return v___x_6031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6032_, lean_object* v_xs_6033_, lean_object* v_toErase_6034_){
_start:
{
lean_object* v___x_6035_; lean_object* v___x_6036_; uint8_t v___x_6120_; 
v___x_6035_ = lean_unsigned_to_nat(0u);
v___x_6036_ = lean_array_get_size(v_xs_6033_);
v___x_6120_ = lean_nat_dec_lt(v___x_6035_, v___x_6036_);
if (v___x_6120_ == 0)
{
goto v___jp_6037_;
}
else
{
if (v___x_6120_ == 0)
{
goto v___jp_6037_;
}
else
{
size_t v___x_6121_; size_t v___x_6122_; uint8_t v___x_6123_; 
v___x_6121_ = ((size_t)0ULL);
v___x_6122_ = lean_usize_of_nat(v___x_6036_);
v___x_6123_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6033_, v___x_6121_, v___x_6122_);
if (v___x_6123_ == 0)
{
goto v___jp_6037_;
}
else
{
lean_object* v___x_6124_; lean_object* v___x_6125_; 
lean_dec_ref(v_toErase_6034_);
lean_dec_ref(v_xs_6033_);
lean_dec_ref(v_fixedParamPerms_6032_);
v___x_6124_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6125_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6124_);
return v___x_6125_;
}
}
}
v___jp_6037_:
{
lean_object* v_numFixed_6038_; lean_object* v_perms_6039_; lean_object* v_revDeps_6040_; uint8_t v___x_6041_; 
v_numFixed_6038_ = lean_ctor_get(v_fixedParamPerms_6032_, 0);
v_perms_6039_ = lean_ctor_get(v_fixedParamPerms_6032_, 1);
lean_inc_ref(v_perms_6039_);
v_revDeps_6040_ = lean_ctor_get(v_fixedParamPerms_6032_, 2);
lean_inc_ref(v_revDeps_6040_);
v___x_6041_ = lean_nat_dec_eq(v_numFixed_6038_, v___x_6036_);
if (v___x_6041_ == 0)
{
lean_object* v___x_6042_; lean_object* v___x_6043_; 
lean_dec_ref(v_revDeps_6040_);
lean_dec_ref(v_perms_6039_);
lean_dec_ref(v_toErase_6034_);
lean_dec_ref(v_xs_6033_);
lean_dec_ref(v_fixedParamPerms_6032_);
v___x_6042_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6043_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6042_);
return v___x_6043_;
}
else
{
lean_object* v___x_6044_; lean_object* v___x_6045_; uint8_t v_changed_6046_; 
v___x_6044_ = lean_array_get_size(v_toErase_6034_);
v___x_6045_ = lean_array_get_size(v_perms_6039_);
v_changed_6046_ = lean_nat_dec_eq(v___x_6044_, v___x_6045_);
if (v_changed_6046_ == 0)
{
lean_object* v___x_6047_; lean_object* v___x_6048_; 
lean_dec_ref(v_revDeps_6040_);
lean_dec_ref(v_perms_6039_);
lean_dec_ref(v_toErase_6034_);
lean_dec_ref(v_xs_6033_);
lean_dec_ref(v_fixedParamPerms_6032_);
v___x_6047_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6048_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6047_);
return v___x_6048_;
}
else
{
uint8_t v_changed_6049_; lean_object* v___x_6050_; lean_object* v_mask_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v_fst_6057_; lean_object* v___x_6059_; uint8_t v_isShared_6060_; uint8_t v_isSharedCheck_6118_; 
v_changed_6049_ = 0;
v___x_6050_ = lean_box(v_changed_6049_);
lean_inc(v_numFixed_6038_);
v_mask_6051_ = lean_mk_array(v_numFixed_6038_, v___x_6050_);
v___x_6052_ = l_Array_toSubarray___redArg(v_toErase_6034_, v___x_6035_, v___x_6044_);
lean_inc_ref(v_perms_6039_);
v___x_6053_ = l_Array_toSubarray___redArg(v_perms_6039_, v___x_6035_, v___x_6045_);
v___x_6054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6052_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6055_, 0, v_mask_6051_);
lean_ctor_set(v___x_6055_, 1, v___x_6054_);
v___x_6056_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6044_, v___x_6044_, v___x_6045_, v___x_6035_, v___x_6055_);
v_fst_6057_ = lean_ctor_get(v___x_6056_, 0);
v_isSharedCheck_6118_ = !lean_is_exclusive(v___x_6056_);
if (v_isSharedCheck_6118_ == 0)
{
lean_object* v_unused_6119_; 
v_unused_6119_ = lean_ctor_get(v___x_6056_, 1);
lean_dec(v_unused_6119_);
v___x_6059_ = v___x_6056_;
v_isShared_6060_ = v_isSharedCheck_6118_;
goto v_resetjp_6058_;
}
else
{
lean_inc(v_fst_6057_);
lean_dec(v___x_6056_);
v___x_6059_ = lean_box(0);
v_isShared_6060_ = v_isSharedCheck_6118_;
goto v_resetjp_6058_;
}
v_resetjp_6058_:
{
lean_object* v___x_6061_; lean_object* v___x_6063_; 
v___x_6061_ = lean_box(v_changed_6046_);
if (v_isShared_6060_ == 0)
{
lean_ctor_set(v___x_6059_, 1, v___x_6061_);
v___x_6063_ = v___x_6059_;
goto v_reusejp_6062_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_fst_6057_);
lean_ctor_set(v_reuseFailAlloc_6117_, 1, v___x_6061_);
v___x_6063_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6062_;
}
v_reusejp_6062_:
{
lean_object* v___x_6064_; lean_object* v___x_6066_; uint8_t v_isShared_6067_; uint8_t v_isSharedCheck_6113_; 
v___x_6064_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6045_, v_perms_6039_, v___x_6044_, v_fixedParamPerms_6032_, v___x_6063_);
v_isSharedCheck_6113_ = !lean_is_exclusive(v_fixedParamPerms_6032_);
if (v_isSharedCheck_6113_ == 0)
{
lean_object* v_unused_6114_; lean_object* v_unused_6115_; lean_object* v_unused_6116_; 
v_unused_6114_ = lean_ctor_get(v_fixedParamPerms_6032_, 2);
lean_dec(v_unused_6114_);
v_unused_6115_ = lean_ctor_get(v_fixedParamPerms_6032_, 1);
lean_dec(v_unused_6115_);
v_unused_6116_ = lean_ctor_get(v_fixedParamPerms_6032_, 0);
lean_dec(v_unused_6116_);
v___x_6066_ = v_fixedParamPerms_6032_;
v_isShared_6067_ = v_isSharedCheck_6113_;
goto v_resetjp_6065_;
}
else
{
lean_dec(v_fixedParamPerms_6032_);
v___x_6066_ = lean_box(0);
v_isShared_6067_ = v_isSharedCheck_6113_;
goto v_resetjp_6065_;
}
v_resetjp_6065_:
{
lean_object* v_fst_6068_; lean_object* v___x_6070_; uint8_t v_isShared_6071_; uint8_t v_isSharedCheck_6111_; 
v_fst_6068_ = lean_ctor_get(v___x_6064_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6064_);
if (v_isSharedCheck_6111_ == 0)
{
lean_object* v_unused_6112_; 
v_unused_6112_ = lean_ctor_get(v___x_6064_, 1);
lean_dec(v_unused_6112_);
v___x_6070_ = v___x_6064_;
v_isShared_6071_ = v_isSharedCheck_6111_;
goto v_resetjp_6069_;
}
else
{
lean_inc(v_fst_6068_);
lean_dec(v___x_6064_);
v___x_6070_ = lean_box(0);
v_isShared_6071_ = v_isSharedCheck_6111_;
goto v_resetjp_6069_;
}
v_resetjp_6069_:
{
lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6077_; 
v___x_6072_ = lean_array_get_size(v_fst_6068_);
v___x_6073_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6074_ = l_Array_toSubarray___redArg(v_fst_6068_, v___x_6035_, v___x_6072_);
v___x_6075_ = l_Array_toSubarray___redArg(v_xs_6033_, v___x_6035_, v___x_6036_);
if (v_isShared_6071_ == 0)
{
lean_ctor_set(v___x_6070_, 1, v___x_6075_);
lean_ctor_set(v___x_6070_, 0, v___x_6074_);
v___x_6077_ = v___x_6070_;
goto v_reusejp_6076_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v___x_6074_);
lean_ctor_set(v_reuseFailAlloc_6110_, 1, v___x_6075_);
v___x_6077_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6076_;
}
v_reusejp_6076_:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v_snd_6082_; lean_object* v_snd_6083_; lean_object* v_fst_6084_; lean_object* v_fst_6085_; lean_object* v___x_6087_; uint8_t v_isShared_6088_; uint8_t v_isSharedCheck_6108_; 
v___x_6078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6073_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6073_);
lean_ctor_set(v___x_6079_, 1, v___x_6078_);
v___x_6080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6073_);
lean_ctor_set(v___x_6080_, 1, v___x_6079_);
v___x_6081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6072_, v___x_6035_, v___x_6080_);
v_snd_6082_ = lean_ctor_get(v___x_6081_, 1);
lean_inc(v_snd_6082_);
v_snd_6083_ = lean_ctor_get(v_snd_6082_, 1);
lean_inc(v_snd_6083_);
v_fst_6084_ = lean_ctor_get(v___x_6081_, 0);
lean_inc(v_fst_6084_);
lean_dec_ref(v___x_6081_);
v_fst_6085_ = lean_ctor_get(v_snd_6082_, 0);
v_isSharedCheck_6108_ = !lean_is_exclusive(v_snd_6082_);
if (v_isSharedCheck_6108_ == 0)
{
lean_object* v_unused_6109_; 
v_unused_6109_ = lean_ctor_get(v_snd_6082_, 1);
lean_dec(v_unused_6109_);
v___x_6087_ = v_snd_6082_;
v_isShared_6088_ = v_isSharedCheck_6108_;
goto v_resetjp_6086_;
}
else
{
lean_inc(v_fst_6085_);
lean_dec(v_snd_6082_);
v___x_6087_ = lean_box(0);
v_isShared_6088_ = v_isSharedCheck_6108_;
goto v_resetjp_6086_;
}
v_resetjp_6086_:
{
lean_object* v_fst_6089_; lean_object* v___x_6091_; uint8_t v_isShared_6092_; uint8_t v_isSharedCheck_6106_; 
v_fst_6089_ = lean_ctor_get(v_snd_6083_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v_snd_6083_);
if (v_isSharedCheck_6106_ == 0)
{
lean_object* v_unused_6107_; 
v_unused_6107_ = lean_ctor_get(v_snd_6083_, 1);
lean_dec(v_unused_6107_);
v___x_6091_ = v_snd_6083_;
v_isShared_6092_ = v_isSharedCheck_6106_;
goto v_resetjp_6090_;
}
else
{
lean_inc(v_fst_6089_);
lean_dec(v_snd_6083_);
v___x_6091_ = lean_box(0);
v_isShared_6092_ = v_isSharedCheck_6106_;
goto v_resetjp_6090_;
}
v_resetjp_6090_:
{
lean_object* v___x_6093_; size_t v_sz_6094_; size_t v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6098_; 
v___x_6093_ = lean_array_get_size(v_fst_6089_);
v_sz_6094_ = lean_array_size(v_perms_6039_);
v___x_6095_ = ((size_t)0ULL);
v___x_6096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6084_, v_sz_6094_, v___x_6095_, v_perms_6039_);
lean_dec(v_fst_6084_);
if (v_isShared_6067_ == 0)
{
lean_ctor_set(v___x_6066_, 1, v___x_6096_);
lean_ctor_set(v___x_6066_, 0, v___x_6093_);
v___x_6098_ = v___x_6066_;
goto v_reusejp_6097_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6093_);
lean_ctor_set(v_reuseFailAlloc_6105_, 1, v___x_6096_);
lean_ctor_set(v_reuseFailAlloc_6105_, 2, v_revDeps_6040_);
v___x_6098_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6097_;
}
v_reusejp_6097_:
{
lean_object* v___x_6100_; 
if (v_isShared_6092_ == 0)
{
lean_ctor_set(v___x_6091_, 1, v_fst_6085_);
v___x_6100_ = v___x_6091_;
goto v_reusejp_6099_;
}
else
{
lean_object* v_reuseFailAlloc_6104_; 
v_reuseFailAlloc_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6104_, 0, v_fst_6089_);
lean_ctor_set(v_reuseFailAlloc_6104_, 1, v_fst_6085_);
v___x_6100_ = v_reuseFailAlloc_6104_;
goto v_reusejp_6099_;
}
v_reusejp_6099_:
{
lean_object* v___x_6102_; 
if (v_isShared_6088_ == 0)
{
lean_ctor_set(v___x_6087_, 1, v___x_6100_);
lean_ctor_set(v___x_6087_, 0, v___x_6098_);
v___x_6102_ = v___x_6087_;
goto v_reusejp_6101_;
}
else
{
lean_object* v_reuseFailAlloc_6103_; 
v_reuseFailAlloc_6103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6103_, 0, v___x_6098_);
lean_ctor_set(v_reuseFailAlloc_6103_, 1, v___x_6100_);
v___x_6102_ = v_reuseFailAlloc_6103_;
goto v_reusejp_6101_;
}
v_reusejp_6101_:
{
return v___x_6102_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6126_, lean_object* v___x_6127_, lean_object* v___x_6128_, lean_object* v___x_6129_, lean_object* v_fixedParamPerms_6130_, lean_object* v_next_6131_, lean_object* v_inst_6132_, lean_object* v_R_6133_, lean_object* v_a_6134_, lean_object* v_b_6135_, lean_object* v_c_6136_){
_start:
{
lean_object* v___x_6137_; 
v___x_6137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6126_, v___x_6127_, v___x_6128_, v___x_6129_, v_fixedParamPerms_6130_, v_next_6131_, v_a_6134_, v_b_6135_);
return v___x_6137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6138_, lean_object* v___x_6139_, lean_object* v___x_6140_, lean_object* v___x_6141_, lean_object* v_fixedParamPerms_6142_, lean_object* v_next_6143_, lean_object* v_inst_6144_, lean_object* v_R_6145_, lean_object* v_a_6146_, lean_object* v_b_6147_, lean_object* v_c_6148_){
_start:
{
lean_object* v_res_6149_; 
v_res_6149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6138_, v___x_6139_, v___x_6140_, v___x_6141_, v_fixedParamPerms_6142_, v_next_6143_, v_inst_6144_, v_R_6145_, v_a_6146_, v_b_6147_, v_c_6148_);
lean_dec(v_a_6146_);
lean_dec(v_next_6143_);
lean_dec_ref(v_fixedParamPerms_6142_);
lean_dec(v___x_6141_);
lean_dec(v___x_6140_);
lean_dec_ref(v___x_6139_);
lean_dec(v_upperBound_6138_);
return v_res_6149_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6150_, lean_object* v___x_6151_, lean_object* v___x_6152_, lean_object* v___x_6153_, lean_object* v_fixedParamPerms_6154_, lean_object* v_inst_6155_, lean_object* v_R_6156_, lean_object* v_a_6157_, lean_object* v_b_6158_, lean_object* v_c_6159_){
_start:
{
lean_object* v___x_6160_; 
v___x_6160_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6150_, v___x_6151_, v___x_6152_, v___x_6153_, v_fixedParamPerms_6154_, v_a_6157_, v_b_6158_);
return v___x_6160_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6161_, lean_object* v___x_6162_, lean_object* v___x_6163_, lean_object* v___x_6164_, lean_object* v_fixedParamPerms_6165_, lean_object* v_inst_6166_, lean_object* v_R_6167_, lean_object* v_a_6168_, lean_object* v_b_6169_, lean_object* v_c_6170_){
_start:
{
lean_object* v_res_6171_; 
v_res_6171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6161_, v___x_6162_, v___x_6163_, v___x_6164_, v_fixedParamPerms_6165_, v_inst_6166_, v_R_6167_, v_a_6168_, v_b_6169_, v_c_6170_);
lean_dec_ref(v_fixedParamPerms_6165_);
lean_dec(v___x_6164_);
lean_dec(v___x_6163_);
lean_dec_ref(v___x_6162_);
lean_dec(v_upperBound_6161_);
return v_res_6171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6172_, lean_object* v___x_6173_, lean_object* v___x_6174_, lean_object* v_fixedParamPerms_6175_, lean_object* v_inst_6176_, lean_object* v_a_6177_){
_start:
{
lean_object* v___x_6178_; 
v___x_6178_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6172_, v___x_6173_, v___x_6174_, v_fixedParamPerms_6175_, v_a_6177_);
return v___x_6178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6179_, lean_object* v___x_6180_, lean_object* v___x_6181_, lean_object* v_fixedParamPerms_6182_, lean_object* v_inst_6183_, lean_object* v_a_6184_){
_start:
{
lean_object* v_res_6185_; 
v_res_6185_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6179_, v___x_6180_, v___x_6181_, v_fixedParamPerms_6182_, v_inst_6183_, v_a_6184_);
lean_dec_ref(v_fixedParamPerms_6182_);
lean_dec(v___x_6181_);
lean_dec_ref(v___x_6180_);
lean_dec(v___x_6179_);
return v_res_6185_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6186_, lean_object* v_inst_6187_, lean_object* v_R_6188_, lean_object* v_a_6189_, lean_object* v_b_6190_, lean_object* v_c_6191_){
_start:
{
lean_object* v___x_6192_; 
v___x_6192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6186_, v_a_6189_, v_b_6190_);
return v___x_6192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6193_, lean_object* v_inst_6194_, lean_object* v_R_6195_, lean_object* v_a_6196_, lean_object* v_b_6197_, lean_object* v_c_6198_){
_start:
{
lean_object* v_res_6199_; 
v_res_6199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6193_, v_inst_6194_, v_R_6195_, v_a_6196_, v_b_6197_, v_c_6198_);
lean_dec(v_upperBound_6193_);
return v_res_6199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6200_, lean_object* v___x_6201_, lean_object* v___x_6202_, lean_object* v_inst_6203_, lean_object* v_R_6204_, lean_object* v_a_6205_, lean_object* v_b_6206_, lean_object* v_c_6207_){
_start:
{
lean_object* v___x_6208_; 
v___x_6208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6200_, v___x_6201_, v___x_6202_, v_a_6205_, v_b_6206_);
return v___x_6208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6209_, lean_object* v___x_6210_, lean_object* v___x_6211_, lean_object* v_inst_6212_, lean_object* v_R_6213_, lean_object* v_a_6214_, lean_object* v_b_6215_, lean_object* v_c_6216_){
_start:
{
lean_object* v_res_6217_; 
v_res_6217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6209_, v___x_6210_, v___x_6211_, v_inst_6212_, v_R_6213_, v_a_6214_, v_b_6215_, v_c_6216_);
lean_dec(v___x_6211_);
lean_dec(v___x_6210_);
lean_dec(v_upperBound_6209_);
return v_res_6217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object* v_upperBound_6218_, lean_object* v___x_6219_, lean_object* v_fixedParamPerms_6220_, lean_object* v_next_6221_, lean_object* v___x_6222_, lean_object* v___x_6223_, lean_object* v_inst_6224_, lean_object* v_R_6225_, lean_object* v_a_6226_, lean_object* v_b_6227_, lean_object* v_c_6228_){
_start:
{
lean_object* v___x_6229_; 
v___x_6229_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_6218_, v___x_6219_, v_fixedParamPerms_6220_, v_next_6221_, v___x_6222_, v___x_6223_, v_a_6226_, v_b_6227_);
return v___x_6229_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object* v_upperBound_6230_, lean_object* v___x_6231_, lean_object* v_fixedParamPerms_6232_, lean_object* v_next_6233_, lean_object* v___x_6234_, lean_object* v___x_6235_, lean_object* v_inst_6236_, lean_object* v_R_6237_, lean_object* v_a_6238_, lean_object* v_b_6239_, lean_object* v_c_6240_){
_start:
{
lean_object* v_res_6241_; 
v_res_6241_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(v_upperBound_6230_, v___x_6231_, v_fixedParamPerms_6232_, v_next_6233_, v___x_6234_, v___x_6235_, v_inst_6236_, v_R_6237_, v_a_6238_, v_b_6239_, v_c_6240_);
lean_dec(v___x_6235_);
lean_dec(v___x_6234_);
lean_dec(v_next_6233_);
lean_dec_ref(v_fixedParamPerms_6232_);
lean_dec_ref(v___x_6231_);
lean_dec(v_upperBound_6230_);
return v_res_6241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6299_; uint8_t v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; 
v___x_6299_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6300_ = 0;
v___x_6301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6302_ = l_Lean_registerTraceClass(v___x_6299_, v___x_6300_, v___x_6301_);
return v___x_6302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6303_){
_start:
{
lean_object* v_res_6304_; 
v_res_6304_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6304_;
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
