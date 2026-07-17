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
lean_object* v___f_1009_; lean_object* v___x_30953__overap_1010_; lean_object* v___x_1011_; 
v___f_1009_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_30953__overap_1010_ = lean_panic_fn_borrowed(v___f_1009_, v_msg_1003_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
v___x_1011_ = lean_apply_5(v___x_30953__overap_1010_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, lean_box(0));
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_upperBound_2402_, lean_object* v_val_2403_, lean_object* v_next_2404_, lean_object* v_params_2405_, lean_object* v___x_2406_, lean_object* v_val_2407_, lean_object* v_next_2408_, uint8_t v___x_2409_, lean_object* v_a_2410_, uint8_t v_b_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
uint8_t v_a_2418_; uint8_t v___x_2422_; 
v___x_2422_ = lean_nat_dec_lt(v_a_2410_, v_upperBound_2402_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec(v_a_2410_);
lean_dec(v_next_2408_);
lean_dec_ref(v___x_2406_);
v___x_2423_ = lean_box(v_b_2411_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = lean_st_ref_get(v_val_2403_);
v___x_2426_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2404_, v_a_2410_, v___x_2425_);
lean_dec(v___x_2425_);
if (v___x_2426_ == 0)
{
v_a_2418_ = v_b_2411_;
goto v___jp_2417_;
}
else
{
lean_object* v___x_2427_; uint8_t v_foApprox_2428_; uint8_t v_ctxApprox_2429_; uint8_t v_quasiPatternApprox_2430_; uint8_t v_constApprox_2431_; uint8_t v_isDefEqStuckEx_2432_; uint8_t v_unificationHints_2433_; uint8_t v_assignSyntheticOpaque_2434_; uint8_t v_offsetCnstrs_2435_; uint8_t v_transparency_2436_; uint8_t v_etaStruct_2437_; uint8_t v_univApprox_2438_; uint8_t v_iota_2439_; uint8_t v_beta_2440_; uint8_t v_proj_2441_; uint8_t v_zeta_2442_; uint8_t v_zetaDelta_2443_; uint8_t v_zetaUnused_2444_; uint8_t v_zetaHave_2445_; uint8_t v_canUnfoldPredicateConfig_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2476_; 
v___x_2427_ = l_Lean_Meta_Context_config(v___y_2412_);
v_foApprox_2428_ = lean_ctor_get_uint8(v___x_2427_, 0);
v_ctxApprox_2429_ = lean_ctor_get_uint8(v___x_2427_, 1);
v_quasiPatternApprox_2430_ = lean_ctor_get_uint8(v___x_2427_, 2);
v_constApprox_2431_ = lean_ctor_get_uint8(v___x_2427_, 3);
v_isDefEqStuckEx_2432_ = lean_ctor_get_uint8(v___x_2427_, 4);
v_unificationHints_2433_ = lean_ctor_get_uint8(v___x_2427_, 5);
v_assignSyntheticOpaque_2434_ = lean_ctor_get_uint8(v___x_2427_, 7);
v_offsetCnstrs_2435_ = lean_ctor_get_uint8(v___x_2427_, 8);
v_transparency_2436_ = lean_ctor_get_uint8(v___x_2427_, 9);
v_etaStruct_2437_ = lean_ctor_get_uint8(v___x_2427_, 10);
v_univApprox_2438_ = lean_ctor_get_uint8(v___x_2427_, 11);
v_iota_2439_ = lean_ctor_get_uint8(v___x_2427_, 12);
v_beta_2440_ = lean_ctor_get_uint8(v___x_2427_, 13);
v_proj_2441_ = lean_ctor_get_uint8(v___x_2427_, 14);
v_zeta_2442_ = lean_ctor_get_uint8(v___x_2427_, 15);
v_zetaDelta_2443_ = lean_ctor_get_uint8(v___x_2427_, 16);
v_zetaUnused_2444_ = lean_ctor_get_uint8(v___x_2427_, 17);
v_zetaHave_2445_ = lean_ctor_get_uint8(v___x_2427_, 18);
v_canUnfoldPredicateConfig_2446_ = lean_ctor_get_uint8(v___x_2427_, 19);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2448_ = v___x_2427_;
v_isShared_2449_ = v_isSharedCheck_2476_;
goto v_resetjp_2447_;
}
else
{
lean_dec(v___x_2427_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2476_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint8_t v_trackZetaDelta_2450_; lean_object* v_zetaDeltaSet_2451_; lean_object* v_lctx_2452_; lean_object* v_localInstances_2453_; lean_object* v_defEqCtx_x3f_2454_; lean_object* v_synthPendingDepth_2455_; lean_object* v_customCanUnfoldPredicate_x3f_2456_; uint8_t v_univApprox_2457_; uint8_t v_inTypeClassResolution_2458_; uint8_t v_cacheInferType_2459_; uint8_t v___x_2460_; lean_object* v___x_2462_; 
v_trackZetaDelta_2450_ = lean_ctor_get_uint8(v___y_2412_, sizeof(void*)*7);
v_zetaDeltaSet_2451_ = lean_ctor_get(v___y_2412_, 1);
v_lctx_2452_ = lean_ctor_get(v___y_2412_, 2);
v_localInstances_2453_ = lean_ctor_get(v___y_2412_, 3);
v_defEqCtx_x3f_2454_ = lean_ctor_get(v___y_2412_, 4);
v_synthPendingDepth_2455_ = lean_ctor_get(v___y_2412_, 5);
v_customCanUnfoldPredicate_x3f_2456_ = lean_ctor_get(v___y_2412_, 6);
v_univApprox_2457_ = lean_ctor_get_uint8(v___y_2412_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2458_ = lean_ctor_get_uint8(v___y_2412_, sizeof(void*)*7 + 2);
v_cacheInferType_2459_ = lean_ctor_get_uint8(v___y_2412_, sizeof(void*)*7 + 3);
v___x_2460_ = 0;
if (v_isShared_2449_ == 0)
{
v___x_2462_ = v___x_2448_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 0, v_foApprox_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 1, v_ctxApprox_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 2, v_quasiPatternApprox_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 3, v_constApprox_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 4, v_isDefEqStuckEx_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 5, v_unificationHints_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 7, v_assignSyntheticOpaque_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 8, v_offsetCnstrs_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 9, v_transparency_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 10, v_etaStruct_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 11, v_univApprox_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 12, v_iota_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 13, v_beta_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 14, v_proj_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 15, v_zeta_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 16, v_zetaDelta_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 17, v_zetaUnused_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 18, v_zetaHave_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2475_, 19, v_canUnfoldPredicateConfig_2446_);
v___x_2462_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
uint64_t v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_ctor_set_uint8(v___x_2462_, 6, v___x_2460_);
v___x_2463_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2462_);
v___x_2464_ = lean_array_fget_borrowed(v_params_2405_, v_a_2410_);
v___x_2465_ = 2;
v___x_2466_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2466_, 0, v___x_2462_);
lean_ctor_set_uint64(v___x_2466_, sizeof(void*)*1, v___x_2463_);
v___x_2467_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2465_, v___x_2466_);
lean_inc(v_customCanUnfoldPredicate_x3f_2456_);
lean_inc(v_synthPendingDepth_2455_);
lean_inc(v_defEqCtx_x3f_2454_);
lean_inc_ref(v_localInstances_2453_);
lean_inc_ref(v_lctx_2452_);
lean_inc(v_zetaDeltaSet_2451_);
v___x_2468_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
lean_ctor_set(v___x_2468_, 1, v_zetaDeltaSet_2451_);
lean_ctor_set(v___x_2468_, 2, v_lctx_2452_);
lean_ctor_set(v___x_2468_, 3, v_localInstances_2453_);
lean_ctor_set(v___x_2468_, 4, v_defEqCtx_x3f_2454_);
lean_ctor_set(v___x_2468_, 5, v_synthPendingDepth_2455_);
lean_ctor_set(v___x_2468_, 6, v_customCanUnfoldPredicate_x3f_2456_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*7, v_trackZetaDelta_2450_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*7 + 1, v_univApprox_2457_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2458_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*7 + 3, v_cacheInferType_2459_);
lean_inc_ref(v___x_2406_);
lean_inc(v___x_2464_);
v___x_2469_ = l_Lean_Meta_isExprDefEq(v___x_2464_, v___x_2406_, v___x_2468_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec_ref_known(v___x_2468_, 7);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; uint8_t v___x_2471_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2471_ = lean_unbox(v_a_2470_);
lean_dec(v_a_2470_);
if (v___x_2471_ == 0)
{
v_a_2418_ = v_b_2411_;
goto v___jp_2417_;
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = lean_st_ref_take(v_val_2403_);
lean_inc(v_a_2410_);
lean_inc(v_next_2408_);
v___x_2473_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2407_, v_next_2408_, v_next_2404_, v_a_2410_, v___x_2472_);
v___x_2474_ = lean_st_ref_set(v_val_2403_, v___x_2473_);
v_a_2418_ = v___x_2409_;
goto v___jp_2417_;
}
}
else
{
lean_dec(v_a_2410_);
lean_dec(v_next_2408_);
lean_dec_ref(v___x_2406_);
return v___x_2469_;
}
}
}
}
}
v___jp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_unsigned_to_nat(1u);
v___x_2420_ = lean_nat_add(v_a_2410_, v___x_2419_);
lean_dec(v_a_2410_);
v_a_2410_ = v___x_2420_;
v_b_2411_ = v_a_2418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_upperBound_2477_, lean_object* v_val_2478_, lean_object* v_next_2479_, lean_object* v_params_2480_, lean_object* v___x_2481_, lean_object* v_val_2482_, lean_object* v_next_2483_, lean_object* v___x_2484_, lean_object* v_a_2485_, lean_object* v_b_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
uint8_t v___x_42614__boxed_2492_; uint8_t v_b_boxed_2493_; lean_object* v_res_2494_; 
v___x_42614__boxed_2492_ = lean_unbox(v___x_2484_);
v_b_boxed_2493_ = lean_unbox(v_b_2486_);
v_res_2494_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_2477_, v_val_2478_, v_next_2479_, v_params_2480_, v___x_2481_, v_val_2482_, v_next_2483_, v___x_42614__boxed_2492_, v_a_2485_, v_b_boxed_2493_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v_val_2482_);
lean_dec_ref(v_params_2480_);
lean_dec(v_next_2479_);
lean_dec(v_val_2478_);
lean_dec(v_upperBound_2477_);
return v_res_2494_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2506_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2507_ = l_Lean_Name_append(v___x_2506_, v___x_2505_);
return v___x_2507_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2510_ = l_Lean_stringToMessageData(v___x_2509_);
return v___x_2510_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2515_ = l_Lean_stringToMessageData(v___x_2514_);
return v___x_2515_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2518_ = l_Lean_stringToMessageData(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2521_ = l_Lean_stringToMessageData(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2527_ = l_Lean_stringToMessageData(v___x_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2528_, lean_object* v_val_2529_, lean_object* v_upperBound_2530_, lean_object* v_args_2531_, lean_object* v_e_2532_, lean_object* v_next_2533_, lean_object* v_params_2534_, lean_object* v___x_2535_, uint8_t v___x_2536_, lean_object* v_a_2537_, lean_object* v_b_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_a_2545_; lean_object* v___y_2550_; uint8_t v___x_2569_; 
v___x_2569_ = lean_nat_dec_lt(v_a_2537_, v_upperBound_2530_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_b_2538_);
return v___x_2570_;
}
else
{
lean_object* v___x_2571_; 
v___x_2571_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2528_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2573_ = lean_box(0);
v___x_2574_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2529_, v_a_2537_, v_a_2572_);
lean_dec(v_a_2572_);
if (v___x_2574_ == 0)
{
v_a_2545_ = v___x_2573_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2575_ = lean_array_get_size(v_args_2531_);
v___x_2576_ = lean_nat_dec_lt(v_a_2537_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_object* v_options_2577_; lean_object* v_inheritedTraceOptions_2578_; uint8_t v_hasTrace_2579_; 
v_options_2577_ = lean_ctor_get(v___y_2541_, 2);
v_inheritedTraceOptions_2578_ = lean_ctor_get(v___y_2541_, 13);
v_hasTrace_2579_ = lean_ctor_get_uint8(v_options_2577_, sizeof(void*)*1);
if (v_hasTrace_2579_ == 0)
{
goto v___jp_2580_;
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2583_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2584_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2578_, v_options_2577_, v___x_2583_);
if (v___x_2584_ == 0)
{
goto v___jp_2580_;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2585_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2529_);
v___x_2586_ = l_Nat_reprFast(v_val_2529_);
v___x_2587_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
v___x_2588_ = l_Lean_MessageData_ofFormat(v___x_2587_);
v___x_2589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2585_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_inc(v_a_2537_);
v___x_2592_ = l_Nat_reprFast(v_a_2537_);
v___x_2593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
v___x_2594_ = l_Lean_MessageData_ofFormat(v___x_2593_);
lean_inc_ref(v___x_2594_);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2591_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2595_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
lean_inc_ref(v_e_2532_);
v___x_2598_ = l_Lean_MessageData_ofExpr(v_e_2532_);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v___x_2594_);
v___x_2603_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2582_, v___x_2602_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
lean_inc(v_a_2537_);
v___x_2605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2528_, v_val_2529_, v_a_2537_, v___x_2573_, v_a_2604_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v___y_2550_ = v___x_2605_;
goto v___jp_2549_;
}
else
{
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
return v___x_2603_;
}
}
}
v___jp_2580_:
{
lean_object* v___x_2581_; 
lean_inc(v_a_2537_);
v___x_2581_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2528_, v_val_2529_, v_a_2537_, v___x_2573_, v___x_2573_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v___y_2550_ = v___x_2581_;
goto v___jp_2549_;
}
}
else
{
lean_object* v___x_2606_; 
v___x_2606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2528_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = lean_array_fget_borrowed(v_args_2531_, v_a_2537_);
v___x_2609_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2529_, v_a_2537_, v_next_2533_, v_a_2607_);
lean_dec(v_a_2607_);
if (lean_obj_tag(v___x_2609_) == 1)
{
lean_object* v_val_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2706_; 
v_val_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2706_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_val_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2706_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; uint8_t v_foApprox_2615_; uint8_t v_ctxApprox_2616_; uint8_t v_quasiPatternApprox_2617_; uint8_t v_constApprox_2618_; uint8_t v_isDefEqStuckEx_2619_; uint8_t v_unificationHints_2620_; uint8_t v_assignSyntheticOpaque_2621_; uint8_t v_offsetCnstrs_2622_; uint8_t v_transparency_2623_; uint8_t v_etaStruct_2624_; uint8_t v_univApprox_2625_; uint8_t v_iota_2626_; uint8_t v_beta_2627_; uint8_t v_proj_2628_; uint8_t v_zeta_2629_; uint8_t v_zetaDelta_2630_; uint8_t v_zetaUnused_2631_; uint8_t v_zetaHave_2632_; uint8_t v_canUnfoldPredicateConfig_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2705_; 
v___x_2614_ = l_Lean_Meta_Context_config(v___y_2539_);
v_foApprox_2615_ = lean_ctor_get_uint8(v___x_2614_, 0);
v_ctxApprox_2616_ = lean_ctor_get_uint8(v___x_2614_, 1);
v_quasiPatternApprox_2617_ = lean_ctor_get_uint8(v___x_2614_, 2);
v_constApprox_2618_ = lean_ctor_get_uint8(v___x_2614_, 3);
v_isDefEqStuckEx_2619_ = lean_ctor_get_uint8(v___x_2614_, 4);
v_unificationHints_2620_ = lean_ctor_get_uint8(v___x_2614_, 5);
v_assignSyntheticOpaque_2621_ = lean_ctor_get_uint8(v___x_2614_, 7);
v_offsetCnstrs_2622_ = lean_ctor_get_uint8(v___x_2614_, 8);
v_transparency_2623_ = lean_ctor_get_uint8(v___x_2614_, 9);
v_etaStruct_2624_ = lean_ctor_get_uint8(v___x_2614_, 10);
v_univApprox_2625_ = lean_ctor_get_uint8(v___x_2614_, 11);
v_iota_2626_ = lean_ctor_get_uint8(v___x_2614_, 12);
v_beta_2627_ = lean_ctor_get_uint8(v___x_2614_, 13);
v_proj_2628_ = lean_ctor_get_uint8(v___x_2614_, 14);
v_zeta_2629_ = lean_ctor_get_uint8(v___x_2614_, 15);
v_zetaDelta_2630_ = lean_ctor_get_uint8(v___x_2614_, 16);
v_zetaUnused_2631_ = lean_ctor_get_uint8(v___x_2614_, 17);
v_zetaHave_2632_ = lean_ctor_get_uint8(v___x_2614_, 18);
v_canUnfoldPredicateConfig_2633_ = lean_ctor_get_uint8(v___x_2614_, 19);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2635_ = v___x_2614_;
v_isShared_2636_ = v_isSharedCheck_2705_;
goto v_resetjp_2634_;
}
else
{
lean_dec(v___x_2614_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2705_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
uint8_t v_trackZetaDelta_2637_; lean_object* v_zetaDeltaSet_2638_; lean_object* v_lctx_2639_; lean_object* v_localInstances_2640_; lean_object* v_defEqCtx_x3f_2641_; lean_object* v_synthPendingDepth_2642_; lean_object* v_customCanUnfoldPredicate_x3f_2643_; uint8_t v_univApprox_2644_; uint8_t v_inTypeClassResolution_2645_; uint8_t v_cacheInferType_2646_; uint8_t v___x_2647_; lean_object* v___x_2649_; 
v_trackZetaDelta_2637_ = lean_ctor_get_uint8(v___y_2539_, sizeof(void*)*7);
v_zetaDeltaSet_2638_ = lean_ctor_get(v___y_2539_, 1);
v_lctx_2639_ = lean_ctor_get(v___y_2539_, 2);
v_localInstances_2640_ = lean_ctor_get(v___y_2539_, 3);
v_defEqCtx_x3f_2641_ = lean_ctor_get(v___y_2539_, 4);
v_synthPendingDepth_2642_ = lean_ctor_get(v___y_2539_, 5);
v_customCanUnfoldPredicate_x3f_2643_ = lean_ctor_get(v___y_2539_, 6);
v_univApprox_2644_ = lean_ctor_get_uint8(v___y_2539_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2645_ = lean_ctor_get_uint8(v___y_2539_, sizeof(void*)*7 + 2);
v_cacheInferType_2646_ = lean_ctor_get_uint8(v___y_2539_, sizeof(void*)*7 + 3);
v___x_2647_ = 0;
if (v_isShared_2636_ == 0)
{
v___x_2649_ = v___x_2635_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 0, v_foApprox_2615_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 1, v_ctxApprox_2616_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 2, v_quasiPatternApprox_2617_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 3, v_constApprox_2618_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 4, v_isDefEqStuckEx_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 5, v_unificationHints_2620_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 7, v_assignSyntheticOpaque_2621_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 8, v_offsetCnstrs_2622_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 9, v_transparency_2623_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 10, v_etaStruct_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 11, v_univApprox_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 12, v_iota_2626_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 13, v_beta_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 14, v_proj_2628_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 15, v_zeta_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 16, v_zetaDelta_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 17, v_zetaUnused_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 18, v_zetaHave_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 19, v_canUnfoldPredicateConfig_2633_);
v___x_2649_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
uint64_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_ctor_set_uint8(v___x_2649_, 6, v___x_2647_);
v___x_2650_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2649_);
v___x_2651_ = l_Lean_instInhabitedExpr;
v___x_2652_ = lean_array_get_borrowed(v___x_2651_, v_params_2534_, v_val_2610_);
lean_dec(v_val_2610_);
v___x_2653_ = 2;
v___x_2654_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2654_, 0, v___x_2649_);
lean_ctor_set_uint64(v___x_2654_, sizeof(void*)*1, v___x_2650_);
v___x_2655_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2653_, v___x_2654_);
lean_inc(v_customCanUnfoldPredicate_x3f_2643_);
lean_inc(v_synthPendingDepth_2642_);
lean_inc(v_defEqCtx_x3f_2641_);
lean_inc_ref(v_localInstances_2640_);
lean_inc_ref(v_lctx_2639_);
lean_inc(v_zetaDeltaSet_2638_);
v___x_2656_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v_zetaDeltaSet_2638_);
lean_ctor_set(v___x_2656_, 2, v_lctx_2639_);
lean_ctor_set(v___x_2656_, 3, v_localInstances_2640_);
lean_ctor_set(v___x_2656_, 4, v_defEqCtx_x3f_2641_);
lean_ctor_set(v___x_2656_, 5, v_synthPendingDepth_2642_);
lean_ctor_set(v___x_2656_, 6, v_customCanUnfoldPredicate_x3f_2643_);
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*7, v_trackZetaDelta_2637_);
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*7 + 1, v_univApprox_2644_);
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2645_);
lean_ctor_set_uint8(v___x_2656_, sizeof(void*)*7 + 3, v_cacheInferType_2646_);
lean_inc(v___x_2608_);
lean_inc(v___x_2652_);
v___x_2657_ = l_Lean_Meta_isExprDefEq(v___x_2652_, v___x_2608_, v___x_2656_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec_ref_known(v___x_2656_, 7);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; uint8_t v___x_2659_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = lean_unbox(v_a_2658_);
lean_dec(v_a_2658_);
if (v___x_2659_ == 0)
{
lean_object* v_options_2660_; lean_object* v_inheritedTraceOptions_2661_; uint8_t v_hasTrace_2662_; 
v_options_2660_ = lean_ctor_get(v___y_2541_, 2);
v_inheritedTraceOptions_2661_ = lean_ctor_get(v___y_2541_, 13);
v_hasTrace_2662_ = lean_ctor_get_uint8(v_options_2660_, sizeof(void*)*1);
if (v_hasTrace_2662_ == 0)
{
lean_del_object(v___x_2612_);
goto v___jp_2663_;
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2666_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2661_, v_options_2660_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_del_object(v___x_2612_);
goto v___jp_2663_;
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2668_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2529_);
v___x_2669_ = l_Nat_reprFast(v_val_2529_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set_tag(v___x_2612_, 3);
lean_ctor_set(v___x_2612_, 0, v___x_2669_);
v___x_2671_ = v___x_2612_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2672_ = l_Lean_MessageData_ofFormat(v___x_2671_);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2668_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
lean_inc(v_a_2537_);
v___x_2676_ = l_Nat_reprFast(v_a_2537_);
v___x_2677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
v___x_2678_ = l_Lean_MessageData_ofFormat(v___x_2677_);
v___x_2679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2675_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
v___x_2680_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2679_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
lean_inc_ref(v_e_2532_);
v___x_2682_ = l_Lean_MessageData_ofExpr(v_e_2532_);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
lean_inc(v___x_2652_);
v___x_2686_ = l_Lean_MessageData_ofExpr(v___x_2652_);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
lean_inc(v___x_2608_);
v___x_2690_ = l_Lean_MessageData_ofExpr(v___x_2608_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2689_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2665_, v___x_2691_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
lean_inc(v_a_2537_);
v___x_2694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2528_, v_val_2529_, v_a_2537_, v___x_2573_, v_a_2693_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v___y_2550_ = v___x_2694_;
goto v___jp_2549_;
}
else
{
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
return v___x_2692_;
}
}
}
}
v___jp_2663_:
{
lean_object* v___x_2664_; 
lean_inc(v_a_2537_);
v___x_2664_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2528_, v_val_2529_, v_a_2537_, v___x_2573_, v___x_2573_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v___y_2550_ = v___x_2664_;
goto v___jp_2549_;
}
}
else
{
lean_del_object(v___x_2612_);
v_a_2545_ = v___x_2573_;
goto v___jp_2544_;
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_del_object(v___x_2612_);
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
v_a_2696_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2657_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2657_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v___x_2609_);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = 0;
lean_inc(v_a_2537_);
lean_inc(v___x_2608_);
v___x_2709_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v___x_2535_, v_val_2528_, v_next_2533_, v_params_2534_, v___x_2608_, v_val_2529_, v_a_2537_, v___x_2536_, v___x_2707_, v___x_2708_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; uint8_t v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2711_ = lean_unbox(v_a_2710_);
lean_dec(v_a_2710_);
if (v___x_2711_ == 0)
{
lean_object* v_options_2712_; lean_object* v_inheritedTraceOptions_2713_; uint8_t v_hasTrace_2714_; 
v_options_2712_ = lean_ctor_get(v___y_2541_, 2);
v_inheritedTraceOptions_2713_ = lean_ctor_get(v___y_2541_, 13);
v_hasTrace_2714_ = lean_ctor_get_uint8(v_options_2712_, sizeof(void*)*1);
if (v_hasTrace_2714_ == 0)
{
goto v___jp_2715_;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2717_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2718_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2713_, v_options_2712_, v___x_2718_);
if (v___x_2719_ == 0)
{
goto v___jp_2715_;
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2720_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2529_);
v___x_2721_ = l_Nat_reprFast(v_val_2529_);
v___x_2722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
v___x_2723_ = l_Lean_MessageData_ofFormat(v___x_2722_);
v___x_2724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2720_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
lean_inc(v_a_2537_);
v___x_2727_ = l_Nat_reprFast(v_a_2537_);
v___x_2728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
v___x_2729_ = l_Lean_MessageData_ofFormat(v___x_2728_);
v___x_2730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2726_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
lean_inc_ref(v_e_2532_);
v___x_2733_ = l_Lean_MessageData_ofExpr(v_e_2532_);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
lean_inc(v___x_2608_);
v___x_2737_ = l_Lean_MessageData_ofExpr(v___x_2608_);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2717_, v___x_2740_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2743_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2741_, 1);
lean_inc(v_a_2537_);
v___x_2743_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2528_, v_val_2529_, v_a_2537_, v___x_2573_, v_a_2742_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v___y_2550_ = v___x_2743_;
goto v___jp_2549_;
}
else
{
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
return v___x_2741_;
}
}
}
v___jp_2715_:
{
lean_object* v___x_2716_; 
lean_inc(v_a_2537_);
v___x_2716_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2528_, v_val_2529_, v_a_2537_, v___x_2573_, v___x_2573_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v___y_2550_ = v___x_2716_;
goto v___jp_2549_;
}
}
else
{
v_a_2545_ = v___x_2573_;
goto v___jp_2544_;
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
v_a_2744_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2709_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2709_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
v_a_2752_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2606_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2606_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
v_a_2760_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2571_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2571_);
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
v___jp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = lean_nat_add(v_a_2537_, v___x_2546_);
lean_dec(v_a_2537_);
v_a_2537_ = v___x_2547_;
v_b_2538_ = v_a_2545_;
goto _start;
}
v___jp_2549_:
{
if (lean_obj_tag(v___y_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2560_; 
v_a_2551_ = lean_ctor_get(v___y_2550_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___y_2550_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2553_ = v___y_2550_;
v_isShared_2554_ = v_isSharedCheck_2560_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___y_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2560_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
if (lean_obj_tag(v_a_2551_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
v_a_2555_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v_a_2551_, 1);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v_a_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
else
{
lean_object* v_a_2559_; 
lean_del_object(v___x_2553_);
v_a_2559_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v_a_2551_, 1);
v_a_2545_ = v_a_2559_;
goto v___jp_2544_;
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2532_);
lean_dec(v_val_2529_);
v_a_2561_ = lean_ctor_get(v___y_2550_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___y_2550_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___y_2550_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___y_2550_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2768_, lean_object* v_val_2769_, lean_object* v_upperBound_2770_, lean_object* v_args_2771_, lean_object* v_e_2772_, lean_object* v_next_2773_, lean_object* v_params_2774_, lean_object* v___x_2775_, lean_object* v___x_2776_, lean_object* v_a_2777_, lean_object* v_b_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v___x_42821__boxed_2784_; lean_object* v_res_2785_; 
v___x_42821__boxed_2784_ = lean_unbox(v___x_2776_);
v_res_2785_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2768_, v_val_2769_, v_upperBound_2770_, v_args_2771_, v_e_2772_, v_next_2773_, v_params_2774_, v___x_2775_, v___x_42821__boxed_2784_, v_a_2777_, v_b_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___x_2775_);
lean_dec_ref(v_params_2774_);
lean_dec(v_next_2773_);
lean_dec_ref(v_args_2771_);
lean_dec(v_upperBound_2770_);
lean_dec(v_val_2768_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2788_, lean_object* v___x_2789_, lean_object* v_val_2790_, lean_object* v_e_2791_, lean_object* v_next_2792_, lean_object* v_params_2793_, lean_object* v___x_2794_, lean_object* v_x_2795_, lean_object* v_x_2796_, lean_object* v_x_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
if (lean_obj_tag(v_x_2795_) == 5)
{
lean_object* v_fn_2803_; lean_object* v_arg_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_fn_2803_ = lean_ctor_get(v_x_2795_, 0);
lean_inc_ref(v_fn_2803_);
v_arg_2804_ = lean_ctor_get(v_x_2795_, 1);
lean_inc_ref(v_arg_2804_);
lean_dec_ref_known(v_x_2795_, 2);
v___x_2805_ = lean_array_set(v_x_2796_, v_x_2797_, v_arg_2804_);
v___x_2806_ = lean_unsigned_to_nat(1u);
v___x_2807_ = lean_nat_sub(v_x_2797_, v___x_2806_);
lean_dec(v_x_2797_);
v_x_2795_ = v_fn_2803_;
v_x_2796_ = v___x_2805_;
v_x_2797_ = v___x_2807_;
goto _start;
}
else
{
uint8_t v___x_2809_; 
lean_dec(v_x_2797_);
v___x_2809_ = l_Lean_Expr_isConst(v_x_2795_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
lean_dec_ref(v_x_2796_);
lean_dec_ref(v_x_2795_);
lean_dec_ref(v_e_2791_);
v___x_2810_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2812_ = l_Lean_Expr_constName_x21(v_x_2795_);
lean_dec_ref(v_x_2795_);
v___x_2813_ = lean_unsigned_to_nat(0u);
v___x_2814_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2812_, v_preDefs_2788_, v___x_2813_);
lean_dec(v___x_2812_);
if (lean_obj_tag(v___x_2814_) == 1)
{
lean_object* v_val_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_val_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_val_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_array_get_borrowed(v___x_2813_, v___x_2789_, v_val_2815_);
v___x_2818_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2790_, v_val_2815_, v___x_2817_, v_x_2796_, v_e_2791_, v_next_2792_, v_params_2793_, v___x_2794_, v___x_2809_, v___x_2813_, v___x_2816_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec_ref(v_x_2796_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2826_; 
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2818_, 0);
lean_dec(v_unused_2827_);
v___x_2820_ = v___x_2818_;
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
else
{
lean_dec(v___x_2818_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
v_a_2828_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2818_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2818_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v___x_2814_);
lean_dec_ref(v_x_2796_);
lean_dec_ref(v_e_2791_);
v___x_2836_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
return v___x_2837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2838_, lean_object* v___x_2839_, lean_object* v_val_2840_, lean_object* v_e_2841_, lean_object* v_next_2842_, lean_object* v_params_2843_, lean_object* v___x_2844_, lean_object* v_x_2845_, lean_object* v_x_2846_, lean_object* v_x_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2838_, v___x_2839_, v_val_2840_, v_e_2841_, v_next_2842_, v_params_2843_, v___x_2844_, v_x_2845_, v_x_2846_, v_x_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___x_2844_);
lean_dec_ref(v_params_2843_);
lean_dec(v_next_2842_);
lean_dec(v_val_2840_);
lean_dec_ref(v___x_2839_);
lean_dec_ref(v_preDefs_2838_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2854_, lean_object* v___x_2855_, lean_object* v_val_2856_, lean_object* v_a_2857_, lean_object* v_params_2858_, lean_object* v___x_2859_, lean_object* v_e_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_dummy_2866_; lean_object* v_nargs_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v_dummy_2866_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2867_ = l_Lean_Expr_getAppNumArgs(v_e_2860_);
lean_inc(v_nargs_2867_);
v___x_2868_ = lean_mk_array(v_nargs_2867_, v_dummy_2866_);
v___x_2869_ = lean_unsigned_to_nat(1u);
v___x_2870_ = lean_nat_sub(v_nargs_2867_, v___x_2869_);
lean_dec(v_nargs_2867_);
lean_inc_ref(v_e_2860_);
v___x_2871_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2854_, v___x_2855_, v_val_2856_, v_e_2860_, v_a_2857_, v_params_2858_, v___x_2859_, v_e_2860_, v___x_2868_, v___x_2870_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2872_, lean_object* v___x_2873_, lean_object* v_val_2874_, lean_object* v_a_2875_, lean_object* v_params_2876_, lean_object* v___x_2877_, lean_object* v_e_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2872_, v___x_2873_, v_val_2874_, v_a_2875_, v_params_2876_, v___x_2877_, v_e_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___x_2877_);
lean_dec_ref(v_params_2876_);
lean_dec(v_a_2875_);
lean_dec(v_val_2874_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v_preDefs_2872_);
return v_res_2884_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2888_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2889_ = lean_unsigned_to_nat(6u);
v___x_2890_ = lean_unsigned_to_nat(201u);
v___x_2891_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2892_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2893_ = l_mkPanicMessageWithDecl(v___x_2892_, v___x_2891_, v___x_2890_, v___x_2889_, v___x_2888_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2894_, lean_object* v___x_2895_, lean_object* v_a_2896_, lean_object* v_preDefs_2897_, lean_object* v_val_2898_, lean_object* v___f_2899_, lean_object* v___x_2900_, lean_object* v_params_2901_, lean_object* v_body_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2908_ = lean_array_get_size(v_params_2901_);
v___x_2909_ = lean_array_get_borrowed(v___x_2894_, v___x_2895_, v_a_2896_);
v___x_2910_ = lean_nat_dec_eq(v___x_2908_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
lean_dec_ref(v_body_2902_);
lean_dec_ref(v_params_2901_);
lean_dec_ref(v___f_2899_);
lean_dec(v_val_2898_);
lean_dec_ref(v_preDefs_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v___x_2895_);
v___x_2911_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2912_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2911_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
return v___x_2912_;
}
else
{
lean_object* v___f_2913_; uint8_t v___x_2914_; lean_object* v___x_2915_; 
v___f_2913_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 12, 6);
lean_closure_set(v___f_2913_, 0, v_preDefs_2897_);
lean_closure_set(v___f_2913_, 1, v___x_2895_);
lean_closure_set(v___f_2913_, 2, v_val_2898_);
lean_closure_set(v___f_2913_, 3, v_a_2896_);
lean_closure_set(v___f_2913_, 4, v_params_2901_);
lean_closure_set(v___f_2913_, 5, v___x_2908_);
v___x_2914_ = 0;
v___x_2915_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2902_, v___f_2913_, v___f_2899_, v___x_2914_, v___x_2910_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v___x_2915_, 0);
lean_dec(v_unused_2923_);
v___x_2917_ = v___x_2915_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_dec(v___x_2915_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2900_);
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2900_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
v_a_2924_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2915_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2915_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2932_, lean_object* v___x_2933_, lean_object* v_a_2934_, lean_object* v_preDefs_2935_, lean_object* v_val_2936_, lean_object* v___f_2937_, lean_object* v___x_2938_, lean_object* v_params_2939_, lean_object* v_body_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2932_, v___x_2933_, v_a_2934_, v_preDefs_2935_, v_val_2936_, v___f_2937_, v___x_2938_, v_params_2939_, v_body_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___x_2932_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_e_2947_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v_preDefs_2963_, lean_object* v___x_2964_, lean_object* v_val_2965_, lean_object* v_upperBound_2966_, lean_object* v_a_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
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
v___f_2978_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_2979_ = lean_unsigned_to_nat(0u);
v___x_2980_ = lean_box(0);
lean_inc(v_val_2965_);
lean_inc_ref(v_preDefs_2963_);
lean_inc(v_a_2967_);
lean_inc_ref(v___x_2964_);
v___f_2981_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
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
lean_dec_ref_known(v___x_2983_, 1);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v_preDefs_2987_, lean_object* v___x_2988_, lean_object* v_val_2989_, lean_object* v_upperBound_2990_, lean_object* v_a_2991_, lean_object* v_b_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_2987_, v___x_2988_, v_val_2989_, v_upperBound_2990_, v_a_2991_, v_b_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v_upperBound_2990_);
return v_res_2998_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3001_ = l_Lean_stringToMessageData(v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
size_t v_sz_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v_sz_3008_ = lean_array_size(v_preDefs_3002_);
v___x_3009_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3002_);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3008_, v___x_3009_, v_preDefs_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; size_t v_sz_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc_n(v_a_3011_, 2);
lean_dec_ref_known(v___x_3010_, 1);
v_sz_3012_ = lean_array_size(v_a_3011_);
v___x_3013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3012_, v___x_3009_, v_a_3011_);
v___x_3014_ = l_Lean_Elab_FixedParams_Info_init(v_a_3011_);
v___x_3015_ = lean_st_mk_ref(v___x_3014_);
v___x_3016_ = lean_st_ref_take(v___x_3015_);
v___x_3017_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3016_);
v___x_3018_ = lean_st_ref_set(v___x_3015_, v___x_3017_);
v___x_3019_ = lean_array_get_size(v_preDefs_3002_);
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = lean_box(0);
lean_inc(v___x_3015_);
v___x_3022_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3002_, v___x_3013_, v___x_3015_, v___x_3019_, v___x_3020_, v___x_3021_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3061_; 
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; 
v_unused_3062_ = lean_ctor_get(v___x_3022_, 0);
lean_dec(v_unused_3062_);
v___x_3024_ = v___x_3022_;
v_isShared_3025_ = v_isSharedCheck_3061_;
goto v_resetjp_3023_;
}
else
{
lean_dec(v___x_3022_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3061_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v_options_3027_; uint8_t v_hasTrace_3028_; 
v___x_3026_ = lean_st_ref_get(v___x_3015_);
lean_dec(v___x_3015_);
v_options_3027_ = lean_ctor_get(v_a_3005_, 2);
v_hasTrace_3028_ = lean_ctor_get_uint8(v_options_3027_, sizeof(void*)*1);
if (v_hasTrace_3028_ == 0)
{
lean_object* v___x_3030_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3026_);
v___x_3030_ = v___x_3024_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3026_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v_inheritedTraceOptions_3032_ = lean_ctor_get(v_a_3005_, 13);
v___x_3033_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3034_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3032_, v_options_3027_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3037_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3026_);
v___x_3037_ = v___x_3024_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3026_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_del_object(v___x_3024_);
v___x_3039_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3026_);
v___x_3040_ = l_Lean_Elab_FixedParams_Info_format(v___x_3026_);
v___x_3041_ = l_Std_Format_indentD(v___x_3040_);
v___x_3042_ = l_Lean_MessageData_ofFormat(v___x_3041_);
v___x_3043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3039_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3033_, v___x_3043_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v___x_3044_, 0);
lean_dec(v_unused_3052_);
v___x_3046_ = v___x_3044_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_dec(v___x_3044_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3026_);
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3026_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v___x_3026_);
v_a_3053_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3044_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3044_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v___x_3015_);
v_a_3063_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3022_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3022_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec_ref(v_preDefs_3002_);
v_a_3071_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3010_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3010_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_upperBound_3086_, lean_object* v_val_3087_, lean_object* v_next_3088_, lean_object* v_params_3089_, lean_object* v___x_3090_, lean_object* v_val_3091_, lean_object* v_next_3092_, uint8_t v___x_3093_, lean_object* v_inst_3094_, lean_object* v_R_3095_, lean_object* v_a_3096_, uint8_t v_b_3097_, lean_object* v_c_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_upperBound_3086_, v_val_3087_, v_next_3088_, v_params_3089_, v___x_3090_, v_val_3091_, v_next_3092_, v___x_3093_, v_a_3096_, v_b_3097_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_3105_ = _args[0];
lean_object* v_val_3106_ = _args[1];
lean_object* v_next_3107_ = _args[2];
lean_object* v_params_3108_ = _args[3];
lean_object* v___x_3109_ = _args[4];
lean_object* v_val_3110_ = _args[5];
lean_object* v_next_3111_ = _args[6];
lean_object* v___x_3112_ = _args[7];
lean_object* v_inst_3113_ = _args[8];
lean_object* v_R_3114_ = _args[9];
lean_object* v_a_3115_ = _args[10];
lean_object* v_b_3116_ = _args[11];
lean_object* v_c_3117_ = _args[12];
lean_object* v___y_3118_ = _args[13];
lean_object* v___y_3119_ = _args[14];
lean_object* v___y_3120_ = _args[15];
lean_object* v___y_3121_ = _args[16];
lean_object* v___y_3122_ = _args[17];
_start:
{
uint8_t v___x_43744__boxed_3123_; uint8_t v_b_boxed_3124_; lean_object* v_res_3125_; 
v___x_43744__boxed_3123_ = lean_unbox(v___x_3112_);
v_b_boxed_3124_ = lean_unbox(v_b_3116_);
v_res_3125_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_upperBound_3105_, v_val_3106_, v_next_3107_, v_params_3108_, v___x_3109_, v_val_3110_, v_next_3111_, v___x_43744__boxed_3123_, v_inst_3113_, v_R_3114_, v_a_3115_, v_b_boxed_3124_, v_c_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v_val_3110_);
lean_dec_ref(v_params_3108_);
lean_dec(v_next_3107_);
lean_dec(v_val_3106_);
lean_dec(v_upperBound_3105_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3126_, lean_object* v_val_3127_, lean_object* v_upperBound_3128_, lean_object* v_args_3129_, lean_object* v_e_3130_, lean_object* v_next_3131_, lean_object* v_params_3132_, lean_object* v___x_3133_, uint8_t v___x_3134_, lean_object* v_inst_3135_, lean_object* v_R_3136_, lean_object* v_a_3137_, lean_object* v_b_3138_, lean_object* v_c_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3126_, v_val_3127_, v_upperBound_3128_, v_args_3129_, v_e_3130_, v_next_3131_, v_params_3132_, v___x_3133_, v___x_3134_, v_a_3137_, v_b_3138_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3146_ = _args[0];
lean_object* v_val_3147_ = _args[1];
lean_object* v_upperBound_3148_ = _args[2];
lean_object* v_args_3149_ = _args[3];
lean_object* v_e_3150_ = _args[4];
lean_object* v_next_3151_ = _args[5];
lean_object* v_params_3152_ = _args[6];
lean_object* v___x_3153_ = _args[7];
lean_object* v___x_3154_ = _args[8];
lean_object* v_inst_3155_ = _args[9];
lean_object* v_R_3156_ = _args[10];
lean_object* v_a_3157_ = _args[11];
lean_object* v_b_3158_ = _args[12];
lean_object* v_c_3159_ = _args[13];
lean_object* v___y_3160_ = _args[14];
lean_object* v___y_3161_ = _args[15];
lean_object* v___y_3162_ = _args[16];
lean_object* v___y_3163_ = _args[17];
lean_object* v___y_3164_ = _args[18];
_start:
{
uint8_t v___x_43779__boxed_3165_; lean_object* v_res_3166_; 
v___x_43779__boxed_3165_ = lean_unbox(v___x_3154_);
v_res_3166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3146_, v_val_3147_, v_upperBound_3148_, v_args_3149_, v_e_3150_, v_next_3151_, v_params_3152_, v___x_3153_, v___x_43779__boxed_3165_, v_inst_3155_, v_R_3156_, v_a_3157_, v_b_3158_, v_c_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___x_3153_);
lean_dec_ref(v_params_3152_);
lean_dec(v_next_3151_);
lean_dec_ref(v_args_3149_);
lean_dec(v_upperBound_3148_);
lean_dec(v_val_3146_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v_preDefs_3167_, lean_object* v___x_3168_, lean_object* v_val_3169_, lean_object* v_upperBound_3170_, lean_object* v_inst_3171_, lean_object* v_R_3172_, lean_object* v_a_3173_, lean_object* v_b_3174_, lean_object* v_c_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v_preDefs_3167_, v___x_3168_, v_val_3169_, v_upperBound_3170_, v_a_3173_, v_b_3174_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v_preDefs_3182_, lean_object* v___x_3183_, lean_object* v_val_3184_, lean_object* v_upperBound_3185_, lean_object* v_inst_3186_, lean_object* v_R_3187_, lean_object* v_a_3188_, lean_object* v_b_3189_, lean_object* v_c_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v_preDefs_3182_, v___x_3183_, v_val_3184_, v_upperBound_3185_, v_inst_3186_, v_R_3187_, v_a_3188_, v_b_3189_, v_c_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v_upperBound_3185_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3197_, lean_object* v___x_3198_, lean_object* v_pre_3199_, lean_object* v_post_3200_, uint8_t v_usedLetOnly_3201_, uint8_t v_skipConstInApp_3202_, uint8_t v_skipInstances_3203_, lean_object* v___x_3204_, lean_object* v_inst_3205_, lean_object* v_R_3206_, lean_object* v_a_3207_, lean_object* v_b_3208_, lean_object* v_c_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3197_, v___x_3198_, v_pre_3199_, v_post_3200_, v_usedLetOnly_3201_, v_skipConstInApp_3202_, v_skipInstances_3203_, v_a_3207_, v_b_3208_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3217_ = _args[0];
lean_object* v___x_3218_ = _args[1];
lean_object* v_pre_3219_ = _args[2];
lean_object* v_post_3220_ = _args[3];
lean_object* v_usedLetOnly_3221_ = _args[4];
lean_object* v_skipConstInApp_3222_ = _args[5];
lean_object* v_skipInstances_3223_ = _args[6];
lean_object* v___x_3224_ = _args[7];
lean_object* v_inst_3225_ = _args[8];
lean_object* v_R_3226_ = _args[9];
lean_object* v_a_3227_ = _args[10];
lean_object* v_b_3228_ = _args[11];
lean_object* v_c_3229_ = _args[12];
lean_object* v___y_3230_ = _args[13];
lean_object* v___y_3231_ = _args[14];
lean_object* v___y_3232_ = _args[15];
lean_object* v___y_3233_ = _args[16];
lean_object* v___y_3234_ = _args[17];
lean_object* v___y_3235_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3236_; uint8_t v_skipConstInApp_boxed_3237_; uint8_t v_skipInstances_boxed_3238_; lean_object* v_res_3239_; 
v_usedLetOnly_boxed_3236_ = lean_unbox(v_usedLetOnly_3221_);
v_skipConstInApp_boxed_3237_ = lean_unbox(v_skipConstInApp_3222_);
v_skipInstances_boxed_3238_ = lean_unbox(v_skipInstances_3223_);
v_res_3239_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3217_, v___x_3218_, v_pre_3219_, v_post_3220_, v_usedLetOnly_boxed_3236_, v_skipConstInApp_boxed_3237_, v_skipInstances_boxed_3238_, v___x_3224_, v_inst_3225_, v_R_3226_, v_a_3227_, v_b_3228_, v_c_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___x_3224_);
lean_dec_ref(v___x_3218_);
lean_dec(v_upperBound_3217_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3240_, lean_object* v_m_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3241_, v_a_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3244_, lean_object* v_m_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3244_, v_m_3245_, v_a_3246_);
lean_dec_ref(v_a_3246_);
lean_dec_ref(v_m_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3248_, lean_object* v_name_3249_, uint8_t v_bi_3250_, lean_object* v_type_3251_, lean_object* v_k_3252_, uint8_t v_kind_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3249_, v_bi_3250_, v_type_3251_, v_k_3252_, v_kind_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3261_, lean_object* v_name_3262_, lean_object* v_bi_3263_, lean_object* v_type_3264_, lean_object* v_k_3265_, lean_object* v_kind_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v_bi_boxed_3273_; uint8_t v_kind_boxed_3274_; lean_object* v_res_3275_; 
v_bi_boxed_3273_ = lean_unbox(v_bi_3263_);
v_kind_boxed_3274_ = lean_unbox(v_kind_3266_);
v_res_3275_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3261_, v_name_3262_, v_bi_boxed_3273_, v_type_3264_, v_k_3265_, v_kind_boxed_3274_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3276_, lean_object* v_name_3277_, lean_object* v_type_3278_, lean_object* v_val_3279_, lean_object* v_k_3280_, uint8_t v_nondep_3281_, uint8_t v_kind_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3277_, v_type_3278_, v_val_3279_, v_k_3280_, v_nondep_3281_, v_kind_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3290_, lean_object* v_name_3291_, lean_object* v_type_3292_, lean_object* v_val_3293_, lean_object* v_k_3294_, lean_object* v_nondep_3295_, lean_object* v_kind_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
uint8_t v_nondep_boxed_3303_; uint8_t v_kind_boxed_3304_; lean_object* v_res_3305_; 
v_nondep_boxed_3303_ = lean_unbox(v_nondep_3295_);
v_kind_boxed_3304_ = lean_unbox(v_kind_3296_);
v_res_3305_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3290_, v_name_3291_, v_type_3292_, v_val_3293_, v_k_3294_, v_nondep_boxed_3303_, v_kind_boxed_3304_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3306_, lean_object* v_ref_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3307_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3314_, lean_object* v_ref_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3314_, v_ref_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3322_, lean_object* v_x_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3331_, lean_object* v_x_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3331_, v_x_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3340_, lean_object* v_m_3341_, lean_object* v_a_3342_, lean_object* v_b_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3341_, v_a_3342_, v_b_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3345_, lean_object* v_a_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3346_, v_x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3349_, lean_object* v_a_3350_, lean_object* v_x_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3349_, v_a_3350_, v_x_3351_);
lean_dec(v_x_3351_);
lean_dec_ref(v_a_3350_);
return v_res_3352_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3353_, lean_object* v_a_3354_, lean_object* v_x_3355_){
_start:
{
uint8_t v___x_3356_; 
v___x_3356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3354_, v_x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3357_, lean_object* v_a_3358_, lean_object* v_x_3359_){
_start:
{
uint8_t v_res_3360_; lean_object* v_r_3361_; 
v_res_3360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3357_, v_a_3358_, v_x_3359_);
lean_dec(v_x_3359_);
lean_dec_ref(v_a_3358_);
v_r_3361_ = lean_box(v_res_3360_);
return v_r_3361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3362_, lean_object* v_data_3363_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3363_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3365_, lean_object* v_a_3366_, lean_object* v_b_3367_, lean_object* v_x_3368_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3366_, v_b_3367_, v_x_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3370_, lean_object* v_i_3371_, lean_object* v_source_3372_, lean_object* v_target_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3371_, v_source_3372_, v_target_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3375_, lean_object* v_x_3376_, lean_object* v_x_3377_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3376_, v_x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3392_, lean_object* v_x_3393_){
_start:
{
if (lean_obj_tag(v_x_3392_) == 0)
{
lean_object* v___x_3394_; 
v___x_3394_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3394_;
}
else
{
lean_object* v_val_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3406_; 
v_val_3395_ = lean_ctor_get(v_x_3392_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_x_3392_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3397_ = v_x_3392_;
v_isShared_3398_ = v_isSharedCheck_3406_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_val_3395_);
lean_dec(v_x_3392_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3406_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3399_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3400_ = l_Nat_reprFast(v_val_3395_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 3);
lean_ctor_set(v___x_3397_, 0, v___x_3400_);
v___x_3402_ = v___x_3397_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3399_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = l_Repr_addAppParen(v___x_3403_, v_x_3393_);
return v___x_3404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3407_, lean_object* v_x_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3407_, v_x_3408_);
lean_dec(v_x_3408_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3410_, lean_object* v_x_3411_, lean_object* v_x_3412_){
_start:
{
if (lean_obj_tag(v_x_3412_) == 0)
{
lean_dec(v_x_3410_);
return v_x_3411_;
}
else
{
lean_object* v_head_3413_; lean_object* v_tail_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3425_; 
v_head_3413_ = lean_ctor_get(v_x_3412_, 0);
v_tail_3414_ = lean_ctor_get(v_x_3412_, 1);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_x_3412_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3416_ = v_x_3412_;
v_isShared_3417_ = v_isSharedCheck_3425_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_tail_3414_);
lean_inc(v_head_3413_);
lean_dec(v_x_3412_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3425_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
lean_inc(v_x_3410_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 5);
lean_ctor_set(v___x_3416_, 1, v_x_3410_);
lean_ctor_set(v___x_3416_, 0, v_x_3411_);
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_x_3411_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_x_3410_);
v___x_3419_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = lean_unsigned_to_nat(0u);
v___x_3421_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3413_, v___x_3420_);
v___x_3422_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3419_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v_x_3411_ = v___x_3422_;
v_x_3412_ = v_tail_3414_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3426_, lean_object* v_x_3427_, lean_object* v_x_3428_){
_start:
{
if (lean_obj_tag(v_x_3428_) == 0)
{
lean_dec(v_x_3426_);
return v_x_3427_;
}
else
{
lean_object* v_head_3429_; lean_object* v_tail_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3441_; 
v_head_3429_ = lean_ctor_get(v_x_3428_, 0);
v_tail_3430_ = lean_ctor_get(v_x_3428_, 1);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_x_3428_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3432_ = v_x_3428_;
v_isShared_3433_ = v_isSharedCheck_3441_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_tail_3430_);
lean_inc(v_head_3429_);
lean_dec(v_x_3428_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3441_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
lean_inc(v_x_3426_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 5);
lean_ctor_set(v___x_3432_, 1, v_x_3426_);
lean_ctor_set(v___x_3432_, 0, v_x_3427_);
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_x_3427_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_x_3426_);
v___x_3435_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3436_ = lean_unsigned_to_nat(0u);
v___x_3437_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3429_, v___x_3436_);
v___x_3438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3435_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3426_, v___x_3438_, v_tail_3430_);
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_unsigned_to_nat(0u);
v___x_3444_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3442_, v___x_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3445_, lean_object* v_x_3446_){
_start:
{
if (lean_obj_tag(v_x_3445_) == 0)
{
lean_object* v___x_3447_; 
lean_dec(v_x_3446_);
v___x_3447_ = lean_box(0);
return v___x_3447_;
}
else
{
lean_object* v_tail_3448_; 
v_tail_3448_ = lean_ctor_get(v_x_3445_, 1);
if (lean_obj_tag(v_tail_3448_) == 0)
{
lean_object* v_head_3449_; lean_object* v___x_3450_; 
lean_dec(v_x_3446_);
v_head_3449_ = lean_ctor_get(v_x_3445_, 0);
lean_inc(v_head_3449_);
lean_dec_ref_known(v_x_3445_, 2);
v___x_3450_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3449_);
return v___x_3450_;
}
else
{
lean_object* v_head_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
lean_inc(v_tail_3448_);
v_head_3451_ = lean_ctor_get(v_x_3445_, 0);
lean_inc(v_head_3451_);
lean_dec_ref_known(v_x_3445_, 2);
v___x_3452_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3451_);
v___x_3453_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3446_, v___x_3452_, v_tail_3448_);
return v___x_3453_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3462_ = lean_string_length(v___x_3461_);
return v___x_3462_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3464_ = lean_nat_to_int(v___x_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3471_ = lean_array_get_size(v_xs_3470_);
v___x_3472_ = lean_unsigned_to_nat(0u);
v___x_3473_ = lean_nat_dec_eq(v___x_3471_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3474_ = lean_array_to_list(v_xs_3470_);
v___x_3475_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3476_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3474_, v___x_3475_);
v___x_3477_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3478_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3479_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v___x_3476_);
v___x_3480_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3479_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3477_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = l_Std_Format_fill(v___x_3482_);
return v___x_3483_;
}
else
{
lean_object* v___x_3484_; 
lean_dec_ref(v_xs_3470_);
v___x_3484_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3485_, lean_object* v_x_3486_, lean_object* v_x_3487_){
_start:
{
if (lean_obj_tag(v_x_3487_) == 0)
{
lean_dec(v_x_3485_);
return v_x_3486_;
}
else
{
lean_object* v_head_3488_; lean_object* v_tail_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3499_; 
v_head_3488_ = lean_ctor_get(v_x_3487_, 0);
v_tail_3489_ = lean_ctor_get(v_x_3487_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_x_3487_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3491_ = v_x_3487_;
v_isShared_3492_ = v_isSharedCheck_3499_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_tail_3489_);
lean_inc(v_head_3488_);
lean_dec(v_x_3487_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3499_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
lean_inc(v_x_3485_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set_tag(v___x_3491_, 5);
lean_ctor_set(v___x_3491_, 1, v_x_3485_);
lean_ctor_set(v___x_3491_, 0, v_x_3486_);
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_x_3486_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_x_3485_);
v___x_3494_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3488_);
v___x_3496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3494_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v_x_3486_ = v___x_3496_;
v_x_3487_ = v_tail_3489_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3500_, lean_object* v_x_3501_){
_start:
{
if (lean_obj_tag(v_x_3500_) == 0)
{
lean_object* v___x_3502_; 
lean_dec(v_x_3501_);
v___x_3502_ = lean_box(0);
return v___x_3502_;
}
else
{
lean_object* v_tail_3503_; 
v_tail_3503_ = lean_ctor_get(v_x_3500_, 1);
if (lean_obj_tag(v_tail_3503_) == 0)
{
lean_object* v_head_3504_; lean_object* v___x_3505_; 
lean_dec(v_x_3501_);
v_head_3504_ = lean_ctor_get(v_x_3500_, 0);
lean_inc(v_head_3504_);
lean_dec_ref_known(v_x_3500_, 2);
v___x_3505_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3504_);
return v___x_3505_;
}
else
{
lean_object* v_head_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_inc(v_tail_3503_);
v_head_3506_ = lean_ctor_get(v_x_3500_, 0);
lean_inc(v_head_3506_);
lean_dec_ref_known(v_x_3500_, 2);
v___x_3507_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3506_);
v___x_3508_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3501_, v___x_3507_, v_tail_3503_);
return v___x_3508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3509_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3510_ = lean_array_get_size(v_xs_3509_);
v___x_3511_ = lean_unsigned_to_nat(0u);
v___x_3512_ = lean_nat_dec_eq(v___x_3510_, v___x_3511_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3513_ = lean_array_to_list(v_xs_3509_);
v___x_3514_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3515_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3513_, v___x_3514_);
v___x_3516_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3517_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
lean_ctor_set(v___x_3518_, 1, v___x_3515_);
v___x_3519_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3516_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = l_Std_Format_fill(v___x_3521_);
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; 
lean_dec_ref(v_xs_3509_);
v___x_3523_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3523_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3524_, lean_object* v_x_3525_, lean_object* v_x_3526_){
_start:
{
if (lean_obj_tag(v_x_3526_) == 0)
{
lean_dec(v_x_3524_);
return v_x_3525_;
}
else
{
lean_object* v_head_3527_; lean_object* v_tail_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3539_; 
v_head_3527_ = lean_ctor_get(v_x_3526_, 0);
v_tail_3528_ = lean_ctor_get(v_x_3526_, 1);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_x_3526_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3530_ = v_x_3526_;
v_isShared_3531_ = v_isSharedCheck_3539_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_tail_3528_);
lean_inc(v_head_3527_);
lean_dec(v_x_3526_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3539_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
lean_inc(v_x_3524_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set_tag(v___x_3530_, 5);
lean_ctor_set(v___x_3530_, 1, v_x_3524_);
lean_ctor_set(v___x_3530_, 0, v_x_3525_);
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_x_3525_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_x_3524_);
v___x_3533_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = l_Nat_reprFast(v_head_3527_);
v___x_3535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
v___x_3536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3533_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v_x_3525_ = v___x_3536_;
v_x_3526_ = v_tail_3528_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3540_, lean_object* v_x_3541_, lean_object* v_x_3542_){
_start:
{
if (lean_obj_tag(v_x_3542_) == 0)
{
lean_dec(v_x_3540_);
return v_x_3541_;
}
else
{
lean_object* v_head_3543_; lean_object* v_tail_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3555_; 
v_head_3543_ = lean_ctor_get(v_x_3542_, 0);
v_tail_3544_ = lean_ctor_get(v_x_3542_, 1);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_x_3542_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3546_ = v_x_3542_;
v_isShared_3547_ = v_isSharedCheck_3555_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_tail_3544_);
lean_inc(v_head_3543_);
lean_dec(v_x_3542_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3555_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
lean_inc(v_x_3540_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set_tag(v___x_3546_, 5);
lean_ctor_set(v___x_3546_, 1, v_x_3540_);
lean_ctor_set(v___x_3546_, 0, v_x_3541_);
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_x_3541_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_x_3540_);
v___x_3549_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3550_ = l_Nat_reprFast(v_head_3543_);
v___x_3551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3549_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3540_, v___x_3552_, v_tail_3544_);
return v___x_3553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3556_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = l_Nat_reprFast(v___y_3556_);
v___x_3558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3559_, lean_object* v_x_3560_){
_start:
{
if (lean_obj_tag(v_x_3559_) == 0)
{
lean_object* v___x_3561_; 
lean_dec(v_x_3560_);
v___x_3561_ = lean_box(0);
return v___x_3561_;
}
else
{
lean_object* v_tail_3562_; 
v_tail_3562_ = lean_ctor_get(v_x_3559_, 1);
if (lean_obj_tag(v_tail_3562_) == 0)
{
lean_object* v_head_3563_; lean_object* v___x_3564_; 
lean_dec(v_x_3560_);
v_head_3563_ = lean_ctor_get(v_x_3559_, 0);
lean_inc(v_head_3563_);
lean_dec_ref_known(v_x_3559_, 2);
v___x_3564_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3563_);
return v___x_3564_;
}
else
{
lean_object* v_head_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
lean_inc(v_tail_3562_);
v_head_3565_ = lean_ctor_get(v_x_3559_, 0);
lean_inc(v_head_3565_);
lean_dec_ref_known(v_x_3559_, 2);
v___x_3566_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3565_);
v___x_3567_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3560_, v___x_3566_, v_tail_3562_);
return v___x_3567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3568_){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3569_ = lean_array_get_size(v_xs_3568_);
v___x_3570_ = lean_unsigned_to_nat(0u);
v___x_3571_ = lean_nat_dec_eq(v___x_3569_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3572_ = lean_array_to_list(v_xs_3568_);
v___x_3573_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3574_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3572_, v___x_3573_);
v___x_3575_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3576_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
lean_ctor_set(v___x_3577_, 1, v___x_3574_);
v___x_3578_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3577_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3575_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = l_Std_Format_fill(v___x_3580_);
return v___x_3581_;
}
else
{
lean_object* v___x_3582_; 
lean_dec_ref(v_xs_3568_);
v___x_3582_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_){
_start:
{
if (lean_obj_tag(v_x_3585_) == 0)
{
lean_dec(v_x_3583_);
return v_x_3584_;
}
else
{
lean_object* v_head_3586_; lean_object* v_tail_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3597_; 
v_head_3586_ = lean_ctor_get(v_x_3585_, 0);
v_tail_3587_ = lean_ctor_get(v_x_3585_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_x_3585_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3589_ = v_x_3585_;
v_isShared_3590_ = v_isSharedCheck_3597_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_tail_3587_);
lean_inc(v_head_3586_);
lean_dec(v_x_3585_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3597_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
lean_inc(v_x_3583_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set_tag(v___x_3589_, 5);
lean_ctor_set(v___x_3589_, 1, v_x_3583_);
lean_ctor_set(v___x_3589_, 0, v_x_3584_);
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_x_3584_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_x_3583_);
v___x_3592_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3586_);
v___x_3594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3592_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v_x_3584_ = v___x_3594_;
v_x_3585_ = v_tail_3587_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3598_, lean_object* v_x_3599_){
_start:
{
if (lean_obj_tag(v_x_3598_) == 0)
{
lean_object* v___x_3600_; 
lean_dec(v_x_3599_);
v___x_3600_ = lean_box(0);
return v___x_3600_;
}
else
{
lean_object* v_tail_3601_; 
v_tail_3601_ = lean_ctor_get(v_x_3598_, 1);
if (lean_obj_tag(v_tail_3601_) == 0)
{
lean_object* v_head_3602_; lean_object* v___x_3603_; 
lean_dec(v_x_3599_);
v_head_3602_ = lean_ctor_get(v_x_3598_, 0);
lean_inc(v_head_3602_);
lean_dec_ref_known(v_x_3598_, 2);
v___x_3603_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3602_);
return v___x_3603_;
}
else
{
lean_object* v_head_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_inc(v_tail_3601_);
v_head_3604_ = lean_ctor_get(v_x_3598_, 0);
lean_inc(v_head_3604_);
lean_dec_ref_known(v_x_3598_, 2);
v___x_3605_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3604_);
v___x_3606_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3599_, v___x_3605_, v_tail_3601_);
return v___x_3606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3607_){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3608_ = lean_array_get_size(v_xs_3607_);
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3610_ = lean_nat_dec_eq(v___x_3608_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3611_ = lean_array_to_list(v_xs_3607_);
v___x_3612_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3613_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3611_, v___x_3612_);
v___x_3614_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3615_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v___x_3613_);
v___x_3617_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3616_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3614_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Std_Format_fill(v___x_3619_);
return v___x_3620_;
}
else
{
lean_object* v___x_3621_; 
lean_dec_ref(v_xs_3607_);
v___x_3621_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
if (lean_obj_tag(v_x_3624_) == 0)
{
lean_dec(v_x_3622_);
return v_x_3623_;
}
else
{
lean_object* v_head_3625_; lean_object* v_tail_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3636_; 
v_head_3625_ = lean_ctor_get(v_x_3624_, 0);
v_tail_3626_ = lean_ctor_get(v_x_3624_, 1);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_x_3624_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3628_ = v_x_3624_;
v_isShared_3629_ = v_isSharedCheck_3636_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_tail_3626_);
lean_inc(v_head_3625_);
lean_dec(v_x_3624_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3636_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
lean_inc(v_x_3622_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set_tag(v___x_3628_, 5);
lean_ctor_set(v___x_3628_, 1, v_x_3622_);
lean_ctor_set(v___x_3628_, 0, v_x_3623_);
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_x_3623_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_x_3622_);
v___x_3631_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3625_);
v___x_3633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3631_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v_x_3623_ = v___x_3633_;
v_x_3624_ = v_tail_3626_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3637_, lean_object* v_x_3638_){
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
lean_dec_ref_known(v_x_3637_, 2);
v___x_3642_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3641_);
return v___x_3642_;
}
else
{
lean_object* v_head_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_inc(v_tail_3640_);
v_head_3643_ = lean_ctor_get(v_x_3637_, 0);
lean_inc(v_head_3643_);
lean_dec_ref_known(v_x_3637_, 2);
v___x_3644_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3643_);
v___x_3645_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3638_, v___x_3644_, v_tail_3640_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3646_){
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
v___x_3652_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3650_, v___x_3651_);
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
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = lean_unsigned_to_nat(12u);
v___x_3675_ = lean_nat_to_int(v___x_3674_);
return v___x_3675_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_unsigned_to_nat(9u);
v___x_3680_ = lean_nat_to_int(v___x_3679_);
return v___x_3680_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_unsigned_to_nat(11u);
v___x_3685_ = lean_nat_to_int(v___x_3684_);
return v___x_3685_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3688_ = lean_string_length(v___x_3687_);
return v___x_3688_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3690_ = lean_nat_to_int(v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3695_){
_start:
{
lean_object* v_numFixed_3696_; lean_object* v_perms_3697_; lean_object* v_revDeps_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_numFixed_3696_ = lean_ctor_get(v_x_3695_, 0);
lean_inc(v_numFixed_3696_);
v_perms_3697_ = lean_ctor_get(v_x_3695_, 1);
lean_inc_ref(v_perms_3697_);
v_revDeps_3698_ = lean_ctor_get(v_x_3695_, 2);
lean_inc_ref(v_revDeps_3698_);
lean_dec_ref(v_x_3695_);
v___x_3699_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3700_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3701_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3702_ = l_Nat_reprFast(v_numFixed_3696_);
v___x_3703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
v___x_3704_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3701_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = 0;
v___x_3706_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3706_, 0, v___x_3704_);
lean_ctor_set_uint8(v___x_3706_, sizeof(void*)*1, v___x_3705_);
v___x_3707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3700_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = lean_box(1);
v___x_3711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
lean_ctor_set(v___x_3714_, 1, v___x_3699_);
v___x_3715_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3716_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3697_);
v___x_3717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
lean_ctor_set_uint8(v___x_3718_, sizeof(void*)*1, v___x_3705_);
v___x_3719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3714_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
lean_ctor_set(v___x_3720_, 1, v___x_3708_);
v___x_3721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
lean_ctor_set(v___x_3721_, 1, v___x_3710_);
v___x_3722_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
lean_ctor_set(v___x_3724_, 1, v___x_3699_);
v___x_3725_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3726_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3698_);
v___x_3727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
lean_ctor_set_uint8(v___x_3728_, sizeof(void*)*1, v___x_3705_);
v___x_3729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3724_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3731_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
lean_ctor_set(v___x_3732_, 1, v___x_3729_);
v___x_3733_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3730_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set_uint8(v___x_3736_, sizeof(void*)*1, v___x_3705_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3737_, lean_object* v_prec_3738_){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3740_, lean_object* v_prec_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3740_, v_prec_3741_);
lean_dec(v_prec_3741_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___f_3751_; lean_object* v___x_5797__overap_3752_; lean_object* v___x_3753_; 
v___f_3751_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5797__overap_3752_ = lean_panic_fn_borrowed(v___f_3751_, v_msg_3745_);
lean_inc(v___y_3749_);
lean_inc_ref(v___y_3748_);
lean_inc(v___y_3747_);
lean_inc_ref(v___y_3746_);
v___x_3753_ = lean_apply_5(v___x_5797__overap_3752_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, lean_box(0));
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___f_3767_; lean_object* v___x_5807__overap_3768_; lean_object* v___x_3769_; 
v___f_3767_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5807__overap_3768_ = lean_panic_fn_borrowed(v___f_3767_, v_msg_3761_);
lean_inc(v___y_3765_);
lean_inc_ref(v___y_3764_);
lean_inc(v___y_3763_);
lean_inc_ref(v___y_3762_);
v___x_3769_ = lean_apply_5(v___x_5807__overap_3768_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, lean_box(0));
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v___f_3783_; lean_object* v___x_5817__overap_3784_; lean_object* v___x_3785_; 
v___f_3783_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5817__overap_3784_ = lean_panic_fn_borrowed(v___f_3783_, v_msg_3777_);
lean_inc(v___y_3781_);
lean_inc_ref(v___y_3780_);
lean_inc(v___y_3779_);
lean_inc_ref(v___y_3778_);
v___x_3785_ = lean_apply_5(v___x_5817__overap_3784_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, lean_box(0));
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
return v_res_3792_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3796_ = lean_unsigned_to_nat(12u);
v___x_3797_ = lean_unsigned_to_nat(294u);
v___x_3798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3799_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3800_ = l_mkPanicMessageWithDecl(v___x_3799_, v___x_3798_, v___x_3797_, v___x_3796_, v___x_3795_);
return v___x_3800_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3803_ = lean_unsigned_to_nat(12u);
v___x_3804_ = lean_unsigned_to_nat(297u);
v___x_3805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3806_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3807_ = l_mkPanicMessageWithDecl(v___x_3806_, v___x_3805_, v___x_3804_, v___x_3803_, v___x_3802_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3808_, lean_object* v_as_3809_, size_t v_sz_3810_, size_t v_i_3811_, lean_object* v_b_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_a_3819_; uint8_t v___x_3823_; 
v___x_3823_ = lean_usize_dec_lt(v_i_3811_, v_sz_3810_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_b_3812_);
return v___x_3824_;
}
else
{
lean_object* v_a_3825_; 
v_a_3825_ = lean_array_uget_borrowed(v_as_3809_, v_i_3811_);
if (lean_obj_tag(v_a_3825_) == 1)
{
lean_object* v_val_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_val_3826_ = lean_ctor_get(v_a_3825_, 0);
v___x_3827_ = lean_unsigned_to_nat(0u);
v___x_3828_ = lean_box(0);
v___x_3829_ = lean_array_get_borrowed(v___x_3828_, v_val_3826_, v___x_3827_);
if (lean_obj_tag(v___x_3829_) == 1)
{
lean_object* v_val_3830_; lean_object* v___x_3831_; 
v_val_3830_ = lean_ctor_get(v___x_3829_, 0);
v___x_3831_ = lean_array_get_borrowed(v___x_3828_, v___x_3808_, v_val_3830_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_dec_ref(v_b_3812_);
v___x_3832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3833_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3832_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3843_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3843_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3843_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
if (lean_obj_tag(v_a_3834_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3840_; 
v_a_3838_ = lean_ctor_get(v_a_3834_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v_a_3834_, 1);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v_a_3838_);
v___x_3840_ = v___x_3836_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3838_);
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
lean_object* v_a_3842_; 
lean_del_object(v___x_3836_);
v_a_3842_ = lean_ctor_get(v_a_3834_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v_a_3834_, 1);
v_a_3819_ = v_a_3842_;
goto v___jp_3818_;
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
v_a_3844_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3833_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3833_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
else
{
lean_object* v___x_3852_; 
lean_inc_ref(v___x_3831_);
v___x_3852_ = lean_array_push(v_b_3812_, v___x_3831_);
v_a_3819_ = v___x_3852_;
goto v___jp_3818_;
}
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3854_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3853_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_dec_ref_known(v___x_3854_, 1);
v_a_3819_ = v_b_3812_;
goto v___jp_3818_;
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec_ref(v_b_3812_);
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
else
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = lean_box(0);
v___x_3864_ = lean_array_push(v_b_3812_, v___x_3863_);
v_a_3819_ = v___x_3864_;
goto v___jp_3818_;
}
}
v___jp_3818_:
{
size_t v___x_3820_; size_t v___x_3821_; 
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_add(v_i_3811_, v___x_3820_);
v_i_3811_ = v___x_3821_;
v_b_3812_ = v_a_3819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3865_, lean_object* v_as_3866_, lean_object* v_sz_3867_, lean_object* v_i_3868_, lean_object* v_b_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
size_t v_sz_boxed_3875_; size_t v_i_boxed_3876_; lean_object* v_res_3877_; 
v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3867_);
lean_dec(v_sz_3867_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3868_);
lean_dec(v_i_3868_);
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3865_, v_as_3866_, v_sz_boxed_3875_, v_i_boxed_3876_, v_b_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec_ref(v_as_3866_);
lean_dec_ref(v___x_3865_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3880_, lean_object* v___x_3881_, lean_object* v___x_3882_, lean_object* v_a_3883_, lean_object* v_b_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
uint8_t v___x_3890_; 
v___x_3890_ = lean_nat_dec_lt(v_a_3883_, v_upperBound_3880_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; 
lean_dec(v_a_3883_);
v___x_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3891_, 0, v_b_3884_);
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; lean_object* v___x_3893_; size_t v_sz_3894_; size_t v___x_3895_; lean_object* v___x_3896_; 
v___x_3892_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3893_ = lean_array_fget_borrowed(v___x_3881_, v_a_3883_);
v_sz_3894_ = lean_array_size(v___x_3893_);
v___x_3895_ = ((size_t)0ULL);
v___x_3896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3882_, v___x_3893_, v_sz_3894_, v___x_3895_, v___x_3892_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3898_ = lean_array_push(v_b_3884_, v_a_3897_);
v___x_3899_ = lean_unsigned_to_nat(1u);
v___x_3900_ = lean_nat_add(v_a_3883_, v___x_3899_);
lean_dec(v_a_3883_);
v_a_3883_ = v___x_3900_;
v_b_3884_ = v___x_3898_;
goto _start;
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_dec_ref(v_b_3884_);
lean_dec(v_a_3883_);
v_a_3902_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3896_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3896_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3910_, lean_object* v___x_3911_, lean_object* v___x_3912_, lean_object* v_a_3913_, lean_object* v_b_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3910_, v___x_3911_, v___x_3912_, v_a_3913_, v_b_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v___x_3912_);
lean_dec_ref(v___x_3911_);
lean_dec(v_upperBound_3910_);
return v_res_3920_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3922_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3923_ = lean_unsigned_to_nat(8u);
v___x_3924_ = lean_unsigned_to_nat(281u);
v___x_3925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3926_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3927_ = l_mkPanicMessageWithDecl(v___x_3926_, v___x_3925_, v___x_3924_, v___x_3923_, v___x_3922_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3928_, lean_object* v_a_3929_, lean_object* v_b_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v_a_3937_; uint8_t v___x_3941_; 
v___x_3941_ = lean_nat_dec_lt(v_a_3929_, v_upperBound_3928_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; 
lean_dec(v_a_3929_);
v___x_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3942_, 0, v_b_3930_);
return v___x_3942_;
}
else
{
lean_object* v_snd_3943_; lean_object* v_snd_3944_; lean_object* v_snd_3945_; lean_object* v_fst_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_4070_; 
v_snd_3943_ = lean_ctor_get(v_b_3930_, 1);
lean_inc(v_snd_3943_);
v_snd_3944_ = lean_ctor_get(v_snd_3943_, 1);
lean_inc(v_snd_3944_);
v_snd_3945_ = lean_ctor_get(v_snd_3944_, 1);
lean_inc(v_snd_3945_);
v_fst_3946_ = lean_ctor_get(v_b_3930_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_b_3930_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; 
v_unused_4071_ = lean_ctor_get(v_b_3930_, 1);
lean_dec(v_unused_4071_);
v___x_3948_ = v_b_3930_;
v_isShared_3949_ = v_isSharedCheck_4070_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_fst_3946_);
lean_dec(v_b_3930_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_4070_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v_fst_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_4068_; 
v_fst_3950_ = lean_ctor_get(v_snd_3943_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v_snd_3943_);
if (v_isSharedCheck_4068_ == 0)
{
lean_object* v_unused_4069_; 
v_unused_4069_ = lean_ctor_get(v_snd_3943_, 1);
lean_dec(v_unused_4069_);
v___x_3952_ = v_snd_3943_;
v_isShared_3953_ = v_isSharedCheck_4068_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_fst_3950_);
lean_dec(v_snd_3943_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_4068_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v_fst_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_4066_; 
v_fst_3954_ = lean_ctor_get(v_snd_3944_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_snd_3944_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; 
v_unused_4067_ = lean_ctor_get(v_snd_3944_, 1);
lean_dec(v_unused_4067_);
v___x_3956_ = v_snd_3944_;
v_isShared_3957_ = v_isSharedCheck_4066_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_fst_3954_);
lean_dec(v_snd_3944_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_4066_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v_array_3958_; lean_object* v_start_3959_; lean_object* v_stop_3960_; uint8_t v___x_3961_; 
v_array_3958_ = lean_ctor_get(v_snd_3945_, 0);
v_start_3959_ = lean_ctor_get(v_snd_3945_, 1);
v_stop_3960_ = lean_ctor_get(v_snd_3945_, 2);
v___x_3961_ = lean_nat_dec_lt(v_start_3959_, v_stop_3960_);
if (v___x_3961_ == 0)
{
lean_object* v___x_3963_; 
lean_dec(v_a_3929_);
if (v_isShared_3957_ == 0)
{
v___x_3963_ = v___x_3956_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_fst_3954_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_snd_3945_);
v___x_3963_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3965_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 1, v___x_3963_);
v___x_3965_ = v___x_3952_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_fst_3950_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
lean_object* v___x_3967_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_3965_);
v___x_3967_ = v___x_3948_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_fst_3946_);
lean_ctor_set(v_reuseFailAlloc_3969_, 1, v___x_3965_);
v___x_3967_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3968_; 
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
}
}
}
else
{
lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_4062_; 
lean_inc(v_stop_3960_);
lean_inc(v_start_3959_);
lean_inc_ref(v_array_3958_);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_snd_3945_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; lean_object* v_unused_4064_; lean_object* v_unused_4065_; 
v_unused_4063_ = lean_ctor_get(v_snd_3945_, 2);
lean_dec(v_unused_4063_);
v_unused_4064_ = lean_ctor_get(v_snd_3945_, 1);
lean_dec(v_unused_4064_);
v_unused_4065_ = lean_ctor_get(v_snd_3945_, 0);
lean_dec(v_unused_4065_);
v___x_3973_ = v_snd_3945_;
v_isShared_3974_ = v_isSharedCheck_4062_;
goto v_resetjp_3972_;
}
else
{
lean_dec(v_snd_3945_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_4062_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v_array_3975_; lean_object* v_start_3976_; lean_object* v_stop_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3982_; 
v_array_3975_ = lean_ctor_get(v_fst_3954_, 0);
v_start_3976_ = lean_ctor_get(v_fst_3954_, 1);
v_stop_3977_ = lean_ctor_get(v_fst_3954_, 2);
v___x_3978_ = lean_array_fget(v_array_3958_, v_start_3959_);
v___x_3979_ = lean_unsigned_to_nat(1u);
v___x_3980_ = lean_nat_add(v_start_3959_, v___x_3979_);
lean_dec(v_start_3959_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 1, v___x_3980_);
v___x_3982_ = v___x_3973_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_array_3958_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v___x_3980_);
lean_ctor_set(v_reuseFailAlloc_4061_, 2, v_stop_3960_);
v___x_3982_ = v_reuseFailAlloc_4061_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
uint8_t v___x_3983_; 
v___x_3983_ = lean_nat_dec_lt(v_start_3976_, v_stop_3977_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3985_; 
lean_dec(v___x_3978_);
lean_dec(v_a_3929_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v___x_3982_);
v___x_3985_ = v___x_3956_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_fst_3954_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v___x_3982_);
v___x_3985_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3987_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 1, v___x_3985_);
v___x_3987_ = v___x_3952_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_fst_3950_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3989_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_3987_);
v___x_3989_ = v___x_3948_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_fst_3946_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
}
}
}
else
{
lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4057_; 
lean_inc(v_stop_3977_);
lean_inc(v_start_3976_);
lean_inc_ref(v_array_3975_);
v_isSharedCheck_4057_ = !lean_is_exclusive(v_fst_3954_);
if (v_isSharedCheck_4057_ == 0)
{
lean_object* v_unused_4058_; lean_object* v_unused_4059_; lean_object* v_unused_4060_; 
v_unused_4058_ = lean_ctor_get(v_fst_3954_, 2);
lean_dec(v_unused_4058_);
v_unused_4059_ = lean_ctor_get(v_fst_3954_, 1);
lean_dec(v_unused_4059_);
v_unused_4060_ = lean_ctor_get(v_fst_3954_, 0);
lean_dec(v_unused_4060_);
v___x_3995_ = v_fst_3954_;
v_isShared_3996_ = v_isSharedCheck_4057_;
goto v_resetjp_3994_;
}
else
{
lean_dec(v_fst_3954_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4057_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3997_ = lean_nat_add(v_start_3976_, v___x_3979_);
lean_dec(v_start_3976_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 1, v___x_3997_);
v___x_3999_ = v___x_3995_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_array_3975_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4056_, 2, v_stop_3977_);
v___x_3999_ = v_reuseFailAlloc_4056_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
if (lean_obj_tag(v___x_3978_) == 1)
{
lean_object* v_val_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4044_; 
v_val_4000_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4002_ = v___x_3978_;
v_isShared_4003_ = v_isSharedCheck_4044_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_val_4000_);
lean_dec(v___x_3978_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4044_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4004_ = lean_unsigned_to_nat(0u);
v___x_4005_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4006_ = lean_box(0);
v___x_4007_ = lean_array_get(v___x_4006_, v_val_4000_, v___x_4004_);
lean_dec(v_val_4000_);
lean_inc(v_a_3929_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v_a_3929_);
v___x_4009_ = v___x_4002_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_3929_);
v___x_4009_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
uint8_t v___x_4010_; 
v___x_4010_ = l_Option_instDecidableEq___redArg(v___x_4005_, v___x_4007_, v___x_4009_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
lean_dec_ref(v___x_3999_);
lean_dec_ref(v___x_3982_);
lean_del_object(v___x_3956_);
lean_del_object(v___x_3952_);
lean_dec(v_fst_3950_);
lean_del_object(v___x_3948_);
lean_dec(v_fst_3946_);
v___x_4011_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4012_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4011_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4022_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
if (lean_obj_tag(v_a_4013_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4019_; 
lean_dec(v_a_3929_);
v_a_4017_ = lean_ctor_get(v_a_4013_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v_a_4013_, 1);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v_a_4017_);
v___x_4019_ = v___x_4015_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4017_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
else
{
lean_object* v_a_4021_; 
lean_del_object(v___x_4015_);
v_a_4021_ = lean_ctor_get(v_a_4013_, 0);
lean_inc(v_a_4021_);
lean_dec_ref_known(v_a_4013_, 1);
v_a_3937_ = v_a_4021_;
goto v___jp_3936_;
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec(v_a_3929_);
v_a_4023_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4012_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4012_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4035_; 
lean_inc(v_fst_3950_);
v___x_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4031_, 0, v_fst_3950_);
v___x_4032_ = lean_array_push(v_fst_3946_, v___x_4031_);
v___x_4033_ = lean_nat_add(v_fst_3950_, v___x_3979_);
lean_dec(v_fst_3950_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v___x_3982_);
lean_ctor_set(v___x_3956_, 0, v___x_3999_);
v___x_4035_ = v___x_3956_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v___x_3982_);
v___x_4035_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4037_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 1, v___x_4035_);
lean_ctor_set(v___x_3952_, 0, v___x_4033_);
v___x_4037_ = v___x_3952_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v___x_4035_);
v___x_4037_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4039_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_4037_);
lean_ctor_set(v___x_3948_, 0, v___x_4032_);
v___x_4039_ = v___x_3948_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
v_a_3937_ = v___x_4039_;
goto v___jp_3936_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
lean_dec(v___x_3978_);
v___x_4045_ = lean_box(0);
v___x_4046_ = lean_array_push(v_fst_3946_, v___x_4045_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v___x_3982_);
lean_ctor_set(v___x_3956_, 0, v___x_3999_);
v___x_4048_ = v___x_3956_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v___x_3982_);
v___x_4048_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4050_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 1, v___x_4048_);
v___x_4050_ = v___x_3952_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_fst_3950_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
lean_object* v___x_4052_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v___x_4050_);
lean_ctor_set(v___x_3948_, 0, v___x_4046_);
v___x_4052_ = v___x_3948_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4046_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
v_a_3937_ = v___x_4052_;
goto v___jp_3936_;
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
v___jp_3936_:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_unsigned_to_nat(1u);
v___x_3939_ = lean_nat_add(v_a_3929_, v___x_3938_);
lean_dec(v_a_3929_);
v_a_3929_ = v___x_3939_;
v_b_3930_ = v_a_3937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4072_, lean_object* v_a_4073_, lean_object* v_b_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4072_, v_a_4073_, v_b_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v_upperBound_4072_);
return v_res_4080_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4082_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4083_ = lean_unsigned_to_nat(4u);
v___x_4084_ = lean_unsigned_to_nat(275u);
v___x_4085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4086_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4087_ = l_mkPanicMessageWithDecl(v___x_4086_, v___x_4085_, v___x_4084_, v___x_4083_, v___x_4082_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4088_, lean_object* v___x_4089_, lean_object* v___x_4090_, lean_object* v_xs_4091_, lean_object* v_x_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_graph_4098_; lean_object* v_revDeps_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4152_; 
v_graph_4098_ = lean_ctor_get(v_a_4088_, 0);
v_revDeps_4099_ = lean_ctor_get(v_a_4088_, 1);
v_isSharedCheck_4152_ = !lean_is_exclusive(v_a_4088_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4101_ = v_a_4088_;
v_isShared_4102_ = v_isSharedCheck_4152_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_revDeps_4099_);
lean_inc(v_graph_4098_);
lean_dec(v_a_4088_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4152_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4103_ = lean_array_get_borrowed(v___x_4089_, v_graph_4098_, v___x_4090_);
v___x_4104_ = lean_array_get_size(v_xs_4091_);
v___x_4105_ = lean_array_get_size(v___x_4103_);
v___x_4106_ = lean_nat_dec_eq(v___x_4104_, v___x_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_del_object(v___x_4101_);
lean_dec_ref(v_revDeps_4099_);
lean_dec_ref(v_graph_4098_);
lean_dec_ref(v_xs_4091_);
lean_dec(v___x_4090_);
v___x_4107_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4108_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4107_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4108_;
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4113_; 
v___x_4109_ = lean_mk_empty_array_with_capacity(v___x_4090_);
lean_inc_n(v___x_4090_, 2);
v___x_4110_ = l_Array_toSubarray___redArg(v_xs_4091_, v___x_4090_, v___x_4104_);
lean_inc(v___x_4103_);
v___x_4111_ = l_Array_toSubarray___redArg(v___x_4103_, v___x_4090_, v___x_4105_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 1, v___x_4111_);
lean_ctor_set(v___x_4101_, 0, v___x_4110_);
v___x_4113_ = v___x_4101_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_4110_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
lean_inc(v___x_4090_);
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4090_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4109_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4104_, v___x_4090_, v___x_4115_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v_snd_4118_; lean_object* v_fst_4119_; lean_object* v_fst_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref_known(v___x_4116_, 1);
v_snd_4118_ = lean_ctor_get(v_a_4117_, 1);
lean_inc(v_snd_4118_);
v_fst_4119_ = lean_ctor_get(v_a_4117_, 0);
lean_inc_n(v_fst_4119_, 2);
lean_dec(v_a_4117_);
v_fst_4120_ = lean_ctor_get(v_snd_4118_, 0);
lean_inc(v_fst_4120_);
lean_dec(v_snd_4118_);
v___x_4121_ = lean_unsigned_to_nat(1u);
v___x_4122_ = lean_array_get_size(v_graph_4098_);
v___x_4123_ = lean_mk_empty_array_with_capacity(v___x_4121_);
v___x_4124_ = lean_array_push(v___x_4123_, v_fst_4119_);
v___x_4125_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4122_, v_graph_4098_, v_fst_4119_, v___x_4121_, v___x_4124_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec(v_fst_4119_);
lean_dec_ref(v_graph_4098_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4134_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4128_ = v___x_4125_;
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4134_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; lean_object* v___x_4132_; 
v___x_4130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4130_, 0, v_fst_4120_);
lean_ctor_set(v___x_4130_, 1, v_a_4126_);
lean_ctor_set(v___x_4130_, 2, v_revDeps_4099_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4130_);
v___x_4132_ = v___x_4128_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v_fst_4120_);
lean_dec_ref(v_revDeps_4099_);
v_a_4135_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4125_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4125_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec_ref(v_revDeps_4099_);
lean_dec_ref(v_graph_4098_);
v_a_4143_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4116_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4116_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4153_, lean_object* v___x_4154_, lean_object* v___x_4155_, lean_object* v_xs_4156_, lean_object* v_x_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4153_, v___x_4154_, v___x_4155_, v_xs_4156_, v_x_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v_x_4157_);
lean_dec_ref(v___x_4154_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v___x_4170_; 
lean_inc_ref(v_preDefs_4164_);
v___x_4170_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v_value_4175_; lean_object* v___x_4176_; lean_object* v___f_4177_; uint8_t v___x_4178_; lean_object* v___x_4179_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v___x_4172_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4173_ = lean_unsigned_to_nat(0u);
v___x_4174_ = lean_array_get(v___x_4172_, v_preDefs_4164_, v___x_4173_);
lean_dec_ref(v_preDefs_4164_);
v_value_4175_ = lean_ctor_get(v___x_4174_, 7);
lean_inc_ref(v_value_4175_);
lean_dec(v___x_4174_);
v___x_4176_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4177_, 0, v_a_4171_);
lean_closure_set(v___f_4177_, 1, v___x_4176_);
lean_closure_set(v___f_4177_, 2, v___x_4173_);
v___x_4178_ = 0;
v___x_4179_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4175_, v___f_4177_, v___x_4178_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
return v___x_4179_;
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec_ref(v_preDefs_4164_);
v_a_4180_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4170_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4170_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4195_, lean_object* v___x_4196_, lean_object* v___x_4197_, lean_object* v_inst_4198_, lean_object* v_R_4199_, lean_object* v_a_4200_, lean_object* v_b_4201_, lean_object* v_c_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4195_, v___x_4196_, v___x_4197_, v_a_4200_, v_b_4201_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4209_, lean_object* v___x_4210_, lean_object* v___x_4211_, lean_object* v_inst_4212_, lean_object* v_R_4213_, lean_object* v_a_4214_, lean_object* v_b_4215_, lean_object* v_c_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4209_, v___x_4210_, v___x_4211_, v_inst_4212_, v_R_4213_, v_a_4214_, v_b_4215_, v_c_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec_ref(v___x_4211_);
lean_dec_ref(v___x_4210_);
lean_dec(v_upperBound_4209_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4223_, lean_object* v_inst_4224_, lean_object* v_R_4225_, lean_object* v_a_4226_, lean_object* v_b_4227_, lean_object* v_c_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4223_, v_a_4226_, v_b_4227_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4235_, lean_object* v_inst_4236_, lean_object* v_R_4237_, lean_object* v_a_4238_, lean_object* v_b_4239_, lean_object* v_c_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4235_, v_inst_4236_, v_R_4237_, v_a_4238_, v_b_4239_, v_c_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v_upperBound_4235_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4247_, size_t v_i_4248_, size_t v_stop_4249_, lean_object* v_b_4250_){
_start:
{
uint8_t v___x_4251_; 
v___x_4251_ = lean_usize_dec_eq(v_i_4248_, v_stop_4249_);
if (v___x_4251_ == 0)
{
size_t v___x_4252_; size_t v___x_4253_; lean_object* v___x_4254_; 
v___x_4252_ = ((size_t)1ULL);
v___x_4253_ = lean_usize_sub(v_i_4248_, v___x_4252_);
v___x_4254_ = lean_array_uget_borrowed(v_as_4247_, v___x_4253_);
if (lean_obj_tag(v___x_4254_) == 0)
{
v_i_4248_ = v___x_4253_;
goto _start;
}
else
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = lean_unsigned_to_nat(1u);
v___x_4257_ = lean_nat_add(v_b_4250_, v___x_4256_);
lean_dec(v_b_4250_);
v_i_4248_ = v___x_4253_;
v_b_4250_ = v___x_4257_;
goto _start;
}
}
else
{
return v_b_4250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4259_, lean_object* v_i_4260_, lean_object* v_stop_4261_, lean_object* v_b_4262_){
_start:
{
size_t v_i_boxed_4263_; size_t v_stop_boxed_4264_; lean_object* v_res_4265_; 
v_i_boxed_4263_ = lean_unbox_usize(v_i_4260_);
lean_dec(v_i_4260_);
v_stop_boxed_4264_ = lean_unbox_usize(v_stop_4261_);
lean_dec(v_stop_4261_);
v_res_4265_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4259_, v_i_boxed_4263_, v_stop_boxed_4264_, v_b_4262_);
lean_dec_ref(v_as_4259_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4266_){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = lean_array_get_size(v_perm_4266_);
v___x_4269_ = lean_nat_dec_lt(v___x_4267_, v___x_4268_);
if (v___x_4269_ == 0)
{
return v___x_4267_;
}
else
{
size_t v___x_4270_; size_t v___x_4271_; lean_object* v___x_4272_; 
v___x_4270_ = lean_usize_of_nat(v___x_4268_);
v___x_4271_ = ((size_t)0ULL);
v___x_4272_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4266_, v___x_4270_, v___x_4271_, v___x_4267_);
return v___x_4272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4273_);
lean_dec_ref(v_perm_4273_);
return v_res_4274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4275_, lean_object* v_i_4276_){
_start:
{
lean_object* v___x_4277_; uint8_t v___x_4278_; 
v___x_4277_ = lean_array_get_size(v_perm_4275_);
v___x_4278_ = lean_nat_dec_lt(v_i_4276_, v___x_4277_);
if (v___x_4278_ == 0)
{
return v___x_4278_;
}
else
{
lean_object* v___x_4279_; 
v___x_4279_ = lean_array_fget_borrowed(v_perm_4275_, v_i_4276_);
if (lean_obj_tag(v___x_4279_) == 0)
{
uint8_t v___x_4280_; 
v___x_4280_ = 0;
return v___x_4280_;
}
else
{
return v___x_4278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4281_, lean_object* v_i_4282_){
_start:
{
uint8_t v_res_4283_; lean_object* v_r_4284_; 
v_res_4283_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4281_, v_i_4282_);
lean_dec(v_i_4282_);
lean_dec_ref(v_perm_4281_);
v_r_4284_ = lean_box(v_res_4283_);
return v_r_4284_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___f_4291_; lean_object* v___x_1072__overap_4292_; lean_object* v___x_4293_; 
v___f_4291_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_1072__overap_4292_ = lean_panic_fn_borrowed(v___f_4291_, v_msg_4285_);
lean_inc(v___y_4289_);
lean_inc_ref(v___y_4288_);
lean_inc(v___y_4287_);
lean_inc_ref(v___y_4286_);
v___x_4293_ = lean_apply_5(v___x_1072__overap_4292_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, lean_box(0));
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4301_, lean_object* v_msg_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4309_, lean_object* v_msg_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4309_, v_msg_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4317_, lean_object* v_maxFVars_x3f_4318_, lean_object* v_k_4319_, uint8_t v_cleanupAnnotations_4320_, uint8_t v_whnfType_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v___f_4327_; lean_object* v___x_4328_; 
v___f_4327_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4327_, 0, v_k_4319_);
v___x_4328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4317_, v_maxFVars_x3f_4318_, v___f_4327_, v_cleanupAnnotations_4320_, v_whnfType_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4328_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4328_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
v_a_4337_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4328_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4328_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4345_, lean_object* v_maxFVars_x3f_4346_, lean_object* v_k_4347_, lean_object* v_cleanupAnnotations_4348_, lean_object* v_whnfType_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4355_; uint8_t v_whnfType_boxed_4356_; lean_object* v_res_4357_; 
v_cleanupAnnotations_boxed_4355_ = lean_unbox(v_cleanupAnnotations_4348_);
v_whnfType_boxed_4356_ = lean_unbox(v_whnfType_4349_);
v_res_4357_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4345_, v_maxFVars_x3f_4346_, v_k_4347_, v_cleanupAnnotations_boxed_4355_, v_whnfType_boxed_4356_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4358_, lean_object* v_type_4359_, lean_object* v_maxFVars_x3f_4360_, lean_object* v_k_4361_, uint8_t v_cleanupAnnotations_4362_, uint8_t v_whnfType_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4359_, v_maxFVars_x3f_4360_, v_k_4361_, v_cleanupAnnotations_4362_, v_whnfType_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4370_, lean_object* v_type_4371_, lean_object* v_maxFVars_x3f_4372_, lean_object* v_k_4373_, lean_object* v_cleanupAnnotations_4374_, lean_object* v_whnfType_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4381_; uint8_t v_whnfType_boxed_4382_; lean_object* v_res_4383_; 
v_cleanupAnnotations_boxed_4381_ = lean_unbox(v_cleanupAnnotations_4374_);
v_whnfType_boxed_4382_ = lean_unbox(v_whnfType_4375_);
v_res_4383_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4370_, v_type_4371_, v_maxFVars_x3f_4372_, v_k_4373_, v_cleanupAnnotations_boxed_4381_, v_whnfType_boxed_4382_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4383_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4386_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4387_ = lean_unsigned_to_nat(6u);
v___x_4388_ = lean_unsigned_to_nat(329u);
v___x_4389_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4390_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4391_ = l_mkPanicMessageWithDecl(v___x_4390_, v___x_4389_, v___x_4388_, v___x_4387_, v___x_4386_);
return v___x_4391_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4395_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4396_ = lean_unsigned_to_nat(8u);
v___x_4397_ = lean_unsigned_to_nat(322u);
v___x_4398_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4399_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4400_ = l_mkPanicMessageWithDecl(v___x_4399_, v___x_4398_, v___x_4397_, v___x_4396_, v___x_4395_);
return v___x_4400_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4402_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4403_ = lean_unsigned_to_nat(8u);
v___x_4404_ = lean_unsigned_to_nat(325u);
v___x_4405_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4406_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4407_ = l_mkPanicMessageWithDecl(v___x_4406_, v___x_4405_, v___x_4404_, v___x_4403_, v___x_4402_);
return v___x_4407_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4409_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4410_ = lean_unsigned_to_nat(8u);
v___x_4411_ = lean_unsigned_to_nat(324u);
v___x_4412_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4413_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4414_ = l_mkPanicMessageWithDecl(v___x_4413_, v___x_4412_, v___x_4411_, v___x_4410_, v___x_4409_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4415_, lean_object* v_xs_4416_, lean_object* v_val_4417_, lean_object* v_i_4418_, lean_object* v_perm_4419_, lean_object* v_k_4420_, lean_object* v_xs_x27_4421_, lean_object* v_type_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___x_4428_; uint8_t v___x_4429_; 
v___x_4428_ = lean_array_get_size(v_xs_x27_4421_);
v___x_4429_ = lean_nat_dec_eq(v___x_4428_, v___x_4415_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
lean_dec_ref(v_type_4422_);
lean_dec_ref(v_k_4420_);
lean_dec_ref(v_perm_4419_);
lean_dec_ref(v_xs_4416_);
v___x_4430_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4431_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4430_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
return v___x_4431_;
}
else
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v_x_4434_; lean_object* v___x_4435_; 
v___x_4432_ = l_Lean_instInhabitedExpr;
v___x_4433_ = lean_unsigned_to_nat(0u);
v_x_4434_ = lean_array_get_borrowed(v___x_4432_, v_xs_x27_4421_, v___x_4433_);
lean_inc(v___y_4426_);
lean_inc_ref(v___y_4425_);
lean_inc(v___y_4424_);
lean_inc_ref(v___y_4423_);
lean_inc(v_x_4434_);
v___x_4435_ = lean_infer_type(v_x_4434_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; uint8_t v___x_4437_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
v___x_4437_ = l_Lean_Expr_hasLooseBVars(v_a_4436_);
lean_dec(v_a_4436_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4438_ = lean_array_get_size(v_xs_4416_);
v___x_4439_ = lean_nat_dec_lt(v_val_4417_, v___x_4438_);
if (v___x_4439_ == 0)
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_dec_ref(v_type_4422_);
lean_dec_ref(v_k_4420_);
lean_dec_ref(v_perm_4419_);
lean_dec_ref(v_xs_4416_);
v___x_4440_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4441_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4440_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
return v___x_4441_;
}
else
{
lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4442_ = lean_nat_add(v_i_4418_, v___x_4415_);
lean_inc(v_x_4434_);
v___x_4443_ = lean_array_set(v_xs_4416_, v_val_4417_, v_x_4434_);
v___x_4444_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4419_, v_k_4420_, v___x_4442_, v_type_4422_, v___x_4443_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
return v___x_4444_;
}
}
else
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
lean_dec_ref(v_type_4422_);
lean_dec_ref(v_k_4420_);
lean_dec_ref(v_perm_4419_);
lean_dec_ref(v_xs_4416_);
v___x_4445_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4446_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4445_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
return v___x_4446_;
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec_ref(v_type_4422_);
lean_dec_ref(v_k_4420_);
lean_dec_ref(v_perm_4419_);
lean_dec_ref(v_xs_4416_);
v_a_4447_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4435_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4435_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4455_, lean_object* v_xs_4456_, lean_object* v_val_4457_, lean_object* v_i_4458_, lean_object* v_perm_4459_, lean_object* v_k_4460_, lean_object* v_xs_x27_4461_, lean_object* v_type_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4455_, v_xs_4456_, v_val_4457_, v_i_4458_, v_perm_4459_, v_k_4460_, v_xs_x27_4461_, v_type_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec_ref(v_xs_x27_4461_);
lean_dec(v_i_4458_);
lean_dec(v_val_4457_);
lean_dec(v___x_4455_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4469_, lean_object* v_k_4470_, lean_object* v_i_4471_, lean_object* v_type_4472_, lean_object* v_xs_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_){
_start:
{
lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4479_ = lean_array_get_size(v_perm_4469_);
v___x_4480_ = lean_nat_dec_lt(v_i_4471_, v___x_4479_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; 
lean_dec_ref(v_type_4472_);
lean_dec(v_i_4471_);
lean_dec_ref(v_perm_4469_);
lean_inc(v_a_4477_);
lean_inc_ref(v_a_4476_);
lean_inc(v_a_4475_);
lean_inc_ref(v_a_4474_);
v___x_4481_ = lean_apply_6(v_k_4470_, v_xs_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, lean_box(0));
return v___x_4481_;
}
else
{
lean_object* v___x_4482_; 
v___x_4482_ = lean_array_fget_borrowed(v_perm_4469_, v_i_4471_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v___x_4483_; 
lean_inc(v_a_4477_);
lean_inc_ref(v_a_4476_);
lean_inc(v_a_4475_);
lean_inc_ref(v_a_4474_);
v___x_4483_ = lean_whnf(v_type_4472_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; uint8_t v___x_4485_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4485_ = l_Lean_Expr_isForall(v_a_4484_);
if (v___x_4485_ == 0)
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_dec(v_a_4484_);
lean_dec_ref(v_xs_4473_);
lean_dec(v_i_4471_);
lean_dec_ref(v_k_4470_);
lean_dec_ref(v_perm_4469_);
v___x_4486_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4487_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4486_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
return v___x_4487_;
}
else
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4488_ = lean_unsigned_to_nat(1u);
v___x_4489_ = lean_nat_add(v_i_4471_, v___x_4488_);
lean_dec(v_i_4471_);
v___x_4490_ = l_Lean_Expr_bindingBody_x21(v_a_4484_);
lean_dec(v_a_4484_);
v_i_4471_ = v___x_4489_;
v_type_4472_ = v___x_4490_;
goto _start;
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec_ref(v_xs_4473_);
lean_dec(v_i_4471_);
lean_dec_ref(v_k_4470_);
lean_dec_ref(v_perm_4469_);
v_a_4492_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4483_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4483_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
lean_object* v_val_4500_; lean_object* v___x_4501_; lean_object* v___f_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; lean_object* v___x_4505_; 
v_val_4500_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_val_4500_);
v___x_4501_ = lean_unsigned_to_nat(1u);
v___f_4502_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4502_, 0, v___x_4501_);
lean_closure_set(v___f_4502_, 1, v_xs_4473_);
lean_closure_set(v___f_4502_, 2, v_val_4500_);
lean_closure_set(v___f_4502_, 3, v_i_4471_);
lean_closure_set(v___f_4502_, 4, v_perm_4469_);
lean_closure_set(v___f_4502_, 5, v_k_4470_);
v___x_4503_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4504_ = 0;
v___x_4505_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4472_, v___x_4503_, v___f_4502_, v___x_4480_, v___x_4504_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
return v___x_4505_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4506_, lean_object* v_k_4507_, lean_object* v_i_4508_, lean_object* v_type_4509_, lean_object* v_xs_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4506_, v_k_4507_, v_i_4508_, v_type_4509_, v_xs_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4517_, lean_object* v_perm_4518_, lean_object* v_k_4519_, lean_object* v_i_4520_, lean_object* v_type_4521_, lean_object* v_xs_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4518_, v_k_4519_, v_i_4520_, v_type_4521_, v_xs_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4529_, lean_object* v_perm_4530_, lean_object* v_k_4531_, lean_object* v_i_4532_, lean_object* v_type_4533_, lean_object* v_xs_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4529_, v_perm_4530_, v_k_4531_, v_i_4532_, v_type_4533_, v_xs_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4540_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = lean_unsigned_to_nat(0u);
v___x_4542_ = l_Lean_Level_ofNat(v___x_4541_);
return v___x_4542_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4543_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4544_ = l_Lean_mkSort(v___x_4543_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4545_, lean_object* v_type_4546_, lean_object* v_k_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4553_ = lean_unsigned_to_nat(0u);
v___x_4554_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4545_);
v___x_4555_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4556_ = lean_mk_array(v___x_4554_, v___x_4555_);
v___x_4557_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4545_, v_k_4547_, v___x_4553_, v_type_4546_, v___x_4556_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4558_, lean_object* v_type_4559_, lean_object* v_k_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4558_, v_type_4559_, v_k_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4567_, lean_object* v_perm_4568_, lean_object* v_type_4569_, lean_object* v_k_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v___x_4576_; 
v___x_4576_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4568_, v_type_4569_, v_k_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4577_, lean_object* v_perm_4578_, lean_object* v_type_4579_, lean_object* v_k_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4577_, v_perm_4578_, v_type_4579_, v_k_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4587_, lean_object* v_runInBase_4588_, lean_object* v_b_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_apply_1(v_k_4587_, v_b_4589_);
lean_inc(v___y_4593_);
lean_inc_ref(v___y_4592_);
lean_inc(v___y_4591_);
lean_inc_ref(v___y_4590_);
v___x_4596_ = lean_apply_7(v_runInBase_4588_, lean_box(0), v___x_4595_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, lean_box(0));
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4597_, lean_object* v_runInBase_4598_, lean_object* v_b_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4597_, v_runInBase_4598_, v_b_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4606_, lean_object* v_perm_4607_, lean_object* v_type_4608_, lean_object* v_runInBase_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_){
_start:
{
lean_object* v___f_4615_; lean_object* v___x_4616_; 
v___f_4615_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4615_, 0, v_k_4606_);
lean_closure_set(v___f_4615_, 1, v_runInBase_4609_);
v___x_4616_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4607_, v_type_4608_, v___f_4615_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4617_, lean_object* v_perm_4618_, lean_object* v_type_4619_, lean_object* v_runInBase_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4617_, v_perm_4618_, v_type_4619_, v_runInBase_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4627_, lean_object* v_inst_4628_, lean_object* v_perm_4629_, lean_object* v_type_4630_, lean_object* v_k_4631_){
_start:
{
lean_object* v_toBind_4632_; lean_object* v_liftWith_4633_; lean_object* v_restoreM_4634_; lean_object* v___f_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v_toBind_4632_ = lean_ctor_get(v_inst_4628_, 1);
lean_inc(v_toBind_4632_);
lean_dec_ref(v_inst_4628_);
v_liftWith_4633_ = lean_ctor_get(v_inst_4627_, 0);
lean_inc(v_liftWith_4633_);
v_restoreM_4634_ = lean_ctor_get(v_inst_4627_, 1);
lean_inc(v_restoreM_4634_);
lean_dec_ref(v_inst_4627_);
v___f_4635_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4635_, 0, v_k_4631_);
lean_closure_set(v___f_4635_, 1, v_perm_4629_);
lean_closure_set(v___f_4635_, 2, v_type_4630_);
v___x_4636_ = lean_apply_2(v_liftWith_4633_, lean_box(0), v___f_4635_);
v___x_4637_ = lean_apply_1(v_restoreM_4634_, lean_box(0));
v___x_4638_ = lean_apply_4(v_toBind_4632_, lean_box(0), lean_box(0), v___x_4636_, v___x_4637_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4639_, lean_object* v_00_u03b1_4640_, lean_object* v_inst_4641_, lean_object* v_inst_4642_, lean_object* v_perm_4643_, lean_object* v_type_4644_, lean_object* v_k_4645_){
_start:
{
lean_object* v___x_4646_; 
v___x_4646_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4641_, v_inst_4642_, v_perm_4643_, v_type_4644_, v_k_4645_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v___f_4653_; lean_object* v___x_603__overap_4654_; lean_object* v___x_4655_; 
v___f_4653_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_603__overap_4654_ = lean_panic_fn_borrowed(v___f_4653_, v_msg_4647_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc(v___y_4649_);
lean_inc_ref(v___y_4648_);
v___x_4655_ = lean_apply_5(v___x_603__overap_4654_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, lean_box(0));
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
return v_res_4662_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4665_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4666_ = lean_unsigned_to_nat(10u);
v___x_4667_ = lean_unsigned_to_nat(353u);
v___x_4668_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4669_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4670_ = l_mkPanicMessageWithDecl(v___x_4669_, v___x_4668_, v___x_4667_, v___x_4666_, v___x_4665_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4671_, lean_object* v_xs_4672_, lean_object* v_tail_4673_, lean_object* v_ys_4674_, lean_object* v_type_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4671_, v_xs_4672_, v_tail_4673_, v_ys_4674_, v_type_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec_ref(v_ys_4674_);
lean_dec(v___x_4671_);
return v_res_4681_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4682_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4683_ = lean_unsigned_to_nat(8u);
v___x_4684_ = lean_unsigned_to_nat(349u);
v___x_4685_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4687_ = l_mkPanicMessageWithDecl(v___x_4686_, v___x_4685_, v___x_4684_, v___x_4683_, v___x_4682_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4688_, lean_object* v_x_4689_, lean_object* v_x_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_){
_start:
{
if (lean_obj_tag(v_x_4689_) == 0)
{
lean_object* v___x_4696_; 
lean_dec_ref(v_xs_4688_);
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v_x_4690_);
return v___x_4696_;
}
else
{
lean_object* v_head_4697_; 
v_head_4697_ = lean_ctor_get(v_x_4689_, 0);
if (lean_obj_tag(v_head_4697_) == 0)
{
lean_object* v_tail_4698_; lean_object* v___x_4699_; lean_object* v___f_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___x_4703_; 
v_tail_4698_ = lean_ctor_get(v_x_4689_, 1);
lean_inc(v_tail_4698_);
lean_dec_ref_known(v_x_4689_, 2);
v___x_4699_ = lean_unsigned_to_nat(1u);
v___f_4700_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4700_, 0, v___x_4699_);
lean_closure_set(v___f_4700_, 1, v_xs_4688_);
lean_closure_set(v___f_4700_, 2, v_tail_4698_);
v___x_4701_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4702_ = 0;
v___x_4703_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4690_, v___x_4701_, v___f_4700_, v___x_4702_, v___x_4702_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
return v___x_4703_;
}
else
{
lean_object* v_tail_4704_; lean_object* v_val_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; 
lean_inc_ref(v_head_4697_);
v_tail_4704_ = lean_ctor_get(v_x_4689_, 1);
lean_inc(v_tail_4704_);
lean_dec_ref_known(v_x_4689_, 2);
v_val_4705_ = lean_ctor_get(v_head_4697_, 0);
lean_inc(v_val_4705_);
lean_dec_ref_known(v_head_4697_, 1);
v___x_4706_ = lean_array_get_size(v_xs_4688_);
v___x_4707_ = lean_nat_dec_lt(v_val_4705_, v___x_4706_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
lean_dec(v_val_4705_);
lean_dec(v_tail_4704_);
lean_dec_ref(v_x_4690_);
lean_dec_ref(v_xs_4688_);
v___x_4708_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4709_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4708_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
return v___x_4709_;
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4710_ = l_Lean_instInhabitedExpr;
v___x_4711_ = lean_array_get_borrowed(v___x_4710_, v_xs_4688_, v_val_4705_);
lean_dec(v_val_4705_);
v___x_4712_ = lean_unsigned_to_nat(1u);
v___x_4713_ = lean_mk_empty_array_with_capacity(v___x_4712_);
lean_inc(v___x_4711_);
v___x_4714_ = lean_array_push(v___x_4713_, v___x_4711_);
v___x_4715_ = l_Lean_Meta_instantiateForall(v_x_4690_, v___x_4714_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
lean_dec_ref(v___x_4714_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref_known(v___x_4715_, 1);
v_x_4689_ = v_tail_4704_;
v_x_4690_ = v_a_4716_;
goto _start;
}
else
{
lean_dec(v_tail_4704_);
lean_dec_ref(v_xs_4688_);
return v___x_4715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4718_, lean_object* v_xs_4719_, lean_object* v_tail_4720_, lean_object* v_ys_4721_, lean_object* v_type_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4728_ = lean_array_get_size(v_ys_4721_);
v___x_4729_ = lean_nat_dec_eq(v___x_4728_, v___x_4718_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; lean_object* v___x_4731_; 
lean_dec_ref(v_type_4722_);
lean_dec(v_tail_4720_);
lean_dec_ref(v_xs_4719_);
v___x_4730_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4731_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4730_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
return v___x_4731_;
}
else
{
lean_object* v___x_4732_; 
v___x_4732_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4719_, v_tail_4720_, v_type_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_object* v_a_4733_; uint8_t v___x_4734_; uint8_t v___x_4735_; lean_object* v___x_4736_; 
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
lean_inc(v_a_4733_);
lean_dec_ref_known(v___x_4732_, 1);
v___x_4734_ = 0;
v___x_4735_ = 1;
v___x_4736_ = l_Lean_Meta_mkForallFVars(v_ys_4721_, v_a_4733_, v___x_4734_, v___x_4729_, v___x_4729_, v___x_4735_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
return v___x_4736_;
}
else
{
return v___x_4732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4737_, lean_object* v_x_4738_, lean_object* v_x_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4737_, v_x_4738_, v_x_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_);
lean_dec(v_a_4743_);
lean_dec_ref(v_a_4742_);
lean_dec(v_a_4741_);
lean_dec_ref(v_a_4740_);
return v_res_4745_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4748_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4749_ = lean_unsigned_to_nat(2u);
v___x_4750_ = lean_unsigned_to_nat(343u);
v___x_4751_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4752_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4753_ = l_mkPanicMessageWithDecl(v___x_4752_, v___x_4751_, v___x_4750_, v___x_4749_, v___x_4748_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4754_, lean_object* v_type_u2080_4755_, lean_object* v_xs_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___x_4762_ = lean_array_get_size(v_xs_4756_);
v___x_4763_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4754_);
v___x_4764_ = lean_nat_dec_eq(v___x_4762_, v___x_4763_);
lean_dec(v___x_4763_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
lean_dec_ref(v_xs_4756_);
lean_dec_ref(v_type_u2080_4755_);
lean_dec_ref(v_perm_4754_);
v___x_4765_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4766_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4765_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
return v___x_4766_;
}
else
{
lean_object* v_mask_4767_; lean_object* v___x_4768_; 
v_mask_4767_ = lean_array_to_list(v_perm_4754_);
v___x_4768_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4756_, v_mask_4767_, v_type_u2080_4755_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
return v___x_4768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4769_, lean_object* v_type_u2080_4770_, lean_object* v_xs_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4769_, v_type_u2080_4770_, v_xs_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4778_, lean_object* v_maxFVars_4779_, lean_object* v_k_4780_, uint8_t v_cleanupAnnotations_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
lean_object* v___f_4787_; uint8_t v___x_4788_; uint8_t v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___f_4787_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4787_, 0, v_k_4780_);
v___x_4788_ = 1;
v___x_4789_ = 0;
v___x_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4790_, 0, v_maxFVars_4779_);
v___x_4791_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4778_, v___x_4788_, v___x_4789_, v___x_4788_, v___x_4789_, v___x_4790_, v___f_4787_, v_cleanupAnnotations_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
lean_dec_ref_known(v___x_4790_, 1);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4791_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4791_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
v_a_4800_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4791_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4791_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4808_, lean_object* v_maxFVars_4809_, lean_object* v_k_4810_, lean_object* v_cleanupAnnotations_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4817_; lean_object* v_res_4818_; 
v_cleanupAnnotations_boxed_4817_ = lean_unbox(v_cleanupAnnotations_4811_);
v_res_4818_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4808_, v_maxFVars_4809_, v_k_4810_, v_cleanupAnnotations_boxed_4817_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
return v_res_4818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4819_, lean_object* v_e_4820_, lean_object* v_maxFVars_4821_, lean_object* v_k_4822_, uint8_t v_cleanupAnnotations_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4820_, v_maxFVars_4821_, v_k_4822_, v_cleanupAnnotations_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4830_, lean_object* v_e_4831_, lean_object* v_maxFVars_4832_, lean_object* v_k_4833_, lean_object* v_cleanupAnnotations_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4840_; lean_object* v_res_4841_; 
v_cleanupAnnotations_boxed_4840_ = lean_unbox(v_cleanupAnnotations_4834_);
v_res_4841_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4830_, v_e_4831_, v_maxFVars_4832_, v_k_4833_, v_cleanupAnnotations_boxed_4840_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
return v_res_4841_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4842_){
_start:
{
if (lean_obj_tag(v_x_4842_) == 0)
{
uint8_t v___x_4843_; 
v___x_4843_ = 1;
return v___x_4843_;
}
else
{
lean_object* v_head_4844_; 
v_head_4844_ = lean_ctor_get(v_x_4842_, 0);
if (lean_obj_tag(v_head_4844_) == 0)
{
lean_object* v_tail_4845_; 
v_tail_4845_ = lean_ctor_get(v_x_4842_, 1);
v_x_4842_ = v_tail_4845_;
goto _start;
}
else
{
uint8_t v___x_4847_; 
v___x_4847_ = 0;
return v___x_4847_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4848_){
_start:
{
uint8_t v_res_4849_; lean_object* v_r_4850_; 
v_res_4849_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4848_);
lean_dec(v_x_4848_);
v_r_4850_ = lean_box(v_res_4849_);
return v_r_4850_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4853_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4854_ = lean_unsigned_to_nat(12u);
v___x_4855_ = lean_unsigned_to_nat(376u);
v___x_4856_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4857_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4858_ = l_mkPanicMessageWithDecl(v___x_4857_, v___x_4856_, v___x_4855_, v___x_4854_, v___x_4853_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4859_, lean_object* v_xs_4860_, lean_object* v_tail_4861_, lean_object* v___x_4862_, lean_object* v___x_4863_, lean_object* v_ys_4864_, lean_object* v_value_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
uint8_t v___x_1310__boxed_4871_; uint8_t v___x_1311__boxed_4872_; lean_object* v_res_4873_; 
v___x_1310__boxed_4871_ = lean_unbox(v___x_4862_);
v___x_1311__boxed_4872_ = lean_unbox(v___x_4863_);
v_res_4873_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4859_, v_xs_4860_, v_tail_4861_, v___x_1310__boxed_4871_, v___x_1311__boxed_4872_, v_ys_4864_, v_value_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec_ref(v_ys_4864_);
lean_dec(v___x_4859_);
return v_res_4873_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4874_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4875_ = lean_unsigned_to_nat(8u);
v___x_4876_ = lean_unsigned_to_nat(368u);
v___x_4877_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4878_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4879_ = l_mkPanicMessageWithDecl(v___x_4878_, v___x_4877_, v___x_4876_, v___x_4875_, v___x_4874_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4880_, lean_object* v_x_4881_, lean_object* v_x_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_){
_start:
{
if (lean_obj_tag(v_x_4881_) == 0)
{
lean_object* v___x_4888_; 
lean_dec_ref(v_xs_4880_);
v___x_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4888_, 0, v_x_4882_);
return v___x_4888_;
}
else
{
lean_object* v_head_4889_; 
v_head_4889_ = lean_ctor_get(v_x_4881_, 0);
if (lean_obj_tag(v_head_4889_) == 0)
{
lean_object* v_tail_4890_; uint8_t v___x_4891_; 
v_tail_4890_ = lean_ctor_get(v_x_4881_, 1);
lean_inc(v_tail_4890_);
lean_dec_ref_known(v_x_4881_, 2);
v___x_4891_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4890_);
if (v___x_4891_ == 0)
{
uint8_t v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___f_4896_; lean_object* v___x_4897_; 
v___x_4892_ = 1;
v___x_4893_ = lean_unsigned_to_nat(1u);
v___x_4894_ = lean_box(v___x_4891_);
v___x_4895_ = lean_box(v___x_4892_);
v___f_4896_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4896_, 0, v___x_4893_);
lean_closure_set(v___f_4896_, 1, v_xs_4880_);
lean_closure_set(v___f_4896_, 2, v_tail_4890_);
lean_closure_set(v___f_4896_, 3, v___x_4894_);
lean_closure_set(v___f_4896_, 4, v___x_4895_);
v___x_4897_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4882_, v___x_4893_, v___f_4896_, v___x_4891_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4897_;
}
else
{
lean_object* v___x_4898_; 
lean_dec(v_tail_4890_);
lean_dec_ref(v_xs_4880_);
v___x_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4898_, 0, v_x_4882_);
return v___x_4898_;
}
}
else
{
lean_object* v_tail_4899_; lean_object* v_val_4900_; lean_object* v___x_4901_; uint8_t v___x_4902_; 
lean_inc_ref(v_head_4889_);
v_tail_4899_ = lean_ctor_get(v_x_4881_, 1);
lean_inc(v_tail_4899_);
lean_dec_ref_known(v_x_4881_, 2);
v_val_4900_ = lean_ctor_get(v_head_4889_, 0);
lean_inc(v_val_4900_);
lean_dec_ref_known(v_head_4889_, 1);
v___x_4901_ = lean_array_get_size(v_xs_4880_);
v___x_4902_ = lean_nat_dec_lt(v_val_4900_, v___x_4901_);
if (v___x_4902_ == 0)
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
lean_dec(v_val_4900_);
lean_dec(v_tail_4899_);
lean_dec_ref(v_x_4882_);
lean_dec_ref(v_xs_4880_);
v___x_4903_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4904_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4903_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
return v___x_4904_;
}
else
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4905_ = l_Lean_instInhabitedExpr;
v___x_4906_ = lean_array_get_borrowed(v___x_4905_, v_xs_4880_, v_val_4900_);
lean_dec(v_val_4900_);
v___x_4907_ = lean_unsigned_to_nat(1u);
v___x_4908_ = lean_mk_empty_array_with_capacity(v___x_4907_);
lean_inc(v___x_4906_);
v___x_4909_ = lean_array_push(v___x_4908_, v___x_4906_);
v___x_4910_ = l_Lean_Meta_instantiateLambda(v_x_4882_, v___x_4909_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
lean_dec_ref(v___x_4909_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
v_x_4881_ = v_tail_4899_;
v_x_4882_ = v_a_4911_;
goto _start;
}
else
{
lean_dec(v_tail_4899_);
lean_dec_ref(v_xs_4880_);
return v___x_4910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4913_, lean_object* v_xs_4914_, lean_object* v_tail_4915_, uint8_t v___x_4916_, uint8_t v___x_4917_, lean_object* v_ys_4918_, lean_object* v_value_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v___x_4925_; uint8_t v___x_4926_; 
v___x_4925_ = lean_array_get_size(v_ys_4918_);
v___x_4926_ = lean_nat_dec_eq(v___x_4925_, v___x_4913_);
if (v___x_4926_ == 0)
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
lean_dec_ref(v_value_4919_);
lean_dec(v_tail_4915_);
lean_dec_ref(v_xs_4914_);
v___x_4927_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4928_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4927_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
return v___x_4928_;
}
else
{
lean_object* v___x_4929_; 
v___x_4929_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4914_, v_tail_4915_, v_value_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; uint8_t v___x_4931_; lean_object* v___x_4932_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4930_);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4931_ = 1;
v___x_4932_ = l_Lean_Meta_mkLambdaFVars(v_ys_4918_, v_a_4930_, v___x_4916_, v___x_4917_, v___x_4916_, v___x_4917_, v___x_4931_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
return v___x_4932_;
}
else
{
return v___x_4929_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4933_, lean_object* v_x_4934_, lean_object* v_x_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4933_, v_x_4934_, v_x_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_a_4936_);
return v_res_4941_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4943_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4944_ = lean_unsigned_to_nat(2u);
v___x_4945_ = lean_unsigned_to_nat(362u);
v___x_4946_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_4947_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4948_ = l_mkPanicMessageWithDecl(v___x_4947_, v___x_4946_, v___x_4945_, v___x_4944_, v___x_4943_);
return v___x_4948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_4949_, lean_object* v_value_u2080_4950_, lean_object* v_xs_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; uint8_t v___x_4959_; 
v___x_4957_ = lean_array_get_size(v_xs_4951_);
v___x_4958_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4949_);
v___x_4959_ = lean_nat_dec_eq(v___x_4957_, v___x_4958_);
lean_dec(v___x_4958_);
if (v___x_4959_ == 0)
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
lean_dec_ref(v_xs_4951_);
lean_dec_ref(v_value_u2080_4950_);
lean_dec_ref(v_perm_4949_);
v___x_4960_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_4961_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4960_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_);
return v___x_4961_;
}
else
{
lean_object* v_mask_4962_; lean_object* v___x_4963_; 
v_mask_4962_ = lean_array_to_list(v_perm_4949_);
v___x_4963_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4951_, v_mask_4962_, v_value_u2080_4950_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_);
return v___x_4963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_4964_, lean_object* v_value_u2080_4965_, lean_object* v_xs_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_){
_start:
{
lean_object* v_res_4972_; 
v_res_4972_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_4964_, v_value_u2080_4965_, v_xs_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
lean_dec(v_a_4970_);
lean_dec_ref(v_a_4969_);
lean_dec(v_a_4968_);
lean_dec_ref(v_a_4967_);
return v_res_4972_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l_Array_instInhabited(lean_box(0));
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_4981_){
_start:
{
lean_object* v___f_4982_; lean_object* v___f_4983_; lean_object* v___f_4984_; lean_object* v___f_4985_; lean_object* v___f_4986_; lean_object* v___f_4987_; lean_object* v___f_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___f_4982_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_4983_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_4984_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_4985_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_4986_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_4987_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_4988_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_4989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4989_, 0, v___f_4982_);
lean_ctor_set(v___x_4989_, 1, v___f_4983_);
v___x_4990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v___f_4984_);
lean_ctor_set(v___x_4990_, 2, v___f_4985_);
lean_ctor_set(v___x_4990_, 3, v___f_4986_);
lean_ctor_set(v___x_4990_, 4, v___f_4987_);
v___x_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4990_);
lean_ctor_set(v___x_4991_, 1, v___f_4988_);
v___x_4992_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_4993_ = l_instInhabitedOfMonad___redArg(v___x_4991_, v___x_4992_);
v___x_4994_ = lean_panic_fn_borrowed(v___x_4993_, v_msg_4981_);
lean_dec(v___x_4993_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_4995_, lean_object* v_msg_4996_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_4996_);
return v___x_4997_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5000_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5001_ = lean_unsigned_to_nat(8u);
v___x_5002_ = lean_unsigned_to_nat(394u);
v___x_5003_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5005_ = l_mkPanicMessageWithDecl(v___x_5004_, v___x_5003_, v___x_5002_, v___x_5001_, v___x_5000_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5006_, lean_object* v_x_5007_){
_start:
{
if (lean_obj_tag(v_x_5006_) == 0)
{
return v_x_5007_;
}
else
{
lean_object* v_head_5008_; lean_object* v_fst_5009_; 
v_head_5008_ = lean_ctor_get(v_x_5006_, 0);
v_fst_5009_ = lean_ctor_get(v_head_5008_, 0);
if (lean_obj_tag(v_fst_5009_) == 0)
{
lean_object* v_tail_5010_; 
v_tail_5010_ = lean_ctor_get(v_x_5006_, 1);
lean_inc(v_tail_5010_);
lean_dec_ref_known(v_x_5006_, 2);
v_x_5006_ = v_tail_5010_;
goto _start;
}
else
{
lean_object* v_tail_5012_; lean_object* v_snd_5013_; lean_object* v_val_5014_; lean_object* v___x_5015_; uint8_t v___x_5016_; 
lean_inc_ref(v_fst_5009_);
lean_inc(v_head_5008_);
v_tail_5012_ = lean_ctor_get(v_x_5006_, 1);
lean_inc(v_tail_5012_);
lean_dec_ref_known(v_x_5006_, 2);
v_snd_5013_ = lean_ctor_get(v_head_5008_, 1);
lean_inc(v_snd_5013_);
lean_dec(v_head_5008_);
v_val_5014_ = lean_ctor_get(v_fst_5009_, 0);
lean_inc(v_val_5014_);
lean_dec_ref_known(v_fst_5009_, 1);
v___x_5015_ = lean_array_get_size(v_x_5007_);
v___x_5016_ = lean_nat_dec_lt(v_val_5014_, v___x_5015_);
if (v___x_5016_ == 0)
{
lean_object* v___x_5017_; lean_object* v___x_5018_; 
lean_dec(v_val_5014_);
lean_dec(v_snd_5013_);
lean_dec(v_tail_5012_);
lean_dec_ref(v_x_5007_);
v___x_5017_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5018_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5017_);
return v___x_5018_;
}
else
{
lean_object* v___x_5019_; 
v___x_5019_ = lean_array_set(v_x_5007_, v_val_5014_, v_snd_5013_);
lean_dec(v_val_5014_);
v_x_5006_ = v_tail_5012_;
v_x_5007_ = v___x_5019_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5021_, lean_object* v_x_5022_, lean_object* v_x_5023_){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5022_, v_x_5023_);
return v___x_5024_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5027_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5028_ = lean_unsigned_to_nat(2u);
v___x_5029_ = lean_unsigned_to_nat(384u);
v___x_5030_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5031_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5032_ = l_mkPanicMessageWithDecl(v___x_5031_, v___x_5030_, v___x_5029_, v___x_5028_, v___x_5027_);
return v___x_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5035_, lean_object* v_xs_5036_){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
v___x_5037_ = lean_array_get_size(v_xs_5036_);
v___x_5038_ = lean_array_get_size(v_perm_5035_);
v___x_5039_ = lean_nat_dec_eq(v___x_5037_, v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5040_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5041_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5040_);
return v___x_5041_;
}
else
{
lean_object* v___x_5042_; uint8_t v___x_5043_; 
v___x_5042_ = lean_unsigned_to_nat(0u);
v___x_5043_ = lean_nat_dec_eq(v___x_5037_, v___x_5042_);
if (v___x_5043_ == 0)
{
lean_object* v_dummy_5044_; lean_object* v___x_5045_; lean_object* v_ys_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v_dummy_5044_ = lean_array_fget_borrowed(v_xs_5036_, v___x_5042_);
v___x_5045_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5035_);
lean_inc(v_dummy_5044_);
v_ys_5046_ = lean_mk_array(v___x_5045_, v_dummy_5044_);
v___x_5047_ = l_Array_zip___redArg(v_perm_5035_, v_xs_5036_);
v___x_5048_ = lean_array_to_list(v___x_5047_);
v___x_5049_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5048_, v_ys_5046_);
return v___x_5049_;
}
else
{
lean_object* v___x_5050_; 
v___x_5050_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5051_, lean_object* v_xs_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5051_, v_xs_5052_);
lean_dec_ref(v_xs_5052_);
lean_dec_ref(v_perm_5051_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5054_, lean_object* v_perm_5055_, lean_object* v_xs_5056_){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5055_, v_xs_5056_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5058_, lean_object* v_perm_5059_, lean_object* v_xs_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5058_, v_perm_5059_, v_xs_5060_);
lean_dec_ref(v_xs_5060_);
lean_dec_ref(v_perm_5059_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5062_, lean_object* v_upperBound_5063_, lean_object* v_perm_5064_, lean_object* v_a_5065_, lean_object* v_b_5066_){
_start:
{
lean_object* v_a_5068_; uint8_t v___x_5075_; 
v___x_5075_ = lean_nat_dec_lt(v_a_5065_, v_upperBound_5063_);
if (v___x_5075_ == 0)
{
lean_dec(v_a_5065_);
return v_b_5066_;
}
else
{
lean_object* v___x_5076_; uint8_t v___x_5077_; 
v___x_5076_ = lean_array_get_size(v_perm_5064_);
v___x_5077_ = lean_nat_dec_lt(v_a_5065_, v___x_5076_);
if (v___x_5077_ == 0)
{
goto v___jp_5072_;
}
else
{
lean_object* v___x_5078_; 
v___x_5078_ = lean_array_fget_borrowed(v_perm_5064_, v_a_5065_);
if (lean_obj_tag(v___x_5078_) == 0)
{
goto v___jp_5072_;
}
else
{
v_a_5068_ = v_b_5066_;
goto v___jp_5067_;
}
}
}
v___jp_5067_:
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = lean_unsigned_to_nat(1u);
v___x_5070_ = lean_nat_add(v_a_5065_, v___x_5069_);
lean_dec(v_a_5065_);
v_a_5065_ = v___x_5070_;
v_b_5066_ = v_a_5068_;
goto _start;
}
v___jp_5072_:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5073_ = lean_array_fget_borrowed(v_xs_5062_, v_a_5065_);
lean_inc(v___x_5073_);
v___x_5074_ = lean_array_push(v_b_5066_, v___x_5073_);
v_a_5068_ = v___x_5074_;
goto v___jp_5067_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5079_, lean_object* v_upperBound_5080_, lean_object* v_perm_5081_, lean_object* v_a_5082_, lean_object* v_b_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5079_, v_upperBound_5080_, v_perm_5081_, v_a_5082_, v_b_5083_);
lean_dec_ref(v_perm_5081_);
lean_dec(v_upperBound_5080_);
lean_dec_ref(v_xs_5079_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5085_, lean_object* v_xs_5086_){
_start:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v_ys_5089_; lean_object* v___x_5090_; 
v___x_5087_ = lean_array_get_size(v_xs_5086_);
v___x_5088_ = lean_unsigned_to_nat(0u);
v_ys_5089_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5090_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5086_, v___x_5087_, v_perm_5085_, v___x_5088_, v_ys_5089_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5091_, lean_object* v_xs_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5091_, v_xs_5092_);
lean_dec_ref(v_xs_5092_);
lean_dec_ref(v_perm_5091_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5094_, lean_object* v_perm_5095_, lean_object* v_xs_5096_){
_start:
{
lean_object* v___x_5097_; 
v___x_5097_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5095_, v_xs_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5098_, lean_object* v_perm_5099_, lean_object* v_xs_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5098_, v_perm_5099_, v_xs_5100_);
lean_dec_ref(v_xs_5100_);
lean_dec_ref(v_perm_5099_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5102_, lean_object* v_xs_5103_, lean_object* v_upperBound_5104_, lean_object* v_perm_5105_, lean_object* v_inst_5106_, lean_object* v_R_5107_, lean_object* v_a_5108_, lean_object* v_b_5109_, lean_object* v_c_5110_){
_start:
{
lean_object* v___x_5111_; 
v___x_5111_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5103_, v_upperBound_5104_, v_perm_5105_, v_a_5108_, v_b_5109_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5112_, lean_object* v_xs_5113_, lean_object* v_upperBound_5114_, lean_object* v_perm_5115_, lean_object* v_inst_5116_, lean_object* v_R_5117_, lean_object* v_a_5118_, lean_object* v_b_5119_, lean_object* v_c_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5112_, v_xs_5113_, v_upperBound_5114_, v_perm_5115_, v_inst_5116_, v_R_5117_, v_a_5118_, v_b_5119_, v_c_5120_);
lean_dec_ref(v_perm_5115_);
lean_dec(v_upperBound_5114_);
lean_dec_ref(v_xs_5113_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(lean_object* v_msg_5122_){
_start:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5123_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5124_ = lean_panic_fn_borrowed(v___x_5123_, v_msg_5122_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_00_u03b1_5125_, lean_object* v_msg_5126_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v_msg_5126_);
return v___x_5127_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_as_5128_, size_t v_i_5129_, size_t v_stop_5130_){
_start:
{
uint8_t v___x_5131_; 
v___x_5131_ = lean_usize_dec_eq(v_i_5129_, v_stop_5130_);
if (v___x_5131_ == 0)
{
uint8_t v___x_5132_; lean_object* v___x_5133_; 
v___x_5132_ = 1;
v___x_5133_ = lean_array_uget_borrowed(v_as_5128_, v_i_5129_);
if (lean_obj_tag(v___x_5133_) == 0)
{
if (v___x_5131_ == 0)
{
size_t v___x_5134_; size_t v___x_5135_; 
v___x_5134_ = ((size_t)1ULL);
v___x_5135_ = lean_usize_add(v_i_5129_, v___x_5134_);
v_i_5129_ = v___x_5135_;
goto _start;
}
else
{
return v___x_5132_;
}
}
else
{
return v___x_5132_;
}
}
else
{
uint8_t v___x_5137_; 
v___x_5137_ = 0;
return v___x_5137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___boxed(lean_object* v_as_5138_, lean_object* v_i_5139_, lean_object* v_stop_5140_){
_start:
{
size_t v_i_boxed_5141_; size_t v_stop_boxed_5142_; uint8_t v_res_5143_; lean_object* v_r_5144_; 
v_i_boxed_5141_ = lean_unbox_usize(v_i_5139_);
lean_dec(v_i_5139_);
v_stop_boxed_5142_ = lean_unbox_usize(v_stop_5140_);
lean_dec(v_stop_5140_);
v_res_5143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v_as_5138_, v_i_boxed_5141_, v_stop_boxed_5142_);
lean_dec_ref(v_as_5138_);
v_r_5144_ = lean_box(v_res_5143_);
return v_r_5144_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5147_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5148_ = lean_unsigned_to_nat(12u);
v___x_5149_ = lean_unsigned_to_nat(433u);
v___x_5150_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5151_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5152_ = l_mkPanicMessageWithDecl(v___x_5151_, v___x_5150_, v___x_5149_, v___x_5148_, v___x_5147_);
return v___x_5152_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; 
v___x_5154_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5155_ = lean_unsigned_to_nat(10u);
v___x_5156_ = lean_unsigned_to_nat(425u);
v___x_5157_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5159_ = l_mkPanicMessageWithDecl(v___x_5158_, v___x_5157_, v___x_5156_, v___x_5155_, v___x_5154_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5160_, lean_object* v_fixedArgs_5161_, lean_object* v_varyingArgs_5162_, lean_object* v_i_5163_, lean_object* v_j_5164_, lean_object* v_xs_5165_){
_start:
{
lean_object* v_lower_5167_; lean_object* v_upper_5168_; lean_object* v___y_5173_; lean_object* v___y_5174_; lean_object* v___y_5175_; lean_object* v_lower_5183_; lean_object* v_upper_5184_; lean_object* v___x_5192_; uint8_t v___x_5193_; 
v___x_5192_ = lean_array_get_size(v_perm_5160_);
v___x_5193_ = lean_nat_dec_lt(v_i_5163_, v___x_5192_);
if (v___x_5193_ == 0)
{
lean_object* v___x_5194_; lean_object* v___x_5195_; uint8_t v___x_5196_; 
lean_dec(v_i_5163_);
lean_dec_ref(v_perm_5160_);
v___x_5194_ = lean_unsigned_to_nat(0u);
v___x_5195_ = lean_array_get_size(v_varyingArgs_5162_);
v___x_5196_ = lean_nat_dec_le(v_j_5164_, v___x_5194_);
if (v___x_5196_ == 0)
{
v_lower_5167_ = v_j_5164_;
v_upper_5168_ = v___x_5195_;
goto v___jp_5166_;
}
else
{
lean_dec(v_j_5164_);
v_lower_5167_ = v___x_5194_;
v_upper_5168_ = v___x_5195_;
goto v___jp_5166_;
}
}
else
{
lean_object* v___x_5197_; 
v___x_5197_ = lean_array_fget_borrowed(v_perm_5160_, v_i_5163_);
if (lean_obj_tag(v___x_5197_) == 1)
{
lean_object* v_val_5198_; lean_object* v___x_5199_; uint8_t v___x_5200_; 
v_val_5198_ = lean_ctor_get(v___x_5197_, 0);
v___x_5199_ = lean_array_get_size(v_fixedArgs_5161_);
v___x_5200_ = lean_nat_dec_lt(v_val_5198_, v___x_5199_);
if (v___x_5200_ == 0)
{
lean_object* v___x_5201_; lean_object* v___x_5202_; 
lean_dec_ref(v_xs_5165_);
lean_dec(v_j_5164_);
lean_dec(v_i_5163_);
lean_dec_ref(v_varyingArgs_5162_);
lean_dec_ref(v_perm_5160_);
v___x_5201_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5202_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5201_);
return v___x_5202_;
}
else
{
lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
v___x_5203_ = lean_unsigned_to_nat(1u);
v___x_5204_ = lean_nat_add(v_i_5163_, v___x_5203_);
lean_dec(v_i_5163_);
v___x_5205_ = lean_array_fget_borrowed(v_fixedArgs_5161_, v_val_5198_);
lean_inc(v___x_5205_);
v___x_5206_ = lean_array_push(v_xs_5165_, v___x_5205_);
v_i_5163_ = v___x_5204_;
v_xs_5165_ = v___x_5206_;
goto _start;
}
}
else
{
lean_object* v___x_5208_; uint8_t v___x_5209_; 
v___x_5208_ = lean_array_get_size(v_varyingArgs_5162_);
v___x_5209_ = lean_nat_dec_lt(v_j_5164_, v___x_5208_);
if (v___x_5209_ == 0)
{
lean_object* v___x_5210_; uint8_t v___x_5211_; 
lean_dec(v_j_5164_);
lean_dec_ref(v_varyingArgs_5162_);
v___x_5210_ = lean_unsigned_to_nat(0u);
v___x_5211_ = lean_nat_dec_le(v_i_5163_, v___x_5210_);
if (v___x_5211_ == 0)
{
v_lower_5183_ = v_i_5163_;
v_upper_5184_ = v___x_5192_;
goto v___jp_5182_;
}
else
{
lean_dec(v_i_5163_);
v_lower_5183_ = v___x_5210_;
v_upper_5184_ = v___x_5192_;
goto v___jp_5182_;
}
}
else
{
lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
v___x_5212_ = lean_unsigned_to_nat(1u);
v___x_5213_ = lean_nat_add(v_i_5163_, v___x_5212_);
lean_dec(v_i_5163_);
v___x_5214_ = lean_nat_add(v_j_5164_, v___x_5212_);
v___x_5215_ = lean_array_fget_borrowed(v_varyingArgs_5162_, v_j_5164_);
lean_dec(v_j_5164_);
lean_inc(v___x_5215_);
v___x_5216_ = lean_array_push(v_xs_5165_, v___x_5215_);
v_i_5163_ = v___x_5213_;
v_j_5164_ = v___x_5214_;
v_xs_5165_ = v___x_5216_;
goto _start;
}
}
}
v___jp_5166_:
{
lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; 
v___x_5169_ = l_Array_toSubarray___redArg(v_varyingArgs_5162_, v_lower_5167_, v_upper_5168_);
v___x_5170_ = l_Subarray_copy___redArg(v___x_5169_);
v___x_5171_ = l_Array_append___redArg(v_xs_5165_, v___x_5170_);
lean_dec_ref(v___x_5170_);
return v___x_5171_;
}
v___jp_5172_:
{
uint8_t v___x_5176_; 
v___x_5176_ = lean_nat_dec_lt(v___y_5173_, v___y_5175_);
if (v___x_5176_ == 0)
{
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
return v_xs_5165_;
}
else
{
size_t v___x_5177_; size_t v___x_5178_; uint8_t v___x_5179_; 
v___x_5177_ = lean_usize_of_nat(v___y_5173_);
lean_dec(v___y_5173_);
v___x_5178_ = lean_usize_of_nat(v___y_5175_);
lean_dec(v___y_5175_);
v___x_5179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(v___y_5174_, v___x_5177_, v___x_5178_);
lean_dec_ref(v___y_5174_);
if (v___x_5179_ == 0)
{
return v_xs_5165_;
}
else
{
lean_object* v___x_5180_; lean_object* v___x_5181_; 
lean_dec_ref(v_xs_5165_);
v___x_5180_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5181_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5180_);
return v___x_5181_;
}
}
}
v___jp_5182_:
{
lean_object* v___x_5185_; lean_object* v_array_5186_; lean_object* v_start_5187_; lean_object* v_stop_5188_; uint8_t v___x_5189_; 
v___x_5185_ = l_Array_toSubarray___redArg(v_perm_5160_, v_lower_5183_, v_upper_5184_);
v_array_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc_ref(v_array_5186_);
v_start_5187_ = lean_ctor_get(v___x_5185_, 1);
lean_inc(v_start_5187_);
v_stop_5188_ = lean_ctor_get(v___x_5185_, 2);
lean_inc(v_stop_5188_);
lean_dec_ref(v___x_5185_);
v___x_5189_ = lean_nat_dec_lt(v_start_5187_, v_stop_5188_);
if (v___x_5189_ == 0)
{
lean_dec(v_stop_5188_);
lean_dec(v_start_5187_);
lean_dec_ref(v_array_5186_);
return v_xs_5165_;
}
else
{
lean_object* v___x_5190_; uint8_t v___x_5191_; 
v___x_5190_ = lean_array_get_size(v_array_5186_);
v___x_5191_ = lean_nat_dec_le(v_stop_5188_, v___x_5190_);
if (v___x_5191_ == 0)
{
lean_dec(v_stop_5188_);
v___y_5173_ = v_start_5187_;
v___y_5174_ = v_array_5186_;
v___y_5175_ = v___x_5190_;
goto v___jp_5172_;
}
else
{
v___y_5173_ = v_start_5187_;
v___y_5174_ = v_array_5186_;
v___y_5175_ = v_stop_5188_;
goto v___jp_5172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5218_, lean_object* v_fixedArgs_5219_, lean_object* v_varyingArgs_5220_, lean_object* v_i_5221_, lean_object* v_j_5222_, lean_object* v_xs_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5218_, v_fixedArgs_5219_, v_varyingArgs_5220_, v_i_5221_, v_j_5222_, v_xs_5223_);
lean_dec_ref(v_fixedArgs_5219_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5225_, lean_object* v_perm_5226_, lean_object* v_fixedArgs_5227_, lean_object* v_varyingArgs_5228_, lean_object* v_i_5229_, lean_object* v_j_5230_, lean_object* v_xs_5231_){
_start:
{
lean_object* v___x_5232_; 
v___x_5232_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5226_, v_fixedArgs_5227_, v_varyingArgs_5228_, v_i_5229_, v_j_5230_, v_xs_5231_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5233_, lean_object* v_perm_5234_, lean_object* v_fixedArgs_5235_, lean_object* v_varyingArgs_5236_, lean_object* v_i_5237_, lean_object* v_j_5238_, lean_object* v_xs_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5233_, v_perm_5234_, v_fixedArgs_5235_, v_varyingArgs_5236_, v_i_5237_, v_j_5238_, v_xs_5239_);
lean_dec_ref(v_fixedArgs_5235_);
return v_res_5240_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; 
v___x_5243_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5244_ = lean_unsigned_to_nat(2u);
v___x_5245_ = lean_unsigned_to_nat(416u);
v___x_5246_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5247_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5248_ = l_mkPanicMessageWithDecl(v___x_5247_, v___x_5246_, v___x_5245_, v___x_5244_, v___x_5243_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5249_, lean_object* v_fixedArgs_5250_, lean_object* v_varyingArgs_5251_){
_start:
{
lean_object* v___x_5252_; lean_object* v___x_5253_; uint8_t v___x_5254_; 
v___x_5252_ = lean_array_get_size(v_fixedArgs_5250_);
v___x_5253_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5249_);
v___x_5254_ = lean_nat_dec_eq(v___x_5252_, v___x_5253_);
lean_dec(v___x_5253_);
if (v___x_5254_ == 0)
{
lean_object* v___x_5255_; lean_object* v___x_5256_; 
lean_dec_ref(v_varyingArgs_5251_);
lean_dec_ref(v_perm_5249_);
v___x_5255_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5256_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___redArg(v___x_5255_);
return v___x_5256_;
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; 
v___x_5257_ = lean_unsigned_to_nat(0u);
v___x_5258_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5259_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5249_, v_fixedArgs_5250_, v_varyingArgs_5251_, v___x_5257_, v___x_5257_, v___x_5258_);
return v___x_5259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5260_, lean_object* v_fixedArgs_5261_, lean_object* v_varyingArgs_5262_){
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5260_, v_fixedArgs_5261_, v_varyingArgs_5262_);
lean_dec_ref(v_fixedArgs_5261_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5264_, lean_object* v_perm_5265_, lean_object* v_fixedArgs_5266_, lean_object* v_varyingArgs_5267_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5265_, v_fixedArgs_5266_, v_varyingArgs_5267_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5269_, lean_object* v_perm_5270_, lean_object* v_fixedArgs_5271_, lean_object* v_varyingArgs_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5269_, v_perm_5270_, v_fixedArgs_5271_, v_varyingArgs_5272_);
lean_dec_ref(v_fixedArgs_5271_);
return v_res_5273_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5274_, lean_object* v_x_5275_){
_start:
{
if (lean_obj_tag(v_x_5274_) == 0)
{
if (lean_obj_tag(v_x_5275_) == 0)
{
uint8_t v___x_5276_; 
v___x_5276_ = 1;
return v___x_5276_;
}
else
{
uint8_t v___x_5277_; 
v___x_5277_ = 0;
return v___x_5277_;
}
}
else
{
if (lean_obj_tag(v_x_5275_) == 0)
{
uint8_t v___x_5278_; 
v___x_5278_ = 0;
return v___x_5278_;
}
else
{
lean_object* v_val_5279_; lean_object* v_val_5280_; uint8_t v___x_5281_; 
v_val_5279_ = lean_ctor_get(v_x_5274_, 0);
v_val_5280_ = lean_ctor_get(v_x_5275_, 0);
v___x_5281_ = lean_nat_dec_eq(v_val_5279_, v_val_5280_);
return v___x_5281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5282_, lean_object* v_x_5283_){
_start:
{
uint8_t v_res_5284_; lean_object* v_r_5285_; 
v_res_5284_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5282_, v_x_5283_);
lean_dec(v_x_5283_);
lean_dec(v_x_5282_);
v_r_5285_ = lean_box(v_res_5284_);
return v_r_5285_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5286_, lean_object* v_ys_5287_, lean_object* v_x_5288_){
_start:
{
lean_object* v_zero_5289_; uint8_t v_isZero_5290_; 
v_zero_5289_ = lean_unsigned_to_nat(0u);
v_isZero_5290_ = lean_nat_dec_eq(v_x_5288_, v_zero_5289_);
if (v_isZero_5290_ == 1)
{
lean_dec(v_x_5288_);
return v_isZero_5290_;
}
else
{
lean_object* v_one_5291_; lean_object* v_n_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; 
v_one_5291_ = lean_unsigned_to_nat(1u);
v_n_5292_ = lean_nat_sub(v_x_5288_, v_one_5291_);
lean_dec(v_x_5288_);
v___x_5293_ = lean_array_fget_borrowed(v_xs_5286_, v_n_5292_);
v___x_5294_ = lean_array_fget_borrowed(v_ys_5287_, v_n_5292_);
v___x_5295_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5293_, v___x_5294_);
if (v___x_5295_ == 0)
{
lean_dec(v_n_5292_);
return v___x_5295_;
}
else
{
v_x_5288_ = v_n_5292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5297_, lean_object* v_ys_5298_, lean_object* v_x_5299_){
_start:
{
uint8_t v_res_5300_; lean_object* v_r_5301_; 
v_res_5300_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5297_, v_ys_5298_, v_x_5299_);
lean_dec_ref(v_ys_5298_);
lean_dec_ref(v_xs_5297_);
v_r_5301_ = lean_box(v_res_5300_);
return v_r_5301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5302_, size_t v_i_5303_, lean_object* v_bs_5304_){
_start:
{
uint8_t v___x_5305_; 
v___x_5305_ = lean_usize_dec_lt(v_i_5303_, v_sz_5302_);
if (v___x_5305_ == 0)
{
return v_bs_5304_;
}
else
{
lean_object* v_v_5306_; lean_object* v___x_5307_; lean_object* v_bs_x27_5308_; lean_object* v___x_5309_; size_t v___x_5310_; size_t v___x_5311_; lean_object* v___x_5312_; 
v_v_5306_ = lean_array_uget(v_bs_5304_, v_i_5303_);
v___x_5307_ = lean_unsigned_to_nat(0u);
v_bs_x27_5308_ = lean_array_uset(v_bs_5304_, v_i_5303_, v___x_5307_);
v___x_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5309_, 0, v_v_5306_);
v___x_5310_ = ((size_t)1ULL);
v___x_5311_ = lean_usize_add(v_i_5303_, v___x_5310_);
v___x_5312_ = lean_array_uset(v_bs_x27_5308_, v_i_5303_, v___x_5309_);
v_i_5303_ = v___x_5311_;
v_bs_5304_ = v___x_5312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5314_, lean_object* v_i_5315_, lean_object* v_bs_5316_){
_start:
{
size_t v_sz_boxed_5317_; size_t v_i_boxed_5318_; lean_object* v_res_5319_; 
v_sz_boxed_5317_ = lean_unbox_usize(v_sz_5314_);
lean_dec(v_sz_5314_);
v_i_boxed_5318_ = lean_unbox_usize(v_i_5315_);
lean_dec(v_i_5315_);
v_res_5319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5317_, v_i_boxed_5318_, v_bs_5316_);
return v_res_5319_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5320_, lean_object* v_as_5321_, size_t v_i_5322_, size_t v_stop_5323_){
_start:
{
uint8_t v___x_5324_; 
v___x_5324_ = lean_usize_dec_eq(v_i_5322_, v_stop_5323_);
if (v___x_5324_ == 0)
{
lean_object* v_numFixed_5325_; uint8_t v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; size_t v_sz_5329_; size_t v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; uint8_t v___x_5338_; 
v_numFixed_5325_ = lean_ctor_get(v_fixedParamPerms_5320_, 0);
v___x_5326_ = 1;
v___x_5327_ = lean_array_uget_borrowed(v_as_5321_, v_i_5322_);
lean_inc(v_numFixed_5325_);
v___x_5328_ = l_Array_range(v_numFixed_5325_);
v_sz_5329_ = lean_array_size(v___x_5328_);
v___x_5330_ = ((size_t)0ULL);
v___x_5331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5329_, v___x_5330_, v___x_5328_);
v___x_5332_ = lean_array_get_size(v___x_5327_);
v___x_5333_ = lean_nat_sub(v___x_5332_, v_numFixed_5325_);
v___x_5334_ = lean_box(0);
v___x_5335_ = lean_mk_array(v___x_5333_, v___x_5334_);
v___x_5336_ = l_Array_append___redArg(v___x_5331_, v___x_5335_);
lean_dec_ref(v___x_5335_);
v___x_5337_ = lean_array_get_size(v___x_5336_);
v___x_5338_ = lean_nat_dec_eq(v___x_5332_, v___x_5337_);
if (v___x_5338_ == 0)
{
lean_dec_ref(v___x_5336_);
lean_dec_ref(v_fixedParamPerms_5320_);
return v___x_5326_;
}
else
{
uint8_t v___x_5339_; 
v___x_5339_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5327_, v___x_5336_, v___x_5332_);
lean_dec_ref(v___x_5336_);
if (v___x_5339_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5320_);
return v___x_5326_;
}
else
{
if (v___x_5324_ == 0)
{
size_t v___x_5340_; size_t v___x_5341_; 
v___x_5340_ = ((size_t)1ULL);
v___x_5341_ = lean_usize_add(v_i_5322_, v___x_5340_);
v_i_5322_ = v___x_5341_;
goto _start;
}
else
{
lean_dec_ref(v_fixedParamPerms_5320_);
return v___x_5326_;
}
}
}
}
else
{
uint8_t v___x_5343_; 
lean_dec_ref(v_fixedParamPerms_5320_);
v___x_5343_ = 0;
return v___x_5343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5344_, lean_object* v_as_5345_, lean_object* v_i_5346_, lean_object* v_stop_5347_){
_start:
{
size_t v_i_boxed_5348_; size_t v_stop_boxed_5349_; uint8_t v_res_5350_; lean_object* v_r_5351_; 
v_i_boxed_5348_ = lean_unbox_usize(v_i_5346_);
lean_dec(v_i_5346_);
v_stop_boxed_5349_ = lean_unbox_usize(v_stop_5347_);
lean_dec(v_stop_5347_);
v_res_5350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5344_, v_as_5345_, v_i_boxed_5348_, v_stop_boxed_5349_);
lean_dec_ref(v_as_5345_);
v_r_5351_ = lean_box(v_res_5350_);
return v_r_5351_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5352_){
_start:
{
lean_object* v_perms_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; uint8_t v___x_5356_; 
v_perms_5353_ = lean_ctor_get(v_fixedParamPerms_5352_, 1);
lean_inc_ref(v_perms_5353_);
v___x_5354_ = lean_unsigned_to_nat(0u);
v___x_5355_ = lean_array_get_size(v_perms_5353_);
v___x_5356_ = lean_nat_dec_lt(v___x_5354_, v___x_5355_);
if (v___x_5356_ == 0)
{
uint8_t v___x_5357_; 
lean_dec_ref(v_perms_5353_);
lean_dec_ref(v_fixedParamPerms_5352_);
v___x_5357_ = 1;
return v___x_5357_;
}
else
{
if (v___x_5356_ == 0)
{
lean_dec_ref(v_perms_5353_);
lean_dec_ref(v_fixedParamPerms_5352_);
return v___x_5356_;
}
else
{
size_t v___x_5358_; size_t v___x_5359_; uint8_t v___x_5360_; 
v___x_5358_ = ((size_t)0ULL);
v___x_5359_ = lean_usize_of_nat(v___x_5355_);
v___x_5360_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5352_, v_perms_5353_, v___x_5358_, v___x_5359_);
lean_dec_ref(v_perms_5353_);
if (v___x_5360_ == 0)
{
return v___x_5356_;
}
else
{
uint8_t v___x_5361_; 
v___x_5361_ = 0;
return v___x_5361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5362_){
_start:
{
uint8_t v_res_5363_; lean_object* v_r_5364_; 
v_res_5363_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5362_);
v_r_5364_ = lean_box(v_res_5363_);
return v_r_5364_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5365_, lean_object* v_ys_5366_, lean_object* v_hsz_5367_, lean_object* v_x_5368_, lean_object* v_x_5369_){
_start:
{
uint8_t v___x_5370_; 
v___x_5370_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5365_, v_ys_5366_, v_x_5368_);
return v___x_5370_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5371_, lean_object* v_ys_5372_, lean_object* v_hsz_5373_, lean_object* v_x_5374_, lean_object* v_x_5375_){
_start:
{
uint8_t v_res_5376_; lean_object* v_r_5377_; 
v_res_5376_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5371_, v_ys_5372_, v_hsz_5373_, v_x_5374_, v_x_5375_);
lean_dec_ref(v_ys_5372_);
lean_dec_ref(v_xs_5371_);
v_r_5377_ = lean_box(v_res_5376_);
return v_r_5377_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5378_; 
v___x_5378_ = l_Array_instInhabited(lean_box(0));
return v___x_5378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5379_){
_start:
{
lean_object* v___f_5380_; lean_object* v___f_5381_; lean_object* v___f_5382_; lean_object* v___f_5383_; lean_object* v___f_5384_; lean_object* v___f_5385_; lean_object* v___f_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___f_5380_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5381_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5382_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5383_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5384_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5385_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5386_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5387_, 0, v___f_5380_);
lean_ctor_set(v___x_5387_, 1, v___f_5381_);
v___x_5388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5387_);
lean_ctor_set(v___x_5388_, 1, v___f_5382_);
lean_ctor_set(v___x_5388_, 2, v___f_5383_);
lean_ctor_set(v___x_5388_, 3, v___f_5384_);
lean_ctor_set(v___x_5388_, 4, v___f_5385_);
v___x_5389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5389_, 0, v___x_5388_);
lean_ctor_set(v___x_5389_, 1, v___f_5386_);
v___x_5390_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5391_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5391_);
lean_ctor_set(v___x_5392_, 1, v___x_5391_);
v___x_5393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5390_);
lean_ctor_set(v___x_5393_, 1, v___x_5392_);
v___x_5394_ = l_instInhabitedOfMonad___redArg(v___x_5389_, v___x_5393_);
v___x_5395_ = lean_panic_fn_borrowed(v___x_5394_, v_msg_5379_);
lean_dec(v___x_5394_);
return v___x_5395_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5396_; 
v___x_5396_ = l_Array_instInhabited(lean_box(0));
return v___x_5396_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5397_){
_start:
{
lean_object* v___f_5398_; lean_object* v___f_5399_; lean_object* v___f_5400_; lean_object* v___f_5401_; lean_object* v___f_5402_; lean_object* v___f_5403_; lean_object* v___f_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___f_5398_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5399_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5400_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5401_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5402_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5403_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5404_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5405_, 0, v___f_5398_);
lean_ctor_set(v___x_5405_, 1, v___f_5399_);
v___x_5406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5405_);
lean_ctor_set(v___x_5406_, 1, v___f_5400_);
lean_ctor_set(v___x_5406_, 2, v___f_5401_);
lean_ctor_set(v___x_5406_, 3, v___f_5402_);
lean_ctor_set(v___x_5406_, 4, v___f_5403_);
v___x_5407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5406_);
lean_ctor_set(v___x_5407_, 1, v___f_5404_);
v___x_5408_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5408_);
v___x_5410_ = l_instInhabitedOfMonad___redArg(v___x_5407_, v___x_5409_);
v___x_5411_ = lean_panic_fn_borrowed(v___x_5410_, v_msg_5397_);
lean_dec(v___x_5410_);
return v___x_5411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5412_, uint8_t v___x_5413_, lean_object* v_as_5414_, size_t v_sz_5415_, size_t v_i_5416_, lean_object* v_b_5417_){
_start:
{
lean_object* v_a_5419_; uint8_t v___x_5423_; 
v___x_5423_ = lean_usize_dec_lt(v_i_5416_, v_sz_5415_);
if (v___x_5423_ == 0)
{
return v_b_5417_;
}
else
{
lean_object* v_fst_5424_; lean_object* v_snd_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5446_; 
v_fst_5424_ = lean_ctor_get(v_b_5417_, 0);
v_snd_5425_ = lean_ctor_get(v_b_5417_, 1);
v_isSharedCheck_5446_ = !lean_is_exclusive(v_b_5417_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5427_ = v_b_5417_;
v_isShared_5428_ = v_isSharedCheck_5446_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_snd_5425_);
lean_inc(v_fst_5424_);
lean_dec(v_b_5417_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5446_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v_a_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v_a_5433_ = lean_array_uget_borrowed(v_as_5414_, v_i_5416_);
v___x_5434_ = lean_box(0);
v___x_5435_ = lean_array_get_borrowed(v___x_5434_, v___x_5412_, v_a_5433_);
if (lean_obj_tag(v___x_5435_) == 1)
{
lean_object* v_val_5436_; uint8_t v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; uint8_t v___x_5440_; 
v_val_5436_ = lean_ctor_get(v___x_5435_, 0);
v___x_5437_ = 0;
v___x_5438_ = lean_box(v___x_5437_);
v___x_5439_ = lean_array_get(v___x_5438_, v_fst_5424_, v_val_5436_);
lean_dec(v___x_5438_);
v___x_5440_ = lean_unbox(v___x_5439_);
lean_dec(v___x_5439_);
if (v___x_5440_ == 0)
{
if (v___x_5413_ == 0)
{
goto v___jp_5429_;
}
else
{
lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
lean_del_object(v___x_5427_);
lean_dec(v_snd_5425_);
v___x_5441_ = lean_box(v___x_5413_);
v___x_5442_ = lean_array_set(v_fst_5424_, v_val_5436_, v___x_5441_);
v___x_5443_ = lean_box(v___x_5413_);
v___x_5444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5442_);
lean_ctor_set(v___x_5444_, 1, v___x_5443_);
v_a_5419_ = v___x_5444_;
goto v___jp_5418_;
}
}
else
{
goto v___jp_5429_;
}
}
else
{
lean_object* v___x_5445_; 
lean_del_object(v___x_5427_);
v___x_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5445_, 0, v_fst_5424_);
lean_ctor_set(v___x_5445_, 1, v_snd_5425_);
v_a_5419_ = v___x_5445_;
goto v___jp_5418_;
}
v___jp_5429_:
{
lean_object* v___x_5431_; 
if (v_isShared_5428_ == 0)
{
v___x_5431_ = v___x_5427_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_fst_5424_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v_snd_5425_);
v___x_5431_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
v_a_5419_ = v___x_5431_;
goto v___jp_5418_;
}
}
}
}
v___jp_5418_:
{
size_t v___x_5420_; size_t v___x_5421_; 
v___x_5420_ = ((size_t)1ULL);
v___x_5421_ = lean_usize_add(v_i_5416_, v___x_5420_);
v_i_5416_ = v___x_5421_;
v_b_5417_ = v_a_5419_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5447_, lean_object* v___x_5448_, lean_object* v_as_5449_, lean_object* v_sz_5450_, lean_object* v_i_5451_, lean_object* v_b_5452_){
_start:
{
uint8_t v___x_8295__boxed_5453_; size_t v_sz_boxed_5454_; size_t v_i_boxed_5455_; lean_object* v_res_5456_; 
v___x_8295__boxed_5453_ = lean_unbox(v___x_5448_);
v_sz_boxed_5454_ = lean_unbox_usize(v_sz_5450_);
lean_dec(v_sz_5450_);
v_i_boxed_5455_ = lean_unbox_usize(v_i_5451_);
lean_dec(v_i_5451_);
v_res_5456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5447_, v___x_8295__boxed_5453_, v_as_5449_, v_sz_boxed_5454_, v_i_boxed_5455_, v_b_5452_);
lean_dec_ref(v_as_5449_);
lean_dec_ref(v___x_5447_);
return v_res_5456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5457_, lean_object* v___x_5458_, lean_object* v_fixedParamPerms_5459_, lean_object* v_next_5460_, lean_object* v_a_5461_, lean_object* v_b_5462_){
_start:
{
lean_object* v_a_5464_; uint8_t v___x_5468_; 
v___x_5468_ = lean_nat_dec_lt(v_a_5461_, v_upperBound_5457_);
if (v___x_5468_ == 0)
{
lean_dec(v_a_5461_);
return v_b_5462_;
}
else
{
lean_object* v_fst_5469_; lean_object* v_snd_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5506_; 
v_fst_5469_ = lean_ctor_get(v_b_5462_, 0);
v_snd_5470_ = lean_ctor_get(v_b_5462_, 1);
v_isSharedCheck_5506_ = !lean_is_exclusive(v_b_5462_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5472_ = v_b_5462_;
v_isShared_5473_ = v_isSharedCheck_5506_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_snd_5470_);
lean_inc(v_fst_5469_);
lean_dec(v_b_5462_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5506_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v___x_5474_; 
v___x_5474_ = lean_array_fget_borrowed(v___x_5458_, v_a_5461_);
if (lean_obj_tag(v___x_5474_) == 1)
{
lean_object* v_val_5475_; uint8_t v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; uint8_t v___x_5479_; 
v_val_5475_ = lean_ctor_get(v___x_5474_, 0);
v___x_5476_ = 0;
v___x_5477_ = lean_box(v___x_5476_);
v___x_5478_ = lean_array_get(v___x_5477_, v_fst_5469_, v_val_5475_);
lean_dec(v___x_5477_);
v___x_5479_ = lean_unbox(v___x_5478_);
if (v___x_5479_ == 0)
{
lean_object* v___x_5481_; 
lean_dec(v___x_5478_);
if (v_isShared_5473_ == 0)
{
v___x_5481_ = v___x_5472_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_fst_5469_);
lean_ctor_set(v_reuseFailAlloc_5482_, 1, v_snd_5470_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
v_a_5464_ = v___x_5481_;
goto v___jp_5463_;
}
}
else
{
lean_object* v_revDeps_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5488_; 
v_revDeps_5483_ = lean_ctor_get(v_fixedParamPerms_5459_, 2);
v___x_5484_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_setVarying___closed__0, &l_Lean_Elab_FixedParams_Info_setVarying___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_setVarying___closed__0);
v___x_5485_ = lean_array_get_borrowed(v___x_5484_, v_revDeps_5483_, v_next_5460_);
v___x_5486_ = lean_array_get_borrowed(v___x_5484_, v___x_5485_, v_a_5461_);
if (v_isShared_5473_ == 0)
{
v___x_5488_ = v___x_5472_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_fst_5469_);
lean_ctor_set(v_reuseFailAlloc_5502_, 1, v_snd_5470_);
v___x_5488_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
size_t v_sz_5489_; size_t v___x_5490_; uint8_t v___x_5491_; lean_object* v___x_5492_; lean_object* v_fst_5493_; lean_object* v_snd_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5501_; 
v_sz_5489_ = lean_array_size(v___x_5486_);
v___x_5490_ = ((size_t)0ULL);
v___x_5491_ = lean_unbox(v___x_5478_);
lean_dec(v___x_5478_);
v___x_5492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5458_, v___x_5491_, v___x_5486_, v_sz_5489_, v___x_5490_, v___x_5488_);
v_fst_5493_ = lean_ctor_get(v___x_5492_, 0);
v_snd_5494_ = lean_ctor_get(v___x_5492_, 1);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5496_ = v___x_5492_;
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_snd_5494_);
lean_inc(v_fst_5493_);
lean_dec(v___x_5492_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5499_; 
if (v_isShared_5497_ == 0)
{
v___x_5499_ = v___x_5496_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_fst_5493_);
lean_ctor_set(v_reuseFailAlloc_5500_, 1, v_snd_5494_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
v_a_5464_ = v___x_5499_;
goto v___jp_5463_;
}
}
}
}
}
else
{
lean_object* v___x_5504_; 
if (v_isShared_5473_ == 0)
{
v___x_5504_ = v___x_5472_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_fst_5469_);
lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_snd_5470_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
v_a_5464_ = v___x_5504_;
goto v___jp_5463_;
}
}
}
}
v___jp_5463_:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; 
v___x_5465_ = lean_unsigned_to_nat(1u);
v___x_5466_ = lean_nat_add(v_a_5461_, v___x_5465_);
lean_dec(v_a_5461_);
v_a_5461_ = v___x_5466_;
v_b_5462_ = v_a_5464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5507_, lean_object* v___x_5508_, lean_object* v_fixedParamPerms_5509_, lean_object* v_next_5510_, lean_object* v_a_5511_, lean_object* v_b_5512_){
_start:
{
lean_object* v_res_5513_; 
v_res_5513_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5507_, v___x_5508_, v_fixedParamPerms_5509_, v_next_5510_, v_a_5511_, v_b_5512_);
lean_dec(v_next_5510_);
lean_dec_ref(v_fixedParamPerms_5509_);
lean_dec_ref(v___x_5508_);
lean_dec(v_upperBound_5507_);
return v_res_5513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5514_, lean_object* v___x_5515_, lean_object* v_fixedParamPerms_5516_, lean_object* v_a_5517_, lean_object* v_b_5518_){
_start:
{
uint8_t v___x_5519_; 
v___x_5519_ = lean_nat_dec_lt(v_a_5517_, v_upperBound_5514_);
if (v___x_5519_ == 0)
{
lean_dec(v_a_5517_);
return v_b_5518_;
}
else
{
lean_object* v_fst_5520_; lean_object* v_snd_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5544_; 
v_fst_5520_ = lean_ctor_get(v_b_5518_, 0);
v_snd_5521_ = lean_ctor_get(v_b_5518_, 1);
v_isSharedCheck_5544_ = !lean_is_exclusive(v_b_5518_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5523_ = v_b_5518_;
v_isShared_5524_ = v_isSharedCheck_5544_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_snd_5521_);
lean_inc(v_fst_5520_);
lean_dec(v_b_5518_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5544_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5529_; 
v___x_5525_ = lean_array_fget_borrowed(v___x_5515_, v_a_5517_);
v___x_5526_ = lean_array_get_size(v___x_5525_);
v___x_5527_ = lean_unsigned_to_nat(0u);
if (v_isShared_5524_ == 0)
{
v___x_5529_ = v___x_5523_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_fst_5520_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v_snd_5521_);
v___x_5529_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
lean_object* v___x_5530_; lean_object* v_fst_5531_; lean_object* v_snd_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5542_; 
v___x_5530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5526_, v___x_5525_, v_fixedParamPerms_5516_, v_a_5517_, v___x_5527_, v___x_5529_);
v_fst_5531_ = lean_ctor_get(v___x_5530_, 0);
v_snd_5532_ = lean_ctor_get(v___x_5530_, 1);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5534_ = v___x_5530_;
v_isShared_5535_ = v_isSharedCheck_5542_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_snd_5532_);
lean_inc(v_fst_5531_);
lean_dec(v___x_5530_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5542_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_fst_5531_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v_snd_5532_);
v___x_5537_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
v___x_5538_ = lean_unsigned_to_nat(1u);
v___x_5539_ = lean_nat_add(v_a_5517_, v___x_5538_);
lean_dec(v_a_5517_);
v_a_5517_ = v___x_5539_;
v_b_5518_ = v___x_5537_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5545_, lean_object* v___x_5546_, lean_object* v_fixedParamPerms_5547_, lean_object* v_a_5548_, lean_object* v_b_5549_){
_start:
{
lean_object* v_res_5550_; 
v_res_5550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5545_, v___x_5546_, v_fixedParamPerms_5547_, v_a_5548_, v_b_5549_);
lean_dec_ref(v_fixedParamPerms_5547_);
lean_dec_ref(v___x_5546_);
lean_dec(v_upperBound_5545_);
return v_res_5550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5551_, lean_object* v___x_5552_, lean_object* v_fixedParamPerms_5553_, lean_object* v_a_5554_){
_start:
{
lean_object* v_snd_5555_; uint8_t v___x_5556_; 
v_snd_5555_ = lean_ctor_get(v_a_5554_, 1);
v___x_5556_ = lean_unbox(v_snd_5555_);
if (v___x_5556_ == 0)
{
lean_object* v_fst_5557_; lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5564_; 
lean_inc(v_snd_5555_);
v_fst_5557_ = lean_ctor_get(v_a_5554_, 0);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_a_5554_);
if (v_isSharedCheck_5564_ == 0)
{
lean_object* v_unused_5565_; 
v_unused_5565_ = lean_ctor_get(v_a_5554_, 1);
lean_dec(v_unused_5565_);
v___x_5559_ = v_a_5554_;
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
else
{
lean_inc(v_fst_5557_);
lean_dec(v_a_5554_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5564_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v___x_5562_; 
if (v_isShared_5560_ == 0)
{
v___x_5562_ = v___x_5559_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_fst_5557_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v_snd_5555_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
else
{
lean_object* v_fst_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5587_; 
v_fst_5566_ = lean_ctor_get(v_a_5554_, 0);
v_isSharedCheck_5587_ = !lean_is_exclusive(v_a_5554_);
if (v_isSharedCheck_5587_ == 0)
{
lean_object* v_unused_5588_; 
v_unused_5588_ = lean_ctor_get(v_a_5554_, 1);
lean_dec(v_unused_5588_);
v___x_5568_ = v_a_5554_;
v_isShared_5569_ = v_isSharedCheck_5587_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_fst_5566_);
lean_dec(v_a_5554_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5587_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
uint8_t v_changed_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5574_; 
v_changed_5570_ = 0;
v___x_5571_ = lean_unsigned_to_nat(0u);
v___x_5572_ = lean_box(v_changed_5570_);
if (v_isShared_5569_ == 0)
{
lean_ctor_set(v___x_5568_, 1, v___x_5572_);
v___x_5574_ = v___x_5568_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v_fst_5566_);
lean_ctor_set(v_reuseFailAlloc_5586_, 1, v___x_5572_);
v___x_5574_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
lean_object* v___x_5575_; lean_object* v_fst_5576_; lean_object* v_snd_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5585_; 
v___x_5575_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5551_, v___x_5552_, v_fixedParamPerms_5553_, v___x_5571_, v___x_5574_);
v_fst_5576_ = lean_ctor_get(v___x_5575_, 0);
v_snd_5577_ = lean_ctor_get(v___x_5575_, 1);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5579_ = v___x_5575_;
v_isShared_5580_ = v_isSharedCheck_5585_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_snd_5577_);
lean_inc(v_fst_5576_);
lean_dec(v___x_5575_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5585_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5582_; 
if (v_isShared_5580_ == 0)
{
v___x_5582_ = v___x_5579_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_fst_5576_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v_snd_5577_);
v___x_5582_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
v_a_5554_ = v___x_5582_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5589_, lean_object* v___x_5590_, lean_object* v_fixedParamPerms_5591_, lean_object* v_a_5592_){
_start:
{
lean_object* v_res_5593_; 
v_res_5593_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5589_, v___x_5590_, v_fixedParamPerms_5591_, v_a_5592_);
lean_dec_ref(v_fixedParamPerms_5591_);
lean_dec_ref(v___x_5590_);
lean_dec(v___x_5589_);
return v_res_5593_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5594_, lean_object* v_a_5595_, lean_object* v_b_5596_){
_start:
{
lean_object* v_a_5598_; uint8_t v___x_5602_; 
v___x_5602_ = lean_nat_dec_lt(v_a_5595_, v_upperBound_5594_);
if (v___x_5602_ == 0)
{
lean_dec(v_a_5595_);
return v_b_5596_;
}
else
{
lean_object* v_snd_5603_; lean_object* v_snd_5604_; lean_object* v_snd_5605_; lean_object* v_snd_5606_; lean_object* v_fst_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5719_; 
v_snd_5603_ = lean_ctor_get(v_b_5596_, 1);
lean_inc(v_snd_5603_);
v_snd_5604_ = lean_ctor_get(v_snd_5603_, 1);
lean_inc(v_snd_5604_);
v_snd_5605_ = lean_ctor_get(v_snd_5604_, 1);
lean_inc(v_snd_5605_);
v_snd_5606_ = lean_ctor_get(v_snd_5605_, 1);
lean_inc(v_snd_5606_);
v_fst_5607_ = lean_ctor_get(v_b_5596_, 0);
v_isSharedCheck_5719_ = !lean_is_exclusive(v_b_5596_);
if (v_isSharedCheck_5719_ == 0)
{
lean_object* v_unused_5720_; 
v_unused_5720_ = lean_ctor_get(v_b_5596_, 1);
lean_dec(v_unused_5720_);
v___x_5609_ = v_b_5596_;
v_isShared_5610_ = v_isSharedCheck_5719_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_fst_5607_);
lean_dec(v_b_5596_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5719_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v_fst_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5717_; 
v_fst_5611_ = lean_ctor_get(v_snd_5603_, 0);
v_isSharedCheck_5717_ = !lean_is_exclusive(v_snd_5603_);
if (v_isSharedCheck_5717_ == 0)
{
lean_object* v_unused_5718_; 
v_unused_5718_ = lean_ctor_get(v_snd_5603_, 1);
lean_dec(v_unused_5718_);
v___x_5613_ = v_snd_5603_;
v_isShared_5614_ = v_isSharedCheck_5717_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_fst_5611_);
lean_dec(v_snd_5603_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5717_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v_fst_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5715_; 
v_fst_5615_ = lean_ctor_get(v_snd_5604_, 0);
v_isSharedCheck_5715_ = !lean_is_exclusive(v_snd_5604_);
if (v_isSharedCheck_5715_ == 0)
{
lean_object* v_unused_5716_; 
v_unused_5716_ = lean_ctor_get(v_snd_5604_, 1);
lean_dec(v_unused_5716_);
v___x_5617_ = v_snd_5604_;
v_isShared_5618_ = v_isSharedCheck_5715_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_fst_5615_);
lean_dec(v_snd_5604_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5715_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v_fst_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5713_; 
v_fst_5619_ = lean_ctor_get(v_snd_5605_, 0);
v_isSharedCheck_5713_ = !lean_is_exclusive(v_snd_5605_);
if (v_isSharedCheck_5713_ == 0)
{
lean_object* v_unused_5714_; 
v_unused_5714_ = lean_ctor_get(v_snd_5605_, 1);
lean_dec(v_unused_5714_);
v___x_5621_ = v_snd_5605_;
v_isShared_5622_ = v_isSharedCheck_5713_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_fst_5619_);
lean_dec(v_snd_5605_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5713_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v_array_5623_; lean_object* v_start_5624_; lean_object* v_stop_5625_; uint8_t v___x_5626_; 
v_array_5623_ = lean_ctor_get(v_snd_5606_, 0);
v_start_5624_ = lean_ctor_get(v_snd_5606_, 1);
v_stop_5625_ = lean_ctor_get(v_snd_5606_, 2);
v___x_5626_ = lean_nat_dec_lt(v_start_5624_, v_stop_5625_);
if (v___x_5626_ == 0)
{
lean_object* v___x_5628_; 
lean_dec(v_a_5595_);
if (v_isShared_5622_ == 0)
{
v___x_5628_ = v___x_5621_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_fst_5619_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v_snd_5606_);
v___x_5628_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5630_; 
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 1, v___x_5628_);
v___x_5630_ = v___x_5617_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_fst_5615_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v___x_5628_);
v___x_5630_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
lean_object* v___x_5632_; 
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 1, v___x_5630_);
v___x_5632_ = v___x_5613_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_fst_5611_);
lean_ctor_set(v_reuseFailAlloc_5636_, 1, v___x_5630_);
v___x_5632_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
lean_object* v___x_5634_; 
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 1, v___x_5632_);
v___x_5634_ = v___x_5609_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_fst_5607_);
lean_ctor_set(v_reuseFailAlloc_5635_, 1, v___x_5632_);
v___x_5634_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
return v___x_5634_;
}
}
}
}
}
else
{
lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5709_; 
lean_inc(v_stop_5625_);
lean_inc(v_start_5624_);
lean_inc_ref(v_array_5623_);
v_isSharedCheck_5709_ = !lean_is_exclusive(v_snd_5606_);
if (v_isSharedCheck_5709_ == 0)
{
lean_object* v_unused_5710_; lean_object* v_unused_5711_; lean_object* v_unused_5712_; 
v_unused_5710_ = lean_ctor_get(v_snd_5606_, 2);
lean_dec(v_unused_5710_);
v_unused_5711_ = lean_ctor_get(v_snd_5606_, 1);
lean_dec(v_unused_5711_);
v_unused_5712_ = lean_ctor_get(v_snd_5606_, 0);
lean_dec(v_unused_5712_);
v___x_5640_ = v_snd_5606_;
v_isShared_5641_ = v_isSharedCheck_5709_;
goto v_resetjp_5639_;
}
else
{
lean_dec(v_snd_5606_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5709_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
lean_object* v_array_5642_; lean_object* v_start_5643_; lean_object* v_stop_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5649_; 
v_array_5642_ = lean_ctor_get(v_fst_5619_, 0);
v_start_5643_ = lean_ctor_get(v_fst_5619_, 1);
v_stop_5644_ = lean_ctor_get(v_fst_5619_, 2);
v___x_5645_ = lean_array_fget(v_array_5623_, v_start_5624_);
v___x_5646_ = lean_unsigned_to_nat(1u);
v___x_5647_ = lean_nat_add(v_start_5624_, v___x_5646_);
lean_dec(v_start_5624_);
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 1, v___x_5647_);
v___x_5649_ = v___x_5640_;
goto v_reusejp_5648_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_array_5623_);
lean_ctor_set(v_reuseFailAlloc_5708_, 1, v___x_5647_);
lean_ctor_set(v_reuseFailAlloc_5708_, 2, v_stop_5625_);
v___x_5649_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5648_;
}
v_reusejp_5648_:
{
uint8_t v___x_5650_; 
v___x_5650_ = lean_nat_dec_lt(v_start_5643_, v_stop_5644_);
if (v___x_5650_ == 0)
{
lean_object* v___x_5652_; 
lean_dec(v___x_5645_);
lean_dec(v_a_5595_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 1, v___x_5649_);
v___x_5652_ = v___x_5621_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_fst_5619_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v___x_5649_);
v___x_5652_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
lean_object* v___x_5654_; 
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 1, v___x_5652_);
v___x_5654_ = v___x_5617_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_fst_5615_);
lean_ctor_set(v_reuseFailAlloc_5661_, 1, v___x_5652_);
v___x_5654_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
lean_object* v___x_5656_; 
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 1, v___x_5654_);
v___x_5656_ = v___x_5613_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_fst_5611_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v___x_5654_);
v___x_5656_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5658_; 
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 1, v___x_5656_);
v___x_5658_ = v___x_5609_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_fst_5607_);
lean_ctor_set(v_reuseFailAlloc_5659_, 1, v___x_5656_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
return v___x_5658_;
}
}
}
}
}
else
{
lean_object* v___x_5664_; uint8_t v_isShared_5665_; uint8_t v_isSharedCheck_5704_; 
lean_inc(v_stop_5644_);
lean_inc(v_start_5643_);
lean_inc_ref(v_array_5642_);
v_isSharedCheck_5704_ = !lean_is_exclusive(v_fst_5619_);
if (v_isSharedCheck_5704_ == 0)
{
lean_object* v_unused_5705_; lean_object* v_unused_5706_; lean_object* v_unused_5707_; 
v_unused_5705_ = lean_ctor_get(v_fst_5619_, 2);
lean_dec(v_unused_5705_);
v_unused_5706_ = lean_ctor_get(v_fst_5619_, 1);
lean_dec(v_unused_5706_);
v_unused_5707_ = lean_ctor_get(v_fst_5619_, 0);
lean_dec(v_unused_5707_);
v___x_5664_ = v_fst_5619_;
v_isShared_5665_ = v_isSharedCheck_5704_;
goto v_resetjp_5663_;
}
else
{
lean_dec(v_fst_5619_);
v___x_5664_ = lean_box(0);
v_isShared_5665_ = v_isSharedCheck_5704_;
goto v_resetjp_5663_;
}
v_resetjp_5663_:
{
lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5669_; 
v___x_5666_ = lean_array_fget(v_array_5642_, v_start_5643_);
v___x_5667_ = lean_nat_add(v_start_5643_, v___x_5646_);
lean_dec(v_start_5643_);
if (v_isShared_5665_ == 0)
{
lean_ctor_set(v___x_5664_, 1, v___x_5667_);
v___x_5669_ = v___x_5664_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_array_5642_);
lean_ctor_set(v_reuseFailAlloc_5703_, 1, v___x_5667_);
lean_ctor_set(v_reuseFailAlloc_5703_, 2, v_stop_5644_);
v___x_5669_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
uint8_t v___x_5670_; 
v___x_5670_ = lean_unbox(v___x_5666_);
lean_dec(v___x_5666_);
if (v___x_5670_ == 0)
{
lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5676_; 
v___x_5671_ = lean_array_get_size(v_fst_5615_);
v___x_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5671_);
v___x_5673_ = lean_array_push(v_fst_5607_, v___x_5672_);
v___x_5674_ = lean_array_push(v_fst_5615_, v___x_5645_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 1, v___x_5649_);
lean_ctor_set(v___x_5621_, 0, v___x_5669_);
v___x_5676_ = v___x_5621_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v___x_5669_);
lean_ctor_set(v_reuseFailAlloc_5686_, 1, v___x_5649_);
v___x_5676_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
lean_object* v___x_5678_; 
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 1, v___x_5676_);
lean_ctor_set(v___x_5617_, 0, v___x_5674_);
v___x_5678_ = v___x_5617_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5685_; 
v_reuseFailAlloc_5685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5685_, 0, v___x_5674_);
lean_ctor_set(v_reuseFailAlloc_5685_, 1, v___x_5676_);
v___x_5678_ = v_reuseFailAlloc_5685_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
lean_object* v___x_5680_; 
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 1, v___x_5678_);
v___x_5680_ = v___x_5613_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5684_; 
v_reuseFailAlloc_5684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_fst_5611_);
lean_ctor_set(v_reuseFailAlloc_5684_, 1, v___x_5678_);
v___x_5680_ = v_reuseFailAlloc_5684_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
lean_object* v___x_5682_; 
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 1, v___x_5680_);
lean_ctor_set(v___x_5609_, 0, v___x_5673_);
v___x_5682_ = v___x_5609_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v___x_5673_);
lean_ctor_set(v_reuseFailAlloc_5683_, 1, v___x_5680_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
v_a_5598_ = v___x_5682_;
goto v___jp_5597_;
}
}
}
}
}
else
{
lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5692_; 
v___x_5687_ = lean_box(0);
v___x_5688_ = lean_array_push(v_fst_5607_, v___x_5687_);
v___x_5689_ = l_Lean_Expr_fvarId_x21(v___x_5645_);
lean_dec(v___x_5645_);
v___x_5690_ = lean_array_push(v_fst_5611_, v___x_5689_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set(v___x_5621_, 1, v___x_5649_);
lean_ctor_set(v___x_5621_, 0, v___x_5669_);
v___x_5692_ = v___x_5621_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5669_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v___x_5649_);
v___x_5692_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
lean_object* v___x_5694_; 
if (v_isShared_5618_ == 0)
{
lean_ctor_set(v___x_5617_, 1, v___x_5692_);
v___x_5694_ = v___x_5617_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_fst_5615_);
lean_ctor_set(v_reuseFailAlloc_5701_, 1, v___x_5692_);
v___x_5694_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
lean_object* v___x_5696_; 
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 1, v___x_5694_);
lean_ctor_set(v___x_5613_, 0, v___x_5690_);
v___x_5696_ = v___x_5613_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5690_);
lean_ctor_set(v_reuseFailAlloc_5700_, 1, v___x_5694_);
v___x_5696_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
lean_object* v___x_5698_; 
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 1, v___x_5696_);
lean_ctor_set(v___x_5609_, 0, v___x_5688_);
v___x_5698_ = v___x_5609_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v___x_5688_);
lean_ctor_set(v_reuseFailAlloc_5699_, 1, v___x_5696_);
v___x_5698_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
v_a_5598_ = v___x_5698_;
goto v___jp_5597_;
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
v___jp_5597_:
{
lean_object* v___x_5599_; lean_object* v___x_5600_; 
v___x_5599_ = lean_unsigned_to_nat(1u);
v___x_5600_ = lean_nat_add(v_a_5595_, v___x_5599_);
lean_dec(v_a_5595_);
v_a_5595_ = v___x_5600_;
v_b_5596_ = v_a_5598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5721_, lean_object* v_a_5722_, lean_object* v_b_5723_){
_start:
{
lean_object* v_res_5724_; 
v_res_5724_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5721_, v_a_5722_, v_b_5723_);
lean_dec(v_upperBound_5721_);
return v_res_5724_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5725_, size_t v_i_5726_, size_t v_stop_5727_){
_start:
{
uint8_t v___x_5728_; 
v___x_5728_ = lean_usize_dec_eq(v_i_5726_, v_stop_5727_);
if (v___x_5728_ == 0)
{
uint8_t v___x_5729_; lean_object* v___x_5730_; uint8_t v___x_5731_; 
v___x_5729_ = 1;
v___x_5730_ = lean_array_uget_borrowed(v_as_5725_, v_i_5726_);
v___x_5731_ = l_Lean_Expr_isFVar(v___x_5730_);
if (v___x_5731_ == 0)
{
return v___x_5729_;
}
else
{
if (v___x_5728_ == 0)
{
size_t v___x_5732_; size_t v___x_5733_; 
v___x_5732_ = ((size_t)1ULL);
v___x_5733_ = lean_usize_add(v_i_5726_, v___x_5732_);
v_i_5726_ = v___x_5733_;
goto _start;
}
else
{
return v___x_5729_;
}
}
}
else
{
uint8_t v___x_5735_; 
v___x_5735_ = 0;
return v___x_5735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5736_, lean_object* v_i_5737_, lean_object* v_stop_5738_){
_start:
{
size_t v_i_boxed_5739_; size_t v_stop_boxed_5740_; uint8_t v_res_5741_; lean_object* v_r_5742_; 
v_i_boxed_5739_ = lean_unbox_usize(v_i_5737_);
lean_dec(v_i_5737_);
v_stop_boxed_5740_ = lean_unbox_usize(v_stop_5738_);
lean_dec(v_stop_5738_);
v_res_5741_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5736_, v_i_boxed_5739_, v_stop_boxed_5740_);
lean_dec_ref(v_as_5736_);
v_r_5742_ = lean_box(v_res_5741_);
return v_r_5742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5743_, size_t v_sz_5744_, size_t v_i_5745_, lean_object* v_bs_5746_){
_start:
{
uint8_t v___x_5747_; 
v___x_5747_ = lean_usize_dec_lt(v_i_5745_, v_sz_5744_);
if (v___x_5747_ == 0)
{
return v_bs_5746_;
}
else
{
lean_object* v_v_5748_; lean_object* v___x_5749_; lean_object* v_bs_x27_5750_; lean_object* v___y_5752_; 
v_v_5748_ = lean_array_uget(v_bs_5746_, v_i_5745_);
v___x_5749_ = lean_unsigned_to_nat(0u);
v_bs_x27_5750_ = lean_array_uset(v_bs_5746_, v_i_5745_, v___x_5749_);
if (lean_obj_tag(v_v_5748_) == 0)
{
v___y_5752_ = v_v_5748_;
goto v___jp_5751_;
}
else
{
lean_object* v_val_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; 
v_val_5757_ = lean_ctor_get(v_v_5748_, 0);
lean_inc(v_val_5757_);
lean_dec_ref_known(v_v_5748_, 1);
v___x_5758_ = lean_box(0);
v___x_5759_ = lean_array_get_borrowed(v___x_5758_, v___x_5743_, v_val_5757_);
lean_dec(v_val_5757_);
lean_inc(v___x_5759_);
v___y_5752_ = v___x_5759_;
goto v___jp_5751_;
}
v___jp_5751_:
{
size_t v___x_5753_; size_t v___x_5754_; lean_object* v___x_5755_; 
v___x_5753_ = ((size_t)1ULL);
v___x_5754_ = lean_usize_add(v_i_5745_, v___x_5753_);
v___x_5755_ = lean_array_uset(v_bs_x27_5750_, v_i_5745_, v___y_5752_);
v_i_5745_ = v___x_5754_;
v_bs_5746_ = v___x_5755_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5760_, lean_object* v_sz_5761_, lean_object* v_i_5762_, lean_object* v_bs_5763_){
_start:
{
size_t v_sz_boxed_5764_; size_t v_i_boxed_5765_; lean_object* v_res_5766_; 
v_sz_boxed_5764_ = lean_unbox_usize(v_sz_5761_);
lean_dec(v_sz_5761_);
v_i_boxed_5765_ = lean_unbox_usize(v_i_5762_);
lean_dec(v_i_5762_);
v_res_5766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5760_, v_sz_boxed_5764_, v_i_boxed_5765_, v_bs_5763_);
lean_dec_ref(v___x_5760_);
return v_res_5766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5767_, size_t v_sz_5768_, size_t v_i_5769_, lean_object* v_bs_5770_){
_start:
{
uint8_t v___x_5771_; 
v___x_5771_ = lean_usize_dec_lt(v_i_5769_, v_sz_5768_);
if (v___x_5771_ == 0)
{
return v_bs_5770_;
}
else
{
lean_object* v_v_5772_; lean_object* v___x_5773_; lean_object* v_bs_x27_5774_; size_t v_sz_5775_; size_t v___x_5776_; lean_object* v___x_5777_; size_t v___x_5778_; size_t v___x_5779_; lean_object* v___x_5780_; 
v_v_5772_ = lean_array_uget(v_bs_5770_, v_i_5769_);
v___x_5773_ = lean_unsigned_to_nat(0u);
v_bs_x27_5774_ = lean_array_uset(v_bs_5770_, v_i_5769_, v___x_5773_);
v_sz_5775_ = lean_array_size(v_v_5772_);
v___x_5776_ = ((size_t)0ULL);
v___x_5777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5767_, v_sz_5775_, v___x_5776_, v_v_5772_);
v___x_5778_ = ((size_t)1ULL);
v___x_5779_ = lean_usize_add(v_i_5769_, v___x_5778_);
v___x_5780_ = lean_array_uset(v_bs_x27_5774_, v_i_5769_, v___x_5777_);
v_i_5769_ = v___x_5779_;
v_bs_5770_ = v___x_5780_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5782_, lean_object* v_sz_5783_, lean_object* v_i_5784_, lean_object* v_bs_5785_){
_start:
{
size_t v_sz_boxed_5786_; size_t v_i_boxed_5787_; lean_object* v_res_5788_; 
v_sz_boxed_5786_ = lean_unbox_usize(v_sz_5783_);
lean_dec(v_sz_5783_);
v_i_boxed_5787_ = lean_unbox_usize(v_i_5784_);
lean_dec(v_i_5784_);
v_res_5788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5782_, v_sz_boxed_5786_, v_i_boxed_5787_, v_bs_5785_);
lean_dec_ref(v___x_5782_);
return v_res_5788_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; 
v___x_5791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5792_ = lean_unsigned_to_nat(6u);
v___x_5793_ = lean_unsigned_to_nat(463u);
v___x_5794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5795_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5796_ = l_mkPanicMessageWithDecl(v___x_5795_, v___x_5794_, v___x_5793_, v___x_5792_, v___x_5791_);
return v___x_5796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5797_, lean_object* v_as_5798_, size_t v_sz_5799_, size_t v_i_5800_, lean_object* v_b_5801_){
_start:
{
lean_object* v_a_5803_; uint8_t v___x_5807_; 
v___x_5807_ = lean_usize_dec_lt(v_i_5800_, v_sz_5799_);
if (v___x_5807_ == 0)
{
return v_b_5801_;
}
else
{
lean_object* v_a_5808_; lean_object* v___x_5809_; uint8_t v_changed_5810_; 
v_a_5808_ = lean_array_uget_borrowed(v_as_5798_, v_i_5800_);
v___x_5809_ = lean_array_get_size(v___x_5797_);
v_changed_5810_ = lean_nat_dec_lt(v_a_5808_, v___x_5809_);
if (v_changed_5810_ == 0)
{
lean_object* v___x_5811_; lean_object* v___x_5812_; 
lean_dec_ref(v_b_5801_);
v___x_5811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5812_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5811_);
if (lean_obj_tag(v___x_5812_) == 0)
{
lean_object* v_a_5813_; 
v_a_5813_ = lean_ctor_get(v___x_5812_, 0);
lean_inc(v_a_5813_);
lean_dec_ref_known(v___x_5812_, 1);
return v_a_5813_;
}
else
{
lean_object* v_a_5814_; 
v_a_5814_ = lean_ctor_get(v___x_5812_, 0);
lean_inc(v_a_5814_);
lean_dec_ref_known(v___x_5812_, 1);
v_a_5803_ = v_a_5814_;
goto v___jp_5802_;
}
}
else
{
lean_object* v___x_5815_; lean_object* v___x_5816_; 
v___x_5815_ = lean_box(0);
v___x_5816_ = lean_array_get_borrowed(v___x_5815_, v___x_5797_, v_a_5808_);
if (lean_obj_tag(v___x_5816_) == 1)
{
lean_object* v_val_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; 
v_val_5817_ = lean_ctor_get(v___x_5816_, 0);
v___x_5818_ = lean_box(v_changed_5810_);
v___x_5819_ = lean_array_set(v_b_5801_, v_val_5817_, v___x_5818_);
v_a_5803_ = v___x_5819_;
goto v___jp_5802_;
}
else
{
v_a_5803_ = v_b_5801_;
goto v___jp_5802_;
}
}
}
v___jp_5802_:
{
size_t v___x_5804_; size_t v___x_5805_; 
v___x_5804_ = ((size_t)1ULL);
v___x_5805_ = lean_usize_add(v_i_5800_, v___x_5804_);
v_i_5800_ = v___x_5805_;
v_b_5801_ = v_a_5803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5820_, lean_object* v_as_5821_, lean_object* v_sz_5822_, lean_object* v_i_5823_, lean_object* v_b_5824_){
_start:
{
size_t v_sz_boxed_5825_; size_t v_i_boxed_5826_; lean_object* v_res_5827_; 
v_sz_boxed_5825_ = lean_unbox_usize(v_sz_5822_);
lean_dec(v_sz_5822_);
v_i_boxed_5826_ = lean_unbox_usize(v_i_5823_);
lean_dec(v_i_5823_);
v_res_5827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5820_, v_as_5821_, v_sz_boxed_5825_, v_i_boxed_5826_, v_b_5824_);
lean_dec_ref(v_as_5821_);
lean_dec_ref(v___x_5820_);
return v_res_5827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5828_, lean_object* v_a_5829_, lean_object* v_b_5830_){
_start:
{
uint8_t v___x_5831_; 
v___x_5831_ = lean_nat_dec_lt(v_a_5829_, v_upperBound_5828_);
if (v___x_5831_ == 0)
{
lean_dec(v_a_5829_);
return v_b_5830_;
}
else
{
lean_object* v_snd_5832_; lean_object* v_snd_5833_; lean_object* v_fst_5834_; lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5900_; 
v_snd_5832_ = lean_ctor_get(v_b_5830_, 1);
lean_inc(v_snd_5832_);
v_snd_5833_ = lean_ctor_get(v_snd_5832_, 1);
lean_inc(v_snd_5833_);
v_fst_5834_ = lean_ctor_get(v_b_5830_, 0);
v_isSharedCheck_5900_ = !lean_is_exclusive(v_b_5830_);
if (v_isSharedCheck_5900_ == 0)
{
lean_object* v_unused_5901_; 
v_unused_5901_ = lean_ctor_get(v_b_5830_, 1);
lean_dec(v_unused_5901_);
v___x_5836_ = v_b_5830_;
v_isShared_5837_ = v_isSharedCheck_5900_;
goto v_resetjp_5835_;
}
else
{
lean_inc(v_fst_5834_);
lean_dec(v_b_5830_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5900_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v_fst_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5898_; 
v_fst_5838_ = lean_ctor_get(v_snd_5832_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v_snd_5832_);
if (v_isSharedCheck_5898_ == 0)
{
lean_object* v_unused_5899_; 
v_unused_5899_ = lean_ctor_get(v_snd_5832_, 1);
lean_dec(v_unused_5899_);
v___x_5840_ = v_snd_5832_;
v_isShared_5841_ = v_isSharedCheck_5898_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_fst_5838_);
lean_dec(v_snd_5832_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5898_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v_array_5842_; lean_object* v_start_5843_; lean_object* v_stop_5844_; uint8_t v___x_5845_; 
v_array_5842_ = lean_ctor_get(v_snd_5833_, 0);
v_start_5843_ = lean_ctor_get(v_snd_5833_, 1);
v_stop_5844_ = lean_ctor_get(v_snd_5833_, 2);
v___x_5845_ = lean_nat_dec_lt(v_start_5843_, v_stop_5844_);
if (v___x_5845_ == 0)
{
lean_object* v___x_5847_; 
lean_dec(v_a_5829_);
if (v_isShared_5841_ == 0)
{
v___x_5847_ = v___x_5840_;
goto v_reusejp_5846_;
}
else
{
lean_object* v_reuseFailAlloc_5851_; 
v_reuseFailAlloc_5851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_fst_5838_);
lean_ctor_set(v_reuseFailAlloc_5851_, 1, v_snd_5833_);
v___x_5847_ = v_reuseFailAlloc_5851_;
goto v_reusejp_5846_;
}
v_reusejp_5846_:
{
lean_object* v___x_5849_; 
if (v_isShared_5837_ == 0)
{
lean_ctor_set(v___x_5836_, 1, v___x_5847_);
v___x_5849_ = v___x_5836_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_fst_5834_);
lean_ctor_set(v_reuseFailAlloc_5850_, 1, v___x_5847_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
return v___x_5849_;
}
}
}
else
{
lean_object* v___x_5853_; uint8_t v_isShared_5854_; uint8_t v_isSharedCheck_5894_; 
lean_inc(v_stop_5844_);
lean_inc(v_start_5843_);
lean_inc_ref(v_array_5842_);
v_isSharedCheck_5894_ = !lean_is_exclusive(v_snd_5833_);
if (v_isSharedCheck_5894_ == 0)
{
lean_object* v_unused_5895_; lean_object* v_unused_5896_; lean_object* v_unused_5897_; 
v_unused_5895_ = lean_ctor_get(v_snd_5833_, 2);
lean_dec(v_unused_5895_);
v_unused_5896_ = lean_ctor_get(v_snd_5833_, 1);
lean_dec(v_unused_5896_);
v_unused_5897_ = lean_ctor_get(v_snd_5833_, 0);
lean_dec(v_unused_5897_);
v___x_5853_ = v_snd_5833_;
v_isShared_5854_ = v_isSharedCheck_5894_;
goto v_resetjp_5852_;
}
else
{
lean_dec(v_snd_5833_);
v___x_5853_ = lean_box(0);
v_isShared_5854_ = v_isSharedCheck_5894_;
goto v_resetjp_5852_;
}
v_resetjp_5852_:
{
lean_object* v_array_5855_; lean_object* v_start_5856_; lean_object* v_stop_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5862_; 
v_array_5855_ = lean_ctor_get(v_fst_5838_, 0);
v_start_5856_ = lean_ctor_get(v_fst_5838_, 1);
v_stop_5857_ = lean_ctor_get(v_fst_5838_, 2);
v___x_5858_ = lean_array_fget(v_array_5842_, v_start_5843_);
v___x_5859_ = lean_unsigned_to_nat(1u);
v___x_5860_ = lean_nat_add(v_start_5843_, v___x_5859_);
lean_dec(v_start_5843_);
if (v_isShared_5854_ == 0)
{
lean_ctor_set(v___x_5853_, 1, v___x_5860_);
v___x_5862_ = v___x_5853_;
goto v_reusejp_5861_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_array_5842_);
lean_ctor_set(v_reuseFailAlloc_5893_, 1, v___x_5860_);
lean_ctor_set(v_reuseFailAlloc_5893_, 2, v_stop_5844_);
v___x_5862_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5861_;
}
v_reusejp_5861_:
{
uint8_t v___x_5863_; 
v___x_5863_ = lean_nat_dec_lt(v_start_5856_, v_stop_5857_);
if (v___x_5863_ == 0)
{
lean_object* v___x_5865_; 
lean_dec(v___x_5858_);
lean_dec(v_a_5829_);
if (v_isShared_5841_ == 0)
{
lean_ctor_set(v___x_5840_, 1, v___x_5862_);
v___x_5865_ = v___x_5840_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_fst_5838_);
lean_ctor_set(v_reuseFailAlloc_5869_, 1, v___x_5862_);
v___x_5865_ = v_reuseFailAlloc_5869_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
lean_object* v___x_5867_; 
if (v_isShared_5837_ == 0)
{
lean_ctor_set(v___x_5836_, 1, v___x_5865_);
v___x_5867_ = v___x_5836_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_fst_5834_);
lean_ctor_set(v_reuseFailAlloc_5868_, 1, v___x_5865_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
else
{
lean_object* v___x_5871_; uint8_t v_isShared_5872_; uint8_t v_isSharedCheck_5889_; 
lean_inc(v_stop_5857_);
lean_inc(v_start_5856_);
lean_inc_ref(v_array_5855_);
v_isSharedCheck_5889_ = !lean_is_exclusive(v_fst_5838_);
if (v_isSharedCheck_5889_ == 0)
{
lean_object* v_unused_5890_; lean_object* v_unused_5891_; lean_object* v_unused_5892_; 
v_unused_5890_ = lean_ctor_get(v_fst_5838_, 2);
lean_dec(v_unused_5890_);
v_unused_5891_ = lean_ctor_get(v_fst_5838_, 1);
lean_dec(v_unused_5891_);
v_unused_5892_ = lean_ctor_get(v_fst_5838_, 0);
lean_dec(v_unused_5892_);
v___x_5871_ = v_fst_5838_;
v_isShared_5872_ = v_isSharedCheck_5889_;
goto v_resetjp_5870_;
}
else
{
lean_dec(v_fst_5838_);
v___x_5871_ = lean_box(0);
v_isShared_5872_ = v_isSharedCheck_5889_;
goto v_resetjp_5870_;
}
v_resetjp_5870_:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5876_; 
v___x_5873_ = lean_array_fget(v_array_5855_, v_start_5856_);
v___x_5874_ = lean_nat_add(v_start_5856_, v___x_5859_);
lean_dec(v_start_5856_);
if (v_isShared_5872_ == 0)
{
lean_ctor_set(v___x_5871_, 1, v___x_5874_);
v___x_5876_ = v___x_5871_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5888_; 
v_reuseFailAlloc_5888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_array_5855_);
lean_ctor_set(v_reuseFailAlloc_5888_, 1, v___x_5874_);
lean_ctor_set(v_reuseFailAlloc_5888_, 2, v_stop_5857_);
v___x_5876_ = v_reuseFailAlloc_5888_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
size_t v_sz_5877_; size_t v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5881_; 
v_sz_5877_ = lean_array_size(v___x_5873_);
v___x_5878_ = ((size_t)0ULL);
v___x_5879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5858_, v___x_5873_, v_sz_5877_, v___x_5878_, v_fst_5834_);
lean_dec(v___x_5873_);
lean_dec(v___x_5858_);
if (v_isShared_5841_ == 0)
{
lean_ctor_set(v___x_5840_, 1, v___x_5862_);
lean_ctor_set(v___x_5840_, 0, v___x_5876_);
v___x_5881_ = v___x_5840_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5887_; 
v_reuseFailAlloc_5887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5887_, 0, v___x_5876_);
lean_ctor_set(v_reuseFailAlloc_5887_, 1, v___x_5862_);
v___x_5881_ = v_reuseFailAlloc_5887_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
lean_object* v___x_5883_; 
if (v_isShared_5837_ == 0)
{
lean_ctor_set(v___x_5836_, 1, v___x_5881_);
lean_ctor_set(v___x_5836_, 0, v___x_5879_);
v___x_5883_ = v___x_5836_;
goto v_reusejp_5882_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v___x_5879_);
lean_ctor_set(v_reuseFailAlloc_5886_, 1, v___x_5881_);
v___x_5883_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5882_;
}
v_reusejp_5882_:
{
lean_object* v___x_5884_; 
v___x_5884_ = lean_nat_add(v_a_5829_, v___x_5859_);
lean_dec(v_a_5829_);
v_a_5829_ = v___x_5884_;
v_b_5830_ = v___x_5883_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_5902_, lean_object* v_a_5903_, lean_object* v_b_5904_){
_start:
{
lean_object* v_res_5905_; 
v_res_5905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_5902_, v_a_5903_, v_b_5904_);
lean_dec(v_upperBound_5902_);
return v_res_5905_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; 
v___x_5907_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_5908_ = lean_unsigned_to_nat(2u);
v___x_5909_ = lean_unsigned_to_nat(457u);
v___x_5910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5911_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5912_ = l_mkPanicMessageWithDecl(v___x_5911_, v___x_5910_, v___x_5909_, v___x_5908_, v___x_5907_);
return v___x_5912_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5914_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_5915_ = lean_unsigned_to_nat(2u);
v___x_5916_ = lean_unsigned_to_nat(458u);
v___x_5917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5918_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5919_ = l_mkPanicMessageWithDecl(v___x_5918_, v___x_5917_, v___x_5916_, v___x_5915_, v___x_5914_);
return v___x_5919_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; 
v___x_5921_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_5922_ = lean_unsigned_to_nat(2u);
v___x_5923_ = lean_unsigned_to_nat(456u);
v___x_5924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5925_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5926_ = l_mkPanicMessageWithDecl(v___x_5925_, v___x_5924_, v___x_5923_, v___x_5922_, v___x_5921_);
return v___x_5926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_5927_, lean_object* v_xs_5928_, lean_object* v_toErase_5929_){
_start:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; uint8_t v___x_6015_; 
v___x_5930_ = lean_unsigned_to_nat(0u);
v___x_5931_ = lean_array_get_size(v_xs_5928_);
v___x_6015_ = lean_nat_dec_lt(v___x_5930_, v___x_5931_);
if (v___x_6015_ == 0)
{
goto v___jp_5932_;
}
else
{
if (v___x_6015_ == 0)
{
goto v___jp_5932_;
}
else
{
size_t v___x_6016_; size_t v___x_6017_; uint8_t v___x_6018_; 
v___x_6016_ = ((size_t)0ULL);
v___x_6017_ = lean_usize_of_nat(v___x_5931_);
v___x_6018_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_5928_, v___x_6016_, v___x_6017_);
if (v___x_6018_ == 0)
{
goto v___jp_5932_;
}
else
{
lean_object* v___x_6019_; lean_object* v___x_6020_; 
lean_dec_ref(v_toErase_5929_);
lean_dec_ref(v_xs_5928_);
lean_dec_ref(v_fixedParamPerms_5927_);
v___x_6019_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6020_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6019_);
return v___x_6020_;
}
}
}
v___jp_5932_:
{
lean_object* v_numFixed_5933_; lean_object* v_perms_5934_; lean_object* v_revDeps_5935_; uint8_t v___x_5936_; 
v_numFixed_5933_ = lean_ctor_get(v_fixedParamPerms_5927_, 0);
v_perms_5934_ = lean_ctor_get(v_fixedParamPerms_5927_, 1);
lean_inc_ref(v_perms_5934_);
v_revDeps_5935_ = lean_ctor_get(v_fixedParamPerms_5927_, 2);
lean_inc_ref(v_revDeps_5935_);
v___x_5936_ = lean_nat_dec_eq(v_numFixed_5933_, v___x_5931_);
if (v___x_5936_ == 0)
{
lean_object* v___x_5937_; lean_object* v___x_5938_; 
lean_dec_ref(v_revDeps_5935_);
lean_dec_ref(v_perms_5934_);
lean_dec_ref(v_toErase_5929_);
lean_dec_ref(v_xs_5928_);
lean_dec_ref(v_fixedParamPerms_5927_);
v___x_5937_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_5938_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_5937_);
return v___x_5938_;
}
else
{
lean_object* v___x_5939_; lean_object* v___x_5940_; uint8_t v_changed_5941_; 
v___x_5939_ = lean_array_get_size(v_toErase_5929_);
v___x_5940_ = lean_array_get_size(v_perms_5934_);
v_changed_5941_ = lean_nat_dec_eq(v___x_5939_, v___x_5940_);
if (v_changed_5941_ == 0)
{
lean_object* v___x_5942_; lean_object* v___x_5943_; 
lean_dec_ref(v_revDeps_5935_);
lean_dec_ref(v_perms_5934_);
lean_dec_ref(v_toErase_5929_);
lean_dec_ref(v_xs_5928_);
lean_dec_ref(v_fixedParamPerms_5927_);
v___x_5942_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_5943_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_5942_);
return v___x_5943_;
}
else
{
uint8_t v_changed_5944_; lean_object* v___x_5945_; lean_object* v_mask_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v_fst_5952_; lean_object* v___x_5954_; uint8_t v_isShared_5955_; uint8_t v_isSharedCheck_6013_; 
v_changed_5944_ = 0;
v___x_5945_ = lean_box(v_changed_5944_);
lean_inc(v_numFixed_5933_);
v_mask_5946_ = lean_mk_array(v_numFixed_5933_, v___x_5945_);
v___x_5947_ = l_Array_toSubarray___redArg(v_toErase_5929_, v___x_5930_, v___x_5939_);
lean_inc_ref(v_perms_5934_);
v___x_5948_ = l_Array_toSubarray___redArg(v_perms_5934_, v___x_5930_, v___x_5940_);
v___x_5949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5947_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v___x_5950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5950_, 0, v_mask_5946_);
lean_ctor_set(v___x_5950_, 1, v___x_5949_);
v___x_5951_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_5939_, v___x_5930_, v___x_5950_);
v_fst_5952_ = lean_ctor_get(v___x_5951_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v___x_5951_);
if (v_isSharedCheck_6013_ == 0)
{
lean_object* v_unused_6014_; 
v_unused_6014_ = lean_ctor_get(v___x_5951_, 1);
lean_dec(v_unused_6014_);
v___x_5954_ = v___x_5951_;
v_isShared_5955_ = v_isSharedCheck_6013_;
goto v_resetjp_5953_;
}
else
{
lean_inc(v_fst_5952_);
lean_dec(v___x_5951_);
v___x_5954_ = lean_box(0);
v_isShared_5955_ = v_isSharedCheck_6013_;
goto v_resetjp_5953_;
}
v_resetjp_5953_:
{
lean_object* v___x_5956_; lean_object* v___x_5958_; 
v___x_5956_ = lean_box(v_changed_5941_);
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5956_);
v___x_5958_ = v___x_5954_;
goto v_reusejp_5957_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v_fst_5952_);
lean_ctor_set(v_reuseFailAlloc_6012_, 1, v___x_5956_);
v___x_5958_ = v_reuseFailAlloc_6012_;
goto v_reusejp_5957_;
}
v_reusejp_5957_:
{
lean_object* v___x_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_6008_; 
v___x_5959_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5940_, v_perms_5934_, v_fixedParamPerms_5927_, v___x_5958_);
v_isSharedCheck_6008_ = !lean_is_exclusive(v_fixedParamPerms_5927_);
if (v_isSharedCheck_6008_ == 0)
{
lean_object* v_unused_6009_; lean_object* v_unused_6010_; lean_object* v_unused_6011_; 
v_unused_6009_ = lean_ctor_get(v_fixedParamPerms_5927_, 2);
lean_dec(v_unused_6009_);
v_unused_6010_ = lean_ctor_get(v_fixedParamPerms_5927_, 1);
lean_dec(v_unused_6010_);
v_unused_6011_ = lean_ctor_get(v_fixedParamPerms_5927_, 0);
lean_dec(v_unused_6011_);
v___x_5961_ = v_fixedParamPerms_5927_;
v_isShared_5962_ = v_isSharedCheck_6008_;
goto v_resetjp_5960_;
}
else
{
lean_dec(v_fixedParamPerms_5927_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_6008_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v_fst_5963_; lean_object* v___x_5965_; uint8_t v_isShared_5966_; uint8_t v_isSharedCheck_6006_; 
v_fst_5963_ = lean_ctor_get(v___x_5959_, 0);
v_isSharedCheck_6006_ = !lean_is_exclusive(v___x_5959_);
if (v_isSharedCheck_6006_ == 0)
{
lean_object* v_unused_6007_; 
v_unused_6007_ = lean_ctor_get(v___x_5959_, 1);
lean_dec(v_unused_6007_);
v___x_5965_ = v___x_5959_;
v_isShared_5966_ = v_isSharedCheck_6006_;
goto v_resetjp_5964_;
}
else
{
lean_inc(v_fst_5963_);
lean_dec(v___x_5959_);
v___x_5965_ = lean_box(0);
v_isShared_5966_ = v_isSharedCheck_6006_;
goto v_resetjp_5964_;
}
v_resetjp_5964_:
{
lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5972_; 
v___x_5967_ = lean_array_get_size(v_fst_5963_);
v___x_5968_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_5969_ = l_Array_toSubarray___redArg(v_fst_5963_, v___x_5930_, v___x_5967_);
v___x_5970_ = l_Array_toSubarray___redArg(v_xs_5928_, v___x_5930_, v___x_5931_);
if (v_isShared_5966_ == 0)
{
lean_ctor_set(v___x_5965_, 1, v___x_5970_);
lean_ctor_set(v___x_5965_, 0, v___x_5969_);
v___x_5972_ = v___x_5965_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_6005_; 
v_reuseFailAlloc_6005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6005_, 0, v___x_5969_);
lean_ctor_set(v_reuseFailAlloc_6005_, 1, v___x_5970_);
v___x_5972_ = v_reuseFailAlloc_6005_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v_snd_5977_; lean_object* v_snd_5978_; lean_object* v_fst_5979_; lean_object* v_fst_5980_; lean_object* v___x_5982_; uint8_t v_isShared_5983_; uint8_t v_isSharedCheck_6003_; 
v___x_5973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5968_);
lean_ctor_set(v___x_5973_, 1, v___x_5972_);
v___x_5974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5968_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5968_);
lean_ctor_set(v___x_5975_, 1, v___x_5974_);
v___x_5976_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_5967_, v___x_5930_, v___x_5975_);
v_snd_5977_ = lean_ctor_get(v___x_5976_, 1);
lean_inc(v_snd_5977_);
v_snd_5978_ = lean_ctor_get(v_snd_5977_, 1);
lean_inc(v_snd_5978_);
v_fst_5979_ = lean_ctor_get(v___x_5976_, 0);
lean_inc(v_fst_5979_);
lean_dec_ref(v___x_5976_);
v_fst_5980_ = lean_ctor_get(v_snd_5977_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v_snd_5977_);
if (v_isSharedCheck_6003_ == 0)
{
lean_object* v_unused_6004_; 
v_unused_6004_ = lean_ctor_get(v_snd_5977_, 1);
lean_dec(v_unused_6004_);
v___x_5982_ = v_snd_5977_;
v_isShared_5983_ = v_isSharedCheck_6003_;
goto v_resetjp_5981_;
}
else
{
lean_inc(v_fst_5980_);
lean_dec(v_snd_5977_);
v___x_5982_ = lean_box(0);
v_isShared_5983_ = v_isSharedCheck_6003_;
goto v_resetjp_5981_;
}
v_resetjp_5981_:
{
lean_object* v_fst_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_6001_; 
v_fst_5984_ = lean_ctor_get(v_snd_5978_, 0);
v_isSharedCheck_6001_ = !lean_is_exclusive(v_snd_5978_);
if (v_isSharedCheck_6001_ == 0)
{
lean_object* v_unused_6002_; 
v_unused_6002_ = lean_ctor_get(v_snd_5978_, 1);
lean_dec(v_unused_6002_);
v___x_5986_ = v_snd_5978_;
v_isShared_5987_ = v_isSharedCheck_6001_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_fst_5984_);
lean_dec(v_snd_5978_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_6001_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5988_; size_t v_sz_5989_; size_t v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5993_; 
v___x_5988_ = lean_array_get_size(v_fst_5984_);
v_sz_5989_ = lean_array_size(v_perms_5934_);
v___x_5990_ = ((size_t)0ULL);
v___x_5991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_5979_, v_sz_5989_, v___x_5990_, v_perms_5934_);
lean_dec(v_fst_5979_);
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 1, v___x_5991_);
lean_ctor_set(v___x_5961_, 0, v___x_5988_);
v___x_5993_ = v___x_5961_;
goto v_reusejp_5992_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v___x_5988_);
lean_ctor_set(v_reuseFailAlloc_6000_, 1, v___x_5991_);
lean_ctor_set(v_reuseFailAlloc_6000_, 2, v_revDeps_5935_);
v___x_5993_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5992_;
}
v_reusejp_5992_:
{
lean_object* v___x_5995_; 
if (v_isShared_5987_ == 0)
{
lean_ctor_set(v___x_5986_, 1, v_fst_5980_);
v___x_5995_ = v___x_5986_;
goto v_reusejp_5994_;
}
else
{
lean_object* v_reuseFailAlloc_5999_; 
v_reuseFailAlloc_5999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_fst_5984_);
lean_ctor_set(v_reuseFailAlloc_5999_, 1, v_fst_5980_);
v___x_5995_ = v_reuseFailAlloc_5999_;
goto v_reusejp_5994_;
}
v_reusejp_5994_:
{
lean_object* v___x_5997_; 
if (v_isShared_5983_ == 0)
{
lean_ctor_set(v___x_5982_, 1, v___x_5995_);
lean_ctor_set(v___x_5982_, 0, v___x_5993_);
v___x_5997_ = v___x_5982_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_5998_; 
v_reuseFailAlloc_5998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5998_, 0, v___x_5993_);
lean_ctor_set(v_reuseFailAlloc_5998_, 1, v___x_5995_);
v___x_5997_ = v_reuseFailAlloc_5998_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
return v___x_5997_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6021_, lean_object* v___x_6022_, lean_object* v_fixedParamPerms_6023_, lean_object* v_next_6024_, lean_object* v_inst_6025_, lean_object* v_R_6026_, lean_object* v_a_6027_, lean_object* v_b_6028_, lean_object* v_c_6029_){
_start:
{
lean_object* v___x_6030_; 
v___x_6030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6021_, v___x_6022_, v_fixedParamPerms_6023_, v_next_6024_, v_a_6027_, v_b_6028_);
return v___x_6030_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6031_, lean_object* v___x_6032_, lean_object* v_fixedParamPerms_6033_, lean_object* v_next_6034_, lean_object* v_inst_6035_, lean_object* v_R_6036_, lean_object* v_a_6037_, lean_object* v_b_6038_, lean_object* v_c_6039_){
_start:
{
lean_object* v_res_6040_; 
v_res_6040_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6031_, v___x_6032_, v_fixedParamPerms_6033_, v_next_6034_, v_inst_6035_, v_R_6036_, v_a_6037_, v_b_6038_, v_c_6039_);
lean_dec(v_next_6034_);
lean_dec_ref(v_fixedParamPerms_6033_);
lean_dec_ref(v___x_6032_);
lean_dec(v_upperBound_6031_);
return v_res_6040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6041_, lean_object* v___x_6042_, lean_object* v_fixedParamPerms_6043_, lean_object* v_inst_6044_, lean_object* v_R_6045_, lean_object* v_a_6046_, lean_object* v_b_6047_, lean_object* v_c_6048_){
_start:
{
lean_object* v___x_6049_; 
v___x_6049_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6041_, v___x_6042_, v_fixedParamPerms_6043_, v_a_6046_, v_b_6047_);
return v___x_6049_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6050_, lean_object* v___x_6051_, lean_object* v_fixedParamPerms_6052_, lean_object* v_inst_6053_, lean_object* v_R_6054_, lean_object* v_a_6055_, lean_object* v_b_6056_, lean_object* v_c_6057_){
_start:
{
lean_object* v_res_6058_; 
v_res_6058_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6050_, v___x_6051_, v_fixedParamPerms_6052_, v_inst_6053_, v_R_6054_, v_a_6055_, v_b_6056_, v_c_6057_);
lean_dec_ref(v_fixedParamPerms_6052_);
lean_dec_ref(v___x_6051_);
lean_dec(v_upperBound_6050_);
return v_res_6058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6059_, lean_object* v___x_6060_, lean_object* v_fixedParamPerms_6061_, lean_object* v_inst_6062_, lean_object* v_a_6063_){
_start:
{
lean_object* v___x_6064_; 
v___x_6064_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6059_, v___x_6060_, v_fixedParamPerms_6061_, v_a_6063_);
return v___x_6064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6065_, lean_object* v___x_6066_, lean_object* v_fixedParamPerms_6067_, lean_object* v_inst_6068_, lean_object* v_a_6069_){
_start:
{
lean_object* v_res_6070_; 
v_res_6070_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6065_, v___x_6066_, v_fixedParamPerms_6067_, v_inst_6068_, v_a_6069_);
lean_dec_ref(v_fixedParamPerms_6067_);
lean_dec_ref(v___x_6066_);
lean_dec(v___x_6065_);
return v_res_6070_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6071_, lean_object* v_inst_6072_, lean_object* v_R_6073_, lean_object* v_a_6074_, lean_object* v_b_6075_, lean_object* v_c_6076_){
_start:
{
lean_object* v___x_6077_; 
v___x_6077_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6071_, v_a_6074_, v_b_6075_);
return v___x_6077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6078_, lean_object* v_inst_6079_, lean_object* v_R_6080_, lean_object* v_a_6081_, lean_object* v_b_6082_, lean_object* v_c_6083_){
_start:
{
lean_object* v_res_6084_; 
v_res_6084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6078_, v_inst_6079_, v_R_6080_, v_a_6081_, v_b_6082_, v_c_6083_);
lean_dec(v_upperBound_6078_);
return v_res_6084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6085_, lean_object* v_inst_6086_, lean_object* v_R_6087_, lean_object* v_a_6088_, lean_object* v_b_6089_, lean_object* v_c_6090_){
_start:
{
lean_object* v___x_6091_; 
v___x_6091_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6085_, v_a_6088_, v_b_6089_);
return v___x_6091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6092_, lean_object* v_inst_6093_, lean_object* v_R_6094_, lean_object* v_a_6095_, lean_object* v_b_6096_, lean_object* v_c_6097_){
_start:
{
lean_object* v_res_6098_; 
v_res_6098_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6092_, v_inst_6093_, v_R_6094_, v_a_6095_, v_b_6096_, v_c_6097_);
lean_dec(v_upperBound_6092_);
return v_res_6098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6156_; uint8_t v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; 
v___x_6156_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6157_ = 0;
v___x_6158_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6159_ = l_Lean_registerTraceClass(v___x_6156_, v___x_6157_, v___x_6158_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6160_){
_start:
{
lean_object* v_res_6161_; 
v_res_6161_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6161_;
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
