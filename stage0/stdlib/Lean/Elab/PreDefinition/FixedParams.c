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
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
lean_object* v___f_1009_; lean_object* v___x_27166__overap_1010_; lean_object* v___x_1011_; 
v___f_1009_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_27166__overap_1010_ = lean_panic_fn_borrowed(v___f_1009_, v_msg_1003_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
v___x_1011_ = lean_apply_5(v___x_27166__overap_1010_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, lean_box(0));
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
lean_object* v___x_1082_; lean_object* v_env_1083_; lean_object* v___x_1084_; lean_object* v_toCold_1085_; lean_object* v_mctx_1086_; lean_object* v_lctx_1087_; lean_object* v_options_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1082_ = lean_st_ref_get(v___y_1080_);
v_env_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc_ref(v_env_1083_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_st_ref_get(v___y_1078_);
v_toCold_1085_ = lean_ctor_get(v___y_1079_, 0);
v_mctx_1086_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_ref(v_mctx_1086_);
lean_dec(v___x_1084_);
v_lctx_1087_ = lean_ctor_get(v___y_1077_, 2);
v_options_1088_ = lean_ctor_get(v_toCold_1085_, 2);
lean_inc_ref(v_options_1088_);
lean_inc_ref(v_lctx_1087_);
v___x_1089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1089_, 0, v_env_1083_);
lean_ctor_set(v___x_1089_, 1, v_mctx_1086_);
lean_ctor_set(v___x_1089_, 2, v_lctx_1087_);
lean_ctor_set(v___x_1089_, 3, v_options_1088_);
v___x_1090_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_msgData_1076_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2___boxed(lean_object* v_msgData_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msgData_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
return v_res_1098_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1099_; double v___x_1100_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_float_of_nat(v___x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object* v_cls_1104_, lean_object* v_msg_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_ref_1111_; lean_object* v___x_1112_; lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1157_; 
v_ref_1111_ = lean_ctor_get(v___y_1108_, 2);
v___x_1112_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1157_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1157_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v_traceState_1118_; lean_object* v_env_1119_; lean_object* v_nextMacroScope_1120_; lean_object* v_ngen_1121_; lean_object* v_auxDeclNGen_1122_; lean_object* v_cache_1123_; lean_object* v_messages_1124_; lean_object* v_infoState_1125_; lean_object* v_snapshotTasks_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1156_; 
v___x_1117_ = lean_st_ref_take(v___y_1109_);
v_traceState_1118_ = lean_ctor_get(v___x_1117_, 4);
v_env_1119_ = lean_ctor_get(v___x_1117_, 0);
v_nextMacroScope_1120_ = lean_ctor_get(v___x_1117_, 1);
v_ngen_1121_ = lean_ctor_get(v___x_1117_, 2);
v_auxDeclNGen_1122_ = lean_ctor_get(v___x_1117_, 3);
v_cache_1123_ = lean_ctor_get(v___x_1117_, 5);
v_messages_1124_ = lean_ctor_get(v___x_1117_, 6);
v_infoState_1125_ = lean_ctor_get(v___x_1117_, 7);
v_snapshotTasks_1126_ = lean_ctor_get(v___x_1117_, 8);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1156_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snapshotTasks_1126_);
lean_inc(v_infoState_1125_);
lean_inc(v_messages_1124_);
lean_inc(v_cache_1123_);
lean_inc(v_traceState_1118_);
lean_inc(v_auxDeclNGen_1122_);
lean_inc(v_ngen_1121_);
lean_inc(v_nextMacroScope_1120_);
lean_inc(v_env_1119_);
lean_dec(v___x_1117_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1156_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint64_t v_tid_1130_; lean_object* v_traces_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_tid_1130_ = lean_ctor_get_uint64(v_traceState_1118_, sizeof(void*)*1);
v_traces_1131_ = lean_ctor_get(v_traceState_1118_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_traceState_1118_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1133_ = v_traceState_1118_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_traces_1131_);
lean_dec(v_traceState_1118_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; double v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_1137_ = 0;
v___x_1138_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_1139_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1139_, 0, v_cls_1104_);
lean_ctor_set(v___x_1139_, 1, v___x_1135_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
lean_ctor_set_float(v___x_1139_, sizeof(void*)*3, v___x_1136_);
lean_ctor_set_float(v___x_1139_, sizeof(void*)*3 + 8, v___x_1136_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*3 + 16, v___x_1137_);
v___x_1140_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_1141_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v_a_1113_);
lean_ctor_set(v___x_1141_, 2, v___x_1140_);
lean_inc(v_ref_1111_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_ref_1111_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_PersistentArray_push___redArg(v_traces_1131_, v___x_1142_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1143_);
v___x_1145_ = v___x_1133_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1143_);
lean_ctor_set_uint64(v_reuseFailAlloc_1154_, sizeof(void*)*1, v_tid_1130_);
v___x_1145_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v___x_1145_);
v___x_1147_ = v___x_1128_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_env_1119_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_nextMacroScope_1120_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_ngen_1121_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_auxDeclNGen_1122_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1153_, 5, v_cache_1123_);
lean_ctor_set(v_reuseFailAlloc_1153_, 6, v_messages_1124_);
lean_ctor_set(v_reuseFailAlloc_1153_, 7, v_infoState_1125_);
lean_ctor_set(v_reuseFailAlloc_1153_, 8, v_snapshotTasks_1126_);
v___x_1147_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1148_ = lean_st_ref_put(v___y_1109_, v___x_1147_);
v___x_1149_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1149_);
v___x_1151_ = v___x_1115_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_1158_, lean_object* v_msg_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_1158_, v_msg_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object* v_00_u03b1_1166_, lean_object* v_x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_apply_1(v_x_1167_, lean_box(0));
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object* v_00_u03b1_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(v_00_u03b1_1175_, v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
if (lean_obj_tag(v_x_1184_) == 0)
{
return v_x_1183_;
}
else
{
lean_object* v_key_1185_; lean_object* v_value_1186_; lean_object* v_tail_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1210_; 
v_key_1185_ = lean_ctor_get(v_x_1184_, 0);
v_value_1186_ = lean_ctor_get(v_x_1184_, 1);
v_tail_1187_ = lean_ctor_get(v_x_1184_, 2);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1184_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1189_ = v_x_1184_;
v_isShared_1190_ = v_isSharedCheck_1210_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_tail_1187_);
lean_inc(v_value_1186_);
lean_inc(v_key_1185_);
lean_dec(v_x_1184_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1210_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; uint64_t v___x_1192_; uint64_t v___x_1193_; uint64_t v___x_1194_; uint64_t v_fold_1195_; uint64_t v___x_1196_; uint64_t v___x_1197_; uint64_t v___x_1198_; size_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1191_ = lean_array_get_size(v_x_1183_);
v___x_1192_ = l_Lean_ExprStructEq_hash(v_key_1185_);
v___x_1193_ = 32ULL;
v___x_1194_ = lean_uint64_shift_right(v___x_1192_, v___x_1193_);
v_fold_1195_ = lean_uint64_xor(v___x_1192_, v___x_1194_);
v___x_1196_ = 16ULL;
v___x_1197_ = lean_uint64_shift_right(v_fold_1195_, v___x_1196_);
v___x_1198_ = lean_uint64_xor(v_fold_1195_, v___x_1197_);
v___x_1199_ = lean_uint64_to_usize(v___x_1198_);
v___x_1200_ = lean_usize_of_nat(v___x_1191_);
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_sub(v___x_1200_, v___x_1201_);
v___x_1203_ = lean_usize_land(v___x_1199_, v___x_1202_);
v___x_1204_ = lean_array_uget_borrowed(v_x_1183_, v___x_1203_);
lean_inc(v___x_1204_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 2, v___x_1204_);
v___x_1206_ = v___x_1189_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_key_1185_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_value_1186_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_array_uset(v_x_1183_, v___x_1203_, v___x_1206_);
v_x_1183_ = v___x_1207_;
v_x_1184_ = v_tail_1187_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object* v_i_1211_, lean_object* v_source_1212_, lean_object* v_target_1213_){
_start:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_array_get_size(v_source_1212_);
v___x_1215_ = lean_nat_dec_lt(v_i_1211_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_dec_ref(v_source_1212_);
lean_dec(v_i_1211_);
return v_target_1213_;
}
else
{
lean_object* v_es_1216_; lean_object* v___x_1217_; lean_object* v_source_1218_; lean_object* v_target_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_es_1216_ = lean_array_fget(v_source_1212_, v_i_1211_);
v___x_1217_ = lean_box(0);
v_source_1218_ = lean_array_fset(v_source_1212_, v_i_1211_, v___x_1217_);
v_target_1219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_target_1213_, v_es_1216_);
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_add(v_i_1211_, v___x_1220_);
lean_dec(v_i_1211_);
v_i_1211_ = v___x_1221_;
v_source_1212_ = v_source_1218_;
v_target_1213_ = v_target_1219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object* v_data_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_nbuckets_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1224_ = lean_array_get_size(v_data_1223_);
v___x_1225_ = lean_unsigned_to_nat(2u);
v_nbuckets_1226_ = lean_nat_mul(v___x_1224_, v___x_1225_);
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_mk_array(v_nbuckets_1226_, v___x_1228_);
v___x_1230_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1227_, v_data_1223_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object* v_a_1231_, lean_object* v_b_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
lean_dec(v_b_1232_);
lean_dec_ref(v_a_1231_);
return v_x_1233_;
}
else
{
lean_object* v_key_1234_; lean_object* v_value_1235_; lean_object* v_tail_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1248_; 
v_key_1234_ = lean_ctor_get(v_x_1233_, 0);
v_value_1235_ = lean_ctor_get(v_x_1233_, 1);
v_tail_1236_ = lean_ctor_get(v_x_1233_, 2);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1233_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1238_ = v_x_1233_;
v_isShared_1239_ = v_isSharedCheck_1248_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_tail_1236_);
lean_inc(v_value_1235_);
lean_inc(v_key_1234_);
lean_dec(v_x_1233_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1248_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
uint8_t v___x_1240_; 
v___x_1240_ = l_Lean_ExprStructEq_beq(v_key_1234_, v_a_1231_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1231_, v_b_1232_, v_tail_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 2, v___x_1241_);
v___x_1243_ = v___x_1238_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_key_1234_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_value_1235_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
else
{
lean_object* v___x_1246_; 
lean_dec(v_value_1235_);
lean_dec(v_key_1234_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v_b_1232_);
lean_ctor_set(v___x_1238_, 0, v_a_1231_);
v___x_1246_ = v___x_1238_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1231_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_b_1232_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_tail_1236_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_a_1249_, lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
uint8_t v___x_1251_; 
v___x_1251_ = 0;
return v___x_1251_;
}
else
{
lean_object* v_key_1252_; lean_object* v_tail_1253_; uint8_t v___x_1254_; 
v_key_1252_ = lean_ctor_get(v_x_1250_, 0);
v_tail_1253_ = lean_ctor_get(v_x_1250_, 2);
v___x_1254_ = l_Lean_ExprStructEq_beq(v_key_1252_, v_a_1249_);
if (v___x_1254_ == 0)
{
v_x_1250_ = v_tail_1253_;
goto _start;
}
else
{
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_a_1256_, lean_object* v_x_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1256_, v_x_1257_);
lean_dec(v_x_1257_);
lean_dec_ref(v_a_1256_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1260_, lean_object* v_a_1261_, lean_object* v_b_1262_){
_start:
{
lean_object* v_size_1263_; lean_object* v_buckets_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1307_; 
v_size_1263_ = lean_ctor_get(v_m_1260_, 0);
v_buckets_1264_ = lean_ctor_get(v_m_1260_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_m_1260_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1266_ = v_m_1260_;
v_isShared_1267_ = v_isSharedCheck_1307_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_buckets_1264_);
lean_inc(v_size_1263_);
lean_dec(v_m_1260_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1307_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v_fold_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; uint64_t v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; lean_object* v_bkt_1281_; uint8_t v___x_1282_; 
v___x_1268_ = lean_array_get_size(v_buckets_1264_);
v___x_1269_ = l_Lean_ExprStructEq_hash(v_a_1261_);
v___x_1270_ = 32ULL;
v___x_1271_ = lean_uint64_shift_right(v___x_1269_, v___x_1270_);
v_fold_1272_ = lean_uint64_xor(v___x_1269_, v___x_1271_);
v___x_1273_ = 16ULL;
v___x_1274_ = lean_uint64_shift_right(v_fold_1272_, v___x_1273_);
v___x_1275_ = lean_uint64_xor(v_fold_1272_, v___x_1274_);
v___x_1276_ = lean_uint64_to_usize(v___x_1275_);
v___x_1277_ = lean_usize_of_nat(v___x_1268_);
v___x_1278_ = ((size_t)1ULL);
v___x_1279_ = lean_usize_sub(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_usize_land(v___x_1276_, v___x_1279_);
v_bkt_1281_ = lean_array_uget_borrowed(v_buckets_1264_, v___x_1280_);
v___x_1282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1261_, v_bkt_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v_size_x27_1284_; lean_object* v___x_1285_; lean_object* v_buckets_x27_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1283_ = lean_unsigned_to_nat(1u);
v_size_x27_1284_ = lean_nat_add(v_size_1263_, v___x_1283_);
lean_dec(v_size_1263_);
lean_inc(v_bkt_1281_);
v___x_1285_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1285_, 0, v_a_1261_);
lean_ctor_set(v___x_1285_, 1, v_b_1262_);
lean_ctor_set(v___x_1285_, 2, v_bkt_1281_);
v_buckets_x27_1286_ = lean_array_uset(v_buckets_1264_, v___x_1280_, v___x_1285_);
v___x_1287_ = lean_unsigned_to_nat(4u);
v___x_1288_ = lean_nat_mul(v_size_x27_1284_, v___x_1287_);
v___x_1289_ = lean_unsigned_to_nat(3u);
v___x_1290_ = lean_nat_div(v___x_1288_, v___x_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_array_get_size(v_buckets_x27_1286_);
v___x_1292_ = lean_nat_dec_le(v___x_1290_, v___x_1291_);
lean_dec(v___x_1290_);
if (v___x_1292_ == 0)
{
lean_object* v_val_1293_; lean_object* v___x_1295_; 
v_val_1293_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_buckets_x27_1286_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_val_1293_);
lean_ctor_set(v___x_1266_, 0, v_size_x27_1284_);
v___x_1295_ = v___x_1266_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_size_x27_1284_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_val_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
else
{
lean_object* v___x_1298_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_buckets_x27_1286_);
lean_ctor_set(v___x_1266_, 0, v_size_x27_1284_);
v___x_1298_ = v___x_1266_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_size_x27_1284_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_buckets_x27_1286_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v___x_1300_; lean_object* v_buckets_x27_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_inc(v_bkt_1281_);
v___x_1300_ = lean_box(0);
v_buckets_x27_1301_ = lean_array_uset(v_buckets_1264_, v___x_1280_, v___x_1300_);
v___x_1302_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1261_, v_b_1262_, v_bkt_1281_);
v___x_1303_ = lean_array_uset(v_buckets_x27_1301_, v___x_1280_, v___x_1302_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1303_);
v___x_1305_ = v___x_1266_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_size_1263_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1308_, lean_object* v_e_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = lean_st_ref_take(v_a_1308_);
v___x_1313_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1312_, v_e_1309_, v_a_1310_);
v___x_1314_ = lean_st_ref_put(v_a_1308_, v___x_1313_);
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1316_, lean_object* v_e_1317_, lean_object* v_a_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1316_, v_e_1317_, v_a_1318_);
lean_dec(v_a_1316_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1321_, lean_object* v___y_1322_, lean_object* v_b_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1322_);
v___x_1329_ = lean_apply_7(v_k_1321_, v_b_1323_, v___y_1322_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, lean_box(0));
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1330_, lean_object* v___y_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1330_, v___y_1331_, v_b_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1331_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1339_, uint8_t v_bi_1340_, lean_object* v_type_1341_, lean_object* v_k_1342_, uint8_t v_kind_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___f_1350_; lean_object* v___x_1351_; 
lean_inc(v___y_1344_);
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1350_, 0, v_k_1342_);
lean_closure_set(v___f_1350_, 1, v___y_1344_);
v___x_1351_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1339_, v_bi_1340_, v_type_1341_, v___f_1350_, v_kind_1343_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1351_) == 0)
{
return v___x_1351_;
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1360_, lean_object* v_bi_1361_, lean_object* v_type_1362_, lean_object* v_k_1363_, lean_object* v_kind_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v_bi_boxed_1371_; uint8_t v_kind_boxed_1372_; lean_object* v_res_1373_; 
v_bi_boxed_1371_ = lean_unbox(v_bi_1361_);
v_kind_boxed_1372_ = lean_unbox(v_kind_1364_);
v_res_1373_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1360_, v_bi_boxed_1371_, v_type_1362_, v_k_1363_, v_kind_boxed_1372_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object* v___x_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1374_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object* v___x_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1388_, lean_object* v_type_1389_, lean_object* v_val_1390_, lean_object* v_k_1391_, uint8_t v_nondep_1392_, uint8_t v_kind_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___f_1400_; lean_object* v___x_1401_; 
lean_inc(v___y_1394_);
v___f_1400_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1400_, 0, v_k_1391_);
lean_closure_set(v___f_1400_, 1, v___y_1394_);
v___x_1401_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1388_, v_type_1389_, v_val_1390_, v___f_1400_, v_nondep_1392_, v_kind_1393_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1401_) == 0)
{
return v___x_1401_;
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1410_, lean_object* v_type_1411_, lean_object* v_val_1412_, lean_object* v_k_1413_, lean_object* v_nondep_1414_, lean_object* v_kind_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v_nondep_boxed_1422_; uint8_t v_kind_boxed_1423_; lean_object* v_res_1424_; 
v_nondep_boxed_1422_ = lean_unbox(v_nondep_1414_);
v_kind_boxed_1423_ = lean_unbox(v_kind_1415_);
v_res_1424_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1410_, v_type_1411_, v_val_1412_, v_k_1413_, v_nondep_boxed_1422_, v_kind_boxed_1423_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = lean_apply_1(v_x_1426_, lean_box(0));
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1434_, v_x_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1441_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = l_Lean_maxRecDepthErrorMessage;
v___x_1448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1450_ = l_Lean_MessageData_ofFormat(v___x_1449_);
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1452_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1453_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v___x_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_ref_1454_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___y_1470_; lean_object* v_toCold_1479_; lean_object* v_currRecDepth_1480_; lean_object* v_ref_1481_; uint8_t v_diag_1482_; uint8_t v_suppressElabErrors_1483_; lean_object* v_maxRecDepth_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v_toCold_1479_ = lean_ctor_get(v___y_1466_, 0);
v_currRecDepth_1480_ = lean_ctor_get(v___y_1466_, 1);
v_ref_1481_ = lean_ctor_get(v___y_1466_, 2);
v_diag_1482_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*3);
v_suppressElabErrors_1483_ = lean_ctor_get_uint8(v___y_1466_, sizeof(void*)*3 + 1);
v_maxRecDepth_1489_ = lean_ctor_get(v_toCold_1479_, 3);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = lean_nat_dec_eq(v_maxRecDepth_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_nat_dec_eq(v_currRecDepth_1480_, v_maxRecDepth_1489_);
if (v___x_1492_ == 0)
{
goto v___jp_1484_;
}
else
{
lean_object* v___x_1493_; 
lean_dec_ref(v_x_1462_);
lean_inc(v_ref_1481_);
v___x_1493_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1481_);
v___y_1470_ = v___x_1493_;
goto v___jp_1469_;
}
}
else
{
goto v___jp_1484_;
}
v___jp_1469_:
{
if (lean_obj_tag(v___y_1470_) == 0)
{
return v___y_1470_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1471_ = lean_ctor_get(v___y_1470_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___y_1470_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___y_1470_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___y_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
v___jp_1484_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1485_ = lean_unsigned_to_nat(1u);
v___x_1486_ = lean_nat_add(v_currRecDepth_1480_, v___x_1485_);
lean_inc(v_ref_1481_);
lean_inc_ref(v_toCold_1479_);
v___x_1487_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1487_, 0, v_toCold_1479_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
lean_ctor_set(v___x_1487_, 2, v_ref_1481_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*3, v_diag_1482_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*3 + 1, v_suppressElabErrors_1483_);
lean_inc(v___y_1467_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
v___x_1488_ = lean_apply_6(v_x_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___x_1487_, v___y_1467_, lean_box(0));
v___y_1470_ = v___x_1488_;
goto v___jp_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1502_, lean_object* v_x_1503_){
_start:
{
if (lean_obj_tag(v_x_1503_) == 0)
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_box(0);
return v___x_1504_;
}
else
{
lean_object* v_key_1505_; lean_object* v_value_1506_; lean_object* v_tail_1507_; uint8_t v___x_1508_; 
v_key_1505_ = lean_ctor_get(v_x_1503_, 0);
v_value_1506_ = lean_ctor_get(v_x_1503_, 1);
v_tail_1507_ = lean_ctor_get(v_x_1503_, 2);
v___x_1508_ = l_Lean_ExprStructEq_beq(v_key_1505_, v_a_1502_);
if (v___x_1508_ == 0)
{
v_x_1503_ = v_tail_1507_;
goto _start;
}
else
{
lean_object* v___x_1510_; 
lean_inc(v_value_1506_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_value_1506_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1511_, lean_object* v_x_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1511_, v_x_1512_);
lean_dec(v_x_1512_);
lean_dec_ref(v_a_1511_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_buckets_1516_; lean_object* v___x_1517_; uint64_t v___x_1518_; uint64_t v___x_1519_; uint64_t v___x_1520_; uint64_t v_fold_1521_; uint64_t v___x_1522_; uint64_t v___x_1523_; uint64_t v___x_1524_; size_t v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_buckets_1516_ = lean_ctor_get(v_m_1514_, 1);
v___x_1517_ = lean_array_get_size(v_buckets_1516_);
v___x_1518_ = l_Lean_ExprStructEq_hash(v_a_1515_);
v___x_1519_ = 32ULL;
v___x_1520_ = lean_uint64_shift_right(v___x_1518_, v___x_1519_);
v_fold_1521_ = lean_uint64_xor(v___x_1518_, v___x_1520_);
v___x_1522_ = 16ULL;
v___x_1523_ = lean_uint64_shift_right(v_fold_1521_, v___x_1522_);
v___x_1524_ = lean_uint64_xor(v_fold_1521_, v___x_1523_);
v___x_1525_ = lean_uint64_to_usize(v___x_1524_);
v___x_1526_ = lean_usize_of_nat(v___x_1517_);
v___x_1527_ = ((size_t)1ULL);
v___x_1528_ = lean_usize_sub(v___x_1526_, v___x_1527_);
v___x_1529_ = lean_usize_land(v___x_1525_, v___x_1528_);
v___x_1530_ = lean_array_uget_borrowed(v_buckets_1516_, v___x_1529_);
v___x_1531_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1515_, v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1532_, v_a_1533_);
lean_dec_ref(v_a_1533_);
lean_dec_ref(v_m_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1538_, lean_object* v_pre_1539_, lean_object* v_post_1540_, uint8_t v_usedLetOnly_1541_, uint8_t v_skipConstInApp_1542_, uint8_t v_skipInstances_1543_, lean_object* v_body_1544_, lean_object* v_x_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_array_push(v_fvars_1538_, v_x_1545_);
v___x_1553_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1539_, v_post_1540_, v_usedLetOnly_1541_, v_skipConstInApp_1542_, v_skipInstances_1543_, v___x_1552_, v_body_1544_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1554_, lean_object* v_pre_1555_, lean_object* v_post_1556_, lean_object* v_usedLetOnly_1557_, lean_object* v_skipConstInApp_1558_, lean_object* v_skipInstances_1559_, lean_object* v_body_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
uint8_t v_usedLetOnly_boxed_1568_; uint8_t v_skipConstInApp_boxed_1569_; uint8_t v_skipInstances_boxed_1570_; lean_object* v_res_1571_; 
v_usedLetOnly_boxed_1568_ = lean_unbox(v_usedLetOnly_1557_);
v_skipConstInApp_boxed_1569_ = lean_unbox(v_skipConstInApp_1558_);
v_skipInstances_boxed_1570_ = lean_unbox(v_skipInstances_1559_);
v_res_1571_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1554_, v_pre_1555_, v_post_1556_, v_usedLetOnly_boxed_1568_, v_skipConstInApp_boxed_1569_, v_skipInstances_boxed_1570_, v_body_1560_, v_x_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1572_, lean_object* v_post_1573_, uint8_t v_usedLetOnly_1574_, uint8_t v_skipConstInApp_1575_, uint8_t v_skipInstances_1576_, lean_object* v_e_1577_, lean_object* v_a_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; 
lean_inc_ref(v_post_1573_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
lean_inc(v___y_1580_);
lean_inc_ref(v___y_1579_);
lean_inc_ref(v_e_1577_);
v___x_1584_ = lean_apply_6(v_post_1573_, v_e_1577_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, lean_box(0));
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1603_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1603_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1603_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
switch(lean_obj_tag(v_a_1585_))
{
case 0:
{
lean_object* v_e_1589_; lean_object* v___x_1591_; 
lean_dec_ref(v_e_1577_);
lean_dec_ref(v_post_1573_);
lean_dec_ref(v_pre_1572_);
v_e_1589_ = lean_ctor_get(v_a_1585_, 0);
lean_inc_ref(v_e_1589_);
lean_dec_ref_known(v_a_1585_, 1);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_e_1589_);
v___x_1591_ = v___x_1587_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_e_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
case 1:
{
lean_object* v_e_1593_; lean_object* v___x_1594_; 
lean_del_object(v___x_1587_);
lean_dec_ref(v_e_1577_);
v_e_1593_ = lean_ctor_get(v_a_1585_, 0);
lean_inc_ref(v_e_1593_);
lean_dec_ref_known(v_a_1585_, 1);
v___x_1594_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1572_, v_post_1573_, v_usedLetOnly_1574_, v_skipConstInApp_1575_, v_skipInstances_1576_, v_e_1593_, v_a_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v___x_1594_;
}
default: 
{
lean_object* v_e_x3f_1595_; 
lean_dec_ref(v_post_1573_);
lean_dec_ref(v_pre_1572_);
v_e_x3f_1595_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_e_x3f_1595_);
lean_dec_ref_known(v_a_1585_, 1);
if (lean_obj_tag(v_e_x3f_1595_) == 0)
{
lean_object* v___x_1597_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_e_1577_);
v___x_1597_ = v___x_1587_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_e_1577_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
else
{
lean_object* v_val_1599_; lean_object* v___x_1601_; 
lean_dec_ref(v_e_1577_);
v_val_1599_ = lean_ctor_get(v_e_x3f_1595_, 0);
lean_inc(v_val_1599_);
lean_dec_ref_known(v_e_x3f_1595_, 1);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_val_1599_);
v___x_1601_ = v___x_1587_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_val_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec_ref(v_e_1577_);
lean_dec_ref(v_post_1573_);
lean_dec_ref(v_pre_1572_);
v_a_1604_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1584_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1584_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1612_, lean_object* v_post_1613_, uint8_t v_usedLetOnly_1614_, uint8_t v_skipConstInApp_1615_, uint8_t v_skipInstances_1616_, lean_object* v_fvars_1617_, lean_object* v_e_1618_, lean_object* v_a_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
if (lean_obj_tag(v_e_1618_) == 6)
{
lean_object* v_binderName_1625_; lean_object* v_binderType_1626_; lean_object* v_body_1627_; uint8_t v_binderInfo_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_binderName_1625_ = lean_ctor_get(v_e_1618_, 0);
lean_inc(v_binderName_1625_);
v_binderType_1626_ = lean_ctor_get(v_e_1618_, 1);
lean_inc_ref(v_binderType_1626_);
v_body_1627_ = lean_ctor_get(v_e_1618_, 2);
lean_inc_ref(v_body_1627_);
v_binderInfo_1628_ = lean_ctor_get_uint8(v_e_1618_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1618_, 3);
v___x_1629_ = lean_expr_instantiate_rev(v_binderType_1626_, v_fvars_1617_);
lean_dec_ref(v_binderType_1626_);
lean_inc_ref(v_post_1613_);
lean_inc_ref(v_pre_1612_);
v___x_1630_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1612_, v_post_1613_, v_usedLetOnly_1614_, v_skipConstInApp_1615_, v_skipInstances_1616_, v___x_1629_, v_a_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___f_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
v___x_1632_ = lean_box(v_usedLetOnly_1614_);
v___x_1633_ = lean_box(v_skipConstInApp_1615_);
v___x_1634_ = lean_box(v_skipInstances_1616_);
v___f_1635_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1635_, 0, v_fvars_1617_);
lean_closure_set(v___f_1635_, 1, v_pre_1612_);
lean_closure_set(v___f_1635_, 2, v_post_1613_);
lean_closure_set(v___f_1635_, 3, v___x_1632_);
lean_closure_set(v___f_1635_, 4, v___x_1633_);
lean_closure_set(v___f_1635_, 5, v___x_1634_);
lean_closure_set(v___f_1635_, 6, v_body_1627_);
v___x_1636_ = 0;
v___x_1637_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1625_, v_binderInfo_1628_, v_a_1631_, v___f_1635_, v___x_1636_, v_a_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v___x_1637_;
}
else
{
lean_dec_ref(v_body_1627_);
lean_dec(v_binderName_1625_);
lean_dec_ref(v_fvars_1617_);
lean_dec_ref(v_post_1613_);
lean_dec_ref(v_pre_1612_);
return v___x_1630_;
}
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = lean_expr_instantiate_rev(v_e_1618_, v_fvars_1617_);
lean_dec_ref(v_e_1618_);
lean_inc_ref(v_post_1613_);
lean_inc_ref(v_pre_1612_);
v___x_1639_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1612_, v_post_1613_, v_usedLetOnly_1614_, v_skipConstInApp_1615_, v_skipInstances_1616_, v___x_1638_, v_a_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; uint8_t v___x_1641_; uint8_t v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = 0;
v___x_1642_ = 1;
v___x_1643_ = 1;
v___x_1644_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1617_, v_a_1640_, v___x_1641_, v_usedLetOnly_1614_, v___x_1641_, v___x_1642_, v___x_1643_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec_ref(v_fvars_1617_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1612_, v_post_1613_, v_usedLetOnly_1614_, v_skipConstInApp_1615_, v_skipInstances_1616_, v_a_1645_, v_a_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v___x_1646_;
}
else
{
lean_dec_ref(v_post_1613_);
lean_dec_ref(v_pre_1612_);
return v___x_1644_;
}
}
else
{
lean_dec_ref(v_fvars_1617_);
lean_dec_ref(v_post_1613_);
lean_dec_ref(v_pre_1612_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1647_, lean_object* v_pre_1648_, lean_object* v_post_1649_, uint8_t v_usedLetOnly_1650_, uint8_t v_skipConstInApp_1651_, uint8_t v_skipInstances_1652_, lean_object* v_body_1653_, lean_object* v_x_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_array_push(v_fvars_1647_, v_x_1654_);
v___x_1662_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1648_, v_post_1649_, v_usedLetOnly_1650_, v_skipConstInApp_1651_, v_skipInstances_1652_, v___x_1661_, v_body_1653_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1663_, lean_object* v_pre_1664_, lean_object* v_post_1665_, lean_object* v_usedLetOnly_1666_, lean_object* v_skipConstInApp_1667_, lean_object* v_skipInstances_1668_, lean_object* v_body_1669_, lean_object* v_x_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v_usedLetOnly_boxed_1677_; uint8_t v_skipConstInApp_boxed_1678_; uint8_t v_skipInstances_boxed_1679_; lean_object* v_res_1680_; 
v_usedLetOnly_boxed_1677_ = lean_unbox(v_usedLetOnly_1666_);
v_skipConstInApp_boxed_1678_ = lean_unbox(v_skipConstInApp_1667_);
v_skipInstances_boxed_1679_ = lean_unbox(v_skipInstances_1668_);
v_res_1680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1663_, v_pre_1664_, v_post_1665_, v_usedLetOnly_boxed_1677_, v_skipConstInApp_boxed_1678_, v_skipInstances_boxed_1679_, v_body_1669_, v_x_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1681_, lean_object* v_post_1682_, uint8_t v_usedLetOnly_1683_, uint8_t v_skipConstInApp_1684_, uint8_t v_skipInstances_1685_, lean_object* v_fvars_1686_, lean_object* v_e_1687_, lean_object* v_a_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
if (lean_obj_tag(v_e_1687_) == 8)
{
lean_object* v_declName_1694_; lean_object* v_type_1695_; lean_object* v_value_1696_; lean_object* v_body_1697_; uint8_t v_nondep_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_declName_1694_ = lean_ctor_get(v_e_1687_, 0);
lean_inc(v_declName_1694_);
v_type_1695_ = lean_ctor_get(v_e_1687_, 1);
lean_inc_ref(v_type_1695_);
v_value_1696_ = lean_ctor_get(v_e_1687_, 2);
lean_inc_ref(v_value_1696_);
v_body_1697_ = lean_ctor_get(v_e_1687_, 3);
lean_inc_ref(v_body_1697_);
v_nondep_1698_ = lean_ctor_get_uint8(v_e_1687_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1687_, 4);
v___x_1699_ = lean_expr_instantiate_rev(v_type_1695_, v_fvars_1686_);
lean_dec_ref(v_type_1695_);
lean_inc_ref(v_post_1682_);
lean_inc_ref(v_pre_1681_);
v___x_1700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1681_, v_post_1682_, v_usedLetOnly_1683_, v_skipConstInApp_1684_, v_skipInstances_1685_, v___x_1699_, v_a_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1702_ = lean_expr_instantiate_rev(v_value_1696_, v_fvars_1686_);
lean_dec_ref(v_value_1696_);
lean_inc_ref(v_post_1682_);
lean_inc_ref(v_pre_1681_);
v___x_1703_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1681_, v_post_1682_, v_usedLetOnly_1683_, v_skipConstInApp_1684_, v_skipInstances_1685_, v___x_1702_, v_a_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___f_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = lean_box(v_usedLetOnly_1683_);
v___x_1706_ = lean_box(v_skipConstInApp_1684_);
v___x_1707_ = lean_box(v_skipInstances_1685_);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1708_, 0, v_fvars_1686_);
lean_closure_set(v___f_1708_, 1, v_pre_1681_);
lean_closure_set(v___f_1708_, 2, v_post_1682_);
lean_closure_set(v___f_1708_, 3, v___x_1705_);
lean_closure_set(v___f_1708_, 4, v___x_1706_);
lean_closure_set(v___f_1708_, 5, v___x_1707_);
lean_closure_set(v___f_1708_, 6, v_body_1697_);
v___x_1709_ = 0;
v___x_1710_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1694_, v_a_1701_, v_a_1704_, v___f_1708_, v_nondep_1698_, v___x_1709_, v_a_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1710_;
}
else
{
lean_dec(v_a_1701_);
lean_dec_ref(v_body_1697_);
lean_dec(v_declName_1694_);
lean_dec_ref(v_fvars_1686_);
lean_dec_ref(v_post_1682_);
lean_dec_ref(v_pre_1681_);
return v___x_1703_;
}
}
else
{
lean_dec_ref(v_body_1697_);
lean_dec_ref(v_value_1696_);
lean_dec(v_declName_1694_);
lean_dec_ref(v_fvars_1686_);
lean_dec_ref(v_post_1682_);
lean_dec_ref(v_pre_1681_);
return v___x_1700_;
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_expr_instantiate_rev(v_e_1687_, v_fvars_1686_);
lean_dec_ref(v_e_1687_);
lean_inc_ref(v_post_1682_);
lean_inc_ref(v_pre_1681_);
v___x_1712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1681_, v_post_1682_, v_usedLetOnly_1683_, v_skipConstInApp_1684_, v_skipInstances_1685_, v___x_1711_, v_a_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; uint8_t v___x_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = 0;
v___x_1715_ = 1;
v___x_1716_ = l_Lean_Meta_mkLetFVars(v_fvars_1686_, v_a_1713_, v_usedLetOnly_1683_, v___x_1714_, v___x_1715_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec_ref(v_fvars_1686_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1681_, v_post_1682_, v_usedLetOnly_1683_, v_skipConstInApp_1684_, v_skipInstances_1685_, v_a_1717_, v_a_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1718_;
}
else
{
lean_dec_ref(v_post_1682_);
lean_dec_ref(v_pre_1681_);
return v___x_1716_;
}
}
else
{
lean_dec_ref(v_fvars_1686_);
lean_dec_ref(v_post_1682_);
lean_dec_ref(v_pre_1681_);
return v___x_1712_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1719_; lean_object* v_dummy_1720_; 
v___x_1719_ = lean_box(0);
v_dummy_1720_ = l_Lean_Expr_sort___override(v___x_1719_);
return v_dummy_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1721_, lean_object* v_post_1722_, uint8_t v_usedLetOnly_1723_, uint8_t v_skipConstInApp_1724_, uint8_t v_skipInstances_1725_, size_t v_sz_1726_, size_t v_i_1727_, lean_object* v_bs_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_lt(v_i_1727_, v_sz_1726_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; 
lean_dec_ref(v_post_1722_);
lean_dec_ref(v_pre_1721_);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_bs_1728_);
return v___x_1736_;
}
else
{
lean_object* v_v_1737_; lean_object* v___x_1738_; 
v_v_1737_ = lean_array_uget_borrowed(v_bs_1728_, v_i_1727_);
lean_inc(v_v_1737_);
lean_inc_ref(v_post_1722_);
lean_inc_ref(v_pre_1721_);
v___x_1738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1721_, v_post_1722_, v_usedLetOnly_1723_, v_skipConstInApp_1724_, v_skipInstances_1725_, v_v_1737_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; lean_object* v_bs_x27_1741_; size_t v___x_1742_; size_t v___x_1743_; lean_object* v___x_1744_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1740_ = lean_unsigned_to_nat(0u);
v_bs_x27_1741_ = lean_array_uset(v_bs_1728_, v_i_1727_, v___x_1740_);
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1727_, v___x_1742_);
v___x_1744_ = lean_array_uset(v_bs_x27_1741_, v_i_1727_, v_a_1739_);
v_i_1727_ = v___x_1743_;
v_bs_1728_ = v___x_1744_;
goto _start;
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v_bs_1728_);
lean_dec_ref(v_post_1722_);
lean_dec_ref(v_pre_1721_);
v_a_1746_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1738_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1738_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1754_, lean_object* v_post_1755_, uint8_t v_usedLetOnly_1756_, uint8_t v_skipConstInApp_1757_, uint8_t v_skipInstances_1758_, lean_object* v___x_1759_, lean_object* v___y_1760_, lean_object* v_b_1761_, lean_object* v_a_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1754_, v_post_1755_, v_usedLetOnly_1756_, v_skipConstInApp_1757_, v_skipInstances_1758_, v___x_1759_, v___y_1760_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1778_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1778_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1778_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1773_ = lean_array_fset(v_b_1761_, v_a_1762_, v_a_1769_);
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1774_);
v___x_1776_ = v___x_1771_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v_b_1761_);
v_a_1779_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1768_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1768_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1787_, lean_object* v_post_1788_, lean_object* v_usedLetOnly_1789_, lean_object* v_skipConstInApp_1790_, lean_object* v_skipInstances_1791_, lean_object* v___x_1792_, lean_object* v___y_1793_, lean_object* v_b_1794_, lean_object* v_a_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v_usedLetOnly_boxed_1801_; uint8_t v_skipConstInApp_boxed_1802_; uint8_t v_skipInstances_boxed_1803_; lean_object* v_res_1804_; 
v_usedLetOnly_boxed_1801_ = lean_unbox(v_usedLetOnly_1789_);
v_skipConstInApp_boxed_1802_ = lean_unbox(v_skipConstInApp_1790_);
v_skipInstances_boxed_1803_ = lean_unbox(v_skipInstances_1791_);
v_res_1804_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1787_, v_post_1788_, v_usedLetOnly_boxed_1801_, v_skipConstInApp_boxed_1802_, v_skipInstances_boxed_1803_, v___x_1792_, v___y_1793_, v_b_1794_, v_a_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v_a_1795_);
lean_dec(v___y_1793_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1805_, lean_object* v___x_1806_, lean_object* v_pre_1807_, lean_object* v_post_1808_, uint8_t v_usedLetOnly_1809_, uint8_t v_skipConstInApp_1810_, uint8_t v_skipInstances_1811_, lean_object* v_a_1812_, lean_object* v_b_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___y_1821_; uint8_t v___x_1844_; 
v___x_1844_ = lean_nat_dec_lt(v_a_1812_, v_upperBound_1805_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec(v_a_1812_);
lean_dec_ref(v_post_1808_);
lean_dec_ref(v_pre_1807_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_b_1813_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1846_ = lean_array_fget_borrowed(v_b_1813_, v_a_1812_);
v___x_1847_ = lean_array_get_size(v___x_1806_);
v___x_1848_ = lean_nat_dec_lt(v_a_1812_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; 
lean_inc(v___x_1846_);
v___x_1849_ = lean_box(v_usedLetOnly_1809_);
v___x_1850_ = lean_box(v_skipConstInApp_1810_);
v___x_1851_ = lean_box(v_skipInstances_1811_);
lean_inc(v_a_1812_);
lean_inc(v___y_1814_);
lean_inc_ref(v_post_1808_);
lean_inc_ref(v_pre_1807_);
v___f_1852_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1852_, 0, v_pre_1807_);
lean_closure_set(v___f_1852_, 1, v_post_1808_);
lean_closure_set(v___f_1852_, 2, v___x_1849_);
lean_closure_set(v___f_1852_, 3, v___x_1850_);
lean_closure_set(v___f_1852_, 4, v___x_1851_);
lean_closure_set(v___f_1852_, 5, v___x_1846_);
lean_closure_set(v___f_1852_, 6, v___y_1814_);
lean_closure_set(v___f_1852_, 7, v_b_1813_);
lean_closure_set(v___f_1852_, 8, v_a_1812_);
v___y_1821_ = v___f_1852_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1853_; uint8_t v_isInstance_1854_; 
v___x_1853_ = lean_array_fget_borrowed(v___x_1806_, v_a_1812_);
v_isInstance_1854_ = lean_ctor_get_uint8(v___x_1853_, sizeof(void*)*1 + 4);
if (v_isInstance_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___f_1858_; 
lean_inc(v___x_1846_);
v___x_1855_ = lean_box(v_usedLetOnly_1809_);
v___x_1856_ = lean_box(v_skipConstInApp_1810_);
v___x_1857_ = lean_box(v_skipInstances_1811_);
lean_inc(v_a_1812_);
lean_inc(v___y_1814_);
lean_inc_ref(v_post_1808_);
lean_inc_ref(v_pre_1807_);
v___f_1858_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1858_, 0, v_pre_1807_);
lean_closure_set(v___f_1858_, 1, v_post_1808_);
lean_closure_set(v___f_1858_, 2, v___x_1855_);
lean_closure_set(v___f_1858_, 3, v___x_1856_);
lean_closure_set(v___f_1858_, 4, v___x_1857_);
lean_closure_set(v___f_1858_, 5, v___x_1846_);
lean_closure_set(v___f_1858_, 6, v___y_1814_);
lean_closure_set(v___f_1858_, 7, v_b_1813_);
lean_closure_set(v___f_1858_, 8, v_a_1812_);
v___y_1821_ = v___f_1858_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1859_; lean_object* v___f_1860_; 
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_b_1813_);
v___f_1860_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1860_, 0, v___x_1859_);
v___y_1821_ = v___f_1860_;
goto v___jp_1820_;
}
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; 
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
lean_inc(v___y_1816_);
lean_inc_ref(v___y_1815_);
v___x_1822_ = lean_apply_5(v___y_1821_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, lean_box(0));
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1835_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1835_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1835_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
if (lean_obj_tag(v_a_1823_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; 
lean_dec(v_a_1812_);
lean_dec_ref(v_post_1808_);
lean_dec_ref(v_pre_1807_);
v_a_1827_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v_a_1823_, 1);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v_a_1827_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_del_object(v___x_1825_);
v_a_1831_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v_a_1823_, 1);
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = lean_nat_add(v_a_1812_, v___x_1832_);
lean_dec(v_a_1812_);
v_a_1812_ = v___x_1833_;
v_b_1813_ = v_a_1831_;
goto _start;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1812_);
lean_dec_ref(v_post_1808_);
lean_dec_ref(v_pre_1807_);
v_a_1836_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1822_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1822_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1861_, lean_object* v_pre_1862_, lean_object* v_post_1863_, uint8_t v_usedLetOnly_1864_, uint8_t v_skipConstInApp_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_f_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; 
if (lean_obj_tag(v_x_1866_) == 5)
{
lean_object* v_fn_1924_; lean_object* v_arg_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_fn_1924_ = lean_ctor_get(v_x_1866_, 0);
lean_inc_ref(v_fn_1924_);
v_arg_1925_ = lean_ctor_get(v_x_1866_, 1);
lean_inc_ref(v_arg_1925_);
lean_dec_ref_known(v_x_1866_, 2);
v___x_1926_ = lean_array_set(v_x_1867_, v_x_1868_, v_arg_1925_);
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_nat_sub(v_x_1868_, v___x_1927_);
lean_dec(v_x_1868_);
v_x_1866_ = v_fn_1924_;
v_x_1867_ = v___x_1926_;
v_x_1868_ = v___x_1928_;
goto _start;
}
else
{
lean_dec(v_x_1868_);
if (v_skipConstInApp_1865_ == 0)
{
goto v___jp_1921_;
}
else
{
uint8_t v___x_1930_; 
v___x_1930_ = l_Lean_Expr_isConst(v_x_1866_);
if (v___x_1930_ == 0)
{
goto v___jp_1921_;
}
else
{
v_f_1876_ = v_x_1866_;
v___y_1877_ = v___y_1869_;
v___y_1878_ = v___y_1870_;
v___y_1879_ = v___y_1871_;
v___y_1880_ = v___y_1872_;
v___y_1881_ = v___y_1873_;
goto v___jp_1875_;
}
}
}
v___jp_1875_:
{
if (v_skipInstances_1861_ == 0)
{
size_t v_sz_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v_sz_1882_ = lean_array_size(v_x_1867_);
v___x_1883_ = ((size_t)0ULL);
lean_inc_ref(v_post_1863_);
lean_inc_ref(v_pre_1862_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1862_, v_post_1863_, v_usedLetOnly_1864_, v_skipConstInApp_1865_, v_skipInstances_1861_, v_sz_1882_, v___x_1883_, v_x_1867_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1886_ = l_Lean_mkAppN(v_f_1876_, v_a_1885_);
lean_dec(v_a_1885_);
v___x_1887_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1862_, v_post_1863_, v_usedLetOnly_1864_, v_skipConstInApp_1865_, v_skipInstances_1861_, v___x_1886_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1887_;
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v_f_1876_);
lean_dec_ref(v_post_1863_);
lean_dec_ref(v_pre_1862_);
v_a_1888_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1884_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1884_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_array_get_size(v_x_1867_);
lean_inc_ref(v_f_1876_);
v___x_1897_ = l_Lean_Meta_getFunInfoNArgs(v_f_1876_, v___x_1896_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v_paramInfo_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v_paramInfo_1899_ = lean_ctor_get(v_a_1898_, 0);
lean_inc_ref(v_paramInfo_1899_);
lean_dec(v_a_1898_);
v___x_1900_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1863_);
lean_inc_ref(v_pre_1862_);
v___x_1901_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1896_, v_paramInfo_1899_, v_pre_1862_, v_post_1863_, v_usedLetOnly_1864_, v_skipConstInApp_1865_, v_skipInstances_1861_, v___x_1900_, v_x_1867_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec_ref(v_paramInfo_1899_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = l_Lean_mkAppN(v_f_1876_, v_a_1902_);
lean_dec(v_a_1902_);
v___x_1904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1862_, v_post_1863_, v_usedLetOnly_1864_, v_skipConstInApp_1865_, v_skipInstances_1861_, v___x_1903_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1904_;
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_f_1876_);
lean_dec_ref(v_post_1863_);
lean_dec_ref(v_pre_1862_);
v_a_1905_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1901_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1901_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_f_1876_);
lean_dec_ref(v_x_1867_);
lean_dec_ref(v_post_1863_);
lean_dec_ref(v_pre_1862_);
v_a_1913_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1897_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1897_);
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
}
v___jp_1921_:
{
lean_object* v___x_1922_; 
lean_inc_ref(v_post_1863_);
lean_inc_ref(v_pre_1862_);
v___x_1922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1862_, v_post_1863_, v_usedLetOnly_1864_, v_skipConstInApp_1865_, v_skipInstances_1861_, v_x_1866_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v_f_1876_ = v_a_1923_;
v___y_1877_ = v___y_1869_;
v___y_1878_ = v___y_1870_;
v___y_1879_ = v___y_1871_;
v___y_1880_ = v___y_1872_;
v___y_1881_ = v___y_1873_;
goto v___jp_1875_;
}
else
{
lean_dec_ref(v_x_1867_);
lean_dec_ref(v_post_1863_);
lean_dec_ref(v_pre_1862_);
return v___x_1922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1931_, lean_object* v_pre_1932_, lean_object* v_e_1933_, lean_object* v_post_1934_, uint8_t v_usedLetOnly_1935_, uint8_t v_skipConstInApp_1936_, uint8_t v_skipInstances_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Core_checkSystem(v___x_1931_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref_known(v___x_1944_, 1);
lean_inc_ref(v_pre_1932_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc_ref(v_e_1933_);
v___x_1945_ = lean_apply_6(v_pre_1932_, v_e_1933_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, lean_box(0));
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1994_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1994_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1994_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___y_1951_; 
switch(lean_obj_tag(v_a_1946_))
{
case 0:
{
lean_object* v_e_1986_; lean_object* v___x_1988_; 
lean_dec_ref(v_post_1934_);
lean_dec_ref(v_e_1933_);
lean_dec_ref(v_pre_1932_);
v_e_1986_ = lean_ctor_get(v_a_1946_, 0);
lean_inc_ref(v_e_1986_);
lean_dec_ref_known(v_a_1946_, 1);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v_e_1986_);
v___x_1988_ = v___x_1948_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_e_1986_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
case 1:
{
lean_object* v_e_1990_; lean_object* v___x_1991_; 
lean_del_object(v___x_1948_);
lean_dec_ref(v_e_1933_);
v_e_1990_ = lean_ctor_get(v_a_1946_, 0);
lean_inc_ref(v_e_1990_);
lean_dec_ref_known(v_a_1946_, 1);
v___x_1991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v_e_1990_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1991_;
}
default: 
{
lean_object* v_e_x3f_1992_; 
lean_del_object(v___x_1948_);
v_e_x3f_1992_ = lean_ctor_get(v_a_1946_, 0);
lean_inc(v_e_x3f_1992_);
lean_dec_ref_known(v_a_1946_, 1);
if (lean_obj_tag(v_e_x3f_1992_) == 0)
{
v___y_1951_ = v_e_1933_;
goto v___jp_1950_;
}
else
{
lean_object* v_val_1993_; 
lean_dec_ref(v_e_1933_);
v_val_1993_ = lean_ctor_get(v_e_x3f_1992_, 0);
lean_inc(v_val_1993_);
lean_dec_ref_known(v_e_x3f_1992_, 1);
v___y_1951_ = v_val_1993_;
goto v___jp_1950_;
}
}
}
v___jp_1950_:
{
switch(lean_obj_tag(v___y_1951_))
{
case 7:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v___x_1952_, v___y_1951_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1953_;
}
case 6:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1955_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v___x_1954_, v___y_1951_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1955_;
}
case 8:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v___x_1956_, v___y_1951_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1957_;
}
case 5:
{
lean_object* v_dummy_1958_; lean_object* v_nargs_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_dummy_1958_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1959_ = l_Lean_Expr_getAppNumArgs(v___y_1951_);
lean_inc(v_nargs_1959_);
v___x_1960_ = lean_mk_array(v_nargs_1959_, v_dummy_1958_);
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_nat_sub(v_nargs_1959_, v___x_1961_);
lean_dec(v_nargs_1959_);
v___x_1963_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1937_, v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v___y_1951_, v___x_1960_, v___x_1962_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1963_;
}
case 10:
{
lean_object* v_data_1964_; lean_object* v_expr_1965_; lean_object* v___x_1966_; 
v_data_1964_ = lean_ctor_get(v___y_1951_, 0);
v_expr_1965_ = lean_ctor_get(v___y_1951_, 1);
lean_inc_ref(v_expr_1965_);
lean_inc_ref(v_post_1934_);
lean_inc_ref(v_pre_1932_);
v___x_1966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v_expr_1965_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; size_t v___x_1968_; size_t v___x_1969_; uint8_t v___x_1970_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = lean_ptr_addr(v_expr_1965_);
v___x_1969_ = lean_ptr_addr(v_a_1967_);
v___x_1970_ = lean_usize_dec_eq(v___x_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_inc(v_data_1964_);
lean_dec_ref_known(v___y_1951_, 2);
v___x_1971_ = l_Lean_Expr_mdata___override(v_data_1964_, v_a_1967_);
v___x_1972_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v___x_1971_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1972_;
}
else
{
lean_object* v___x_1973_; 
lean_dec(v_a_1967_);
v___x_1973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v___y_1951_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1973_;
}
}
else
{
lean_dec_ref_known(v___y_1951_, 2);
lean_dec_ref(v_post_1934_);
lean_dec_ref(v_pre_1932_);
return v___x_1966_;
}
}
case 11:
{
lean_object* v_typeName_1974_; lean_object* v_idx_1975_; lean_object* v_struct_1976_; lean_object* v___x_1977_; 
v_typeName_1974_ = lean_ctor_get(v___y_1951_, 0);
v_idx_1975_ = lean_ctor_get(v___y_1951_, 1);
v_struct_1976_ = lean_ctor_get(v___y_1951_, 2);
lean_inc_ref(v_struct_1976_);
lean_inc_ref(v_post_1934_);
lean_inc_ref(v_pre_1932_);
v___x_1977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v_struct_1976_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; size_t v___x_1979_; size_t v___x_1980_; uint8_t v___x_1981_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = lean_ptr_addr(v_struct_1976_);
v___x_1980_ = lean_ptr_addr(v_a_1978_);
v___x_1981_ = lean_usize_dec_eq(v___x_1979_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_inc(v_idx_1975_);
lean_inc(v_typeName_1974_);
lean_dec_ref_known(v___y_1951_, 3);
v___x_1982_ = l_Lean_Expr_proj___override(v_typeName_1974_, v_idx_1975_, v_a_1978_);
v___x_1983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v___x_1982_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; 
lean_dec(v_a_1978_);
v___x_1984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v___y_1951_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1984_;
}
}
else
{
lean_dec_ref_known(v___y_1951_, 3);
lean_dec_ref(v_post_1934_);
lean_dec_ref(v_pre_1932_);
return v___x_1977_;
}
}
default: 
{
lean_object* v___x_1985_; 
v___x_1985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1932_, v_post_1934_, v_usedLetOnly_1935_, v_skipConstInApp_1936_, v_skipInstances_1937_, v___y_1951_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1985_;
}
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_post_1934_);
lean_dec_ref(v_e_1933_);
lean_dec_ref(v_pre_1932_);
v_a_1995_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1945_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1945_);
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
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v_post_1934_);
lean_dec_ref(v_e_1933_);
lean_dec_ref(v_pre_1932_);
v_a_2003_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1944_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1944_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2011_, lean_object* v_pre_2012_, lean_object* v_e_2013_, lean_object* v_post_2014_, lean_object* v_usedLetOnly_2015_, lean_object* v_skipConstInApp_2016_, lean_object* v_skipInstances_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v_usedLetOnly_boxed_2024_; uint8_t v_skipConstInApp_boxed_2025_; uint8_t v_skipInstances_boxed_2026_; lean_object* v_res_2027_; 
v_usedLetOnly_boxed_2024_ = lean_unbox(v_usedLetOnly_2015_);
v_skipConstInApp_boxed_2025_ = lean_unbox(v_skipConstInApp_2016_);
v_skipInstances_boxed_2026_ = lean_unbox(v_skipInstances_2017_);
v_res_2027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2011_, v_pre_2012_, v_e_2013_, v_post_2014_, v_usedLetOnly_boxed_2024_, v_skipConstInApp_boxed_2025_, v_skipInstances_boxed_2026_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2028_, lean_object* v_post_2029_, uint8_t v_usedLetOnly_2030_, uint8_t v_skipConstInApp_2031_, uint8_t v_skipInstances_2032_, lean_object* v_e_2033_, lean_object* v_a_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_inc(v_a_2034_);
v___x_2040_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2040_, 0, lean_box(0));
lean_closure_set(v___x_2040_, 1, lean_box(0));
lean_closure_set(v___x_2040_, 2, v_a_2034_);
v___x_2041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2040_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2076_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2076_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2076_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2042_, v_e_2033_);
lean_dec(v_a_2042_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___f_2051_; lean_object* v___x_2052_; 
lean_del_object(v___x_2044_);
v___x_2047_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2048_ = lean_box(v_usedLetOnly_2030_);
v___x_2049_ = lean_box(v_skipConstInApp_2031_);
v___x_2050_ = lean_box(v_skipInstances_2032_);
lean_inc_ref(v_e_2033_);
v___f_2051_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2051_, 0, v___x_2047_);
lean_closure_set(v___f_2051_, 1, v_pre_2028_);
lean_closure_set(v___f_2051_, 2, v_e_2033_);
lean_closure_set(v___f_2051_, 3, v_post_2029_);
lean_closure_set(v___f_2051_, 4, v___x_2048_);
lean_closure_set(v___f_2051_, 5, v___x_2049_);
lean_closure_set(v___f_2051_, 6, v___x_2050_);
v___x_2052_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2051_, v_a_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___f_2054_; lean_object* v___x_2055_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_n(v_a_2053_, 2);
lean_dec_ref_known(v___x_2052_, 1);
lean_inc(v_a_2034_);
v___f_2054_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2054_, 0, v_a_2034_);
lean_closure_set(v___f_2054_, 1, v_e_2033_);
lean_closure_set(v___f_2054_, 2, v_a_2053_);
v___x_2055_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2054_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v___x_2055_, 0);
lean_dec(v_unused_2063_);
v___x_2057_ = v___x_2055_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_dec(v___x_2055_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_a_2053_);
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2053_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_a_2053_);
v_a_2064_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2055_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2055_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_dec_ref(v_e_2033_);
return v___x_2052_;
}
}
else
{
lean_object* v_val_2072_; lean_object* v___x_2074_; 
lean_dec_ref(v_e_2033_);
lean_dec_ref(v_post_2029_);
lean_dec_ref(v_pre_2028_);
v_val_2072_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2072_);
lean_dec_ref_known(v___x_2046_, 1);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v_val_2072_);
v___x_2074_ = v___x_2044_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_val_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_e_2033_);
lean_dec_ref(v_post_2029_);
lean_dec_ref(v_pre_2028_);
v_a_2077_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2041_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2041_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2085_, lean_object* v_pre_2086_, lean_object* v_post_2087_, lean_object* v_usedLetOnly_2088_, lean_object* v_skipConstInApp_2089_, lean_object* v_skipInstances_2090_, lean_object* v_body_2091_, lean_object* v_x_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v_usedLetOnly_boxed_2099_; uint8_t v_skipConstInApp_boxed_2100_; uint8_t v_skipInstances_boxed_2101_; lean_object* v_res_2102_; 
v_usedLetOnly_boxed_2099_ = lean_unbox(v_usedLetOnly_2088_);
v_skipConstInApp_boxed_2100_ = lean_unbox(v_skipConstInApp_2089_);
v_skipInstances_boxed_2101_ = lean_unbox(v_skipInstances_2090_);
v_res_2102_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2085_, v_pre_2086_, v_post_2087_, v_usedLetOnly_boxed_2099_, v_skipConstInApp_boxed_2100_, v_skipInstances_boxed_2101_, v_body_2091_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2103_, lean_object* v_post_2104_, uint8_t v_usedLetOnly_2105_, uint8_t v_skipConstInApp_2106_, uint8_t v_skipInstances_2107_, lean_object* v_fvars_2108_, lean_object* v_e_2109_, lean_object* v_a_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
if (lean_obj_tag(v_e_2109_) == 7)
{
lean_object* v_binderName_2116_; lean_object* v_binderType_2117_; lean_object* v_body_2118_; uint8_t v_binderInfo_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_binderName_2116_ = lean_ctor_get(v_e_2109_, 0);
lean_inc(v_binderName_2116_);
v_binderType_2117_ = lean_ctor_get(v_e_2109_, 1);
lean_inc_ref(v_binderType_2117_);
v_body_2118_ = lean_ctor_get(v_e_2109_, 2);
lean_inc_ref(v_body_2118_);
v_binderInfo_2119_ = lean_ctor_get_uint8(v_e_2109_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2109_, 3);
v___x_2120_ = lean_expr_instantiate_rev(v_binderType_2117_, v_fvars_2108_);
lean_dec_ref(v_binderType_2117_);
lean_inc_ref(v_post_2104_);
lean_inc_ref(v_pre_2103_);
v___x_2121_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2103_, v_post_2104_, v_usedLetOnly_2105_, v_skipConstInApp_2106_, v_skipInstances_2107_, v___x_2120_, v_a_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___f_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = lean_box(v_usedLetOnly_2105_);
v___x_2124_ = lean_box(v_skipConstInApp_2106_);
v___x_2125_ = lean_box(v_skipInstances_2107_);
v___f_2126_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2126_, 0, v_fvars_2108_);
lean_closure_set(v___f_2126_, 1, v_pre_2103_);
lean_closure_set(v___f_2126_, 2, v_post_2104_);
lean_closure_set(v___f_2126_, 3, v___x_2123_);
lean_closure_set(v___f_2126_, 4, v___x_2124_);
lean_closure_set(v___f_2126_, 5, v___x_2125_);
lean_closure_set(v___f_2126_, 6, v_body_2118_);
v___x_2127_ = 0;
v___x_2128_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2116_, v_binderInfo_2119_, v_a_2122_, v___f_2126_, v___x_2127_, v_a_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
return v___x_2128_;
}
else
{
lean_dec_ref(v_body_2118_);
lean_dec(v_binderName_2116_);
lean_dec_ref(v_fvars_2108_);
lean_dec_ref(v_post_2104_);
lean_dec_ref(v_pre_2103_);
return v___x_2121_;
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_expr_instantiate_rev(v_e_2109_, v_fvars_2108_);
lean_dec_ref(v_e_2109_);
lean_inc_ref(v_post_2104_);
lean_inc_ref(v_pre_2103_);
v___x_2130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2103_, v_post_2104_, v_usedLetOnly_2105_, v_skipConstInApp_2106_, v_skipInstances_2107_, v___x_2129_, v_a_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; uint8_t v___x_2132_; uint8_t v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = 0;
v___x_2133_ = 1;
v___x_2134_ = 1;
v___x_2135_ = l_Lean_Meta_mkForallFVars(v_fvars_2108_, v_a_2131_, v___x_2132_, v_usedLetOnly_2105_, v___x_2133_, v___x_2134_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec_ref(v_fvars_2108_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2103_, v_post_2104_, v_usedLetOnly_2105_, v_skipConstInApp_2106_, v_skipInstances_2107_, v_a_2136_, v_a_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
return v___x_2137_;
}
else
{
lean_dec_ref(v_post_2104_);
lean_dec_ref(v_pre_2103_);
return v___x_2135_;
}
}
else
{
lean_dec_ref(v_fvars_2108_);
lean_dec_ref(v_post_2104_);
lean_dec_ref(v_pre_2103_);
return v___x_2130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2138_, lean_object* v_pre_2139_, lean_object* v_post_2140_, uint8_t v_usedLetOnly_2141_, uint8_t v_skipConstInApp_2142_, uint8_t v_skipInstances_2143_, lean_object* v_body_2144_, lean_object* v_x_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_array_push(v_fvars_2138_, v_x_2145_);
v___x_2153_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2139_, v_post_2140_, v_usedLetOnly_2141_, v_skipConstInApp_2142_, v_skipInstances_2143_, v___x_2152_, v_body_2144_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2154_, lean_object* v_post_2155_, lean_object* v_usedLetOnly_2156_, lean_object* v_skipConstInApp_2157_, lean_object* v_skipInstances_2158_, lean_object* v_e_2159_, lean_object* v_a_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
uint8_t v_usedLetOnly_boxed_2166_; uint8_t v_skipConstInApp_boxed_2167_; uint8_t v_skipInstances_boxed_2168_; lean_object* v_res_2169_; 
v_usedLetOnly_boxed_2166_ = lean_unbox(v_usedLetOnly_2156_);
v_skipConstInApp_boxed_2167_ = lean_unbox(v_skipConstInApp_2157_);
v_skipInstances_boxed_2168_ = lean_unbox(v_skipInstances_2158_);
v_res_2169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2154_, v_post_2155_, v_usedLetOnly_boxed_2166_, v_skipConstInApp_boxed_2167_, v_skipInstances_boxed_2168_, v_e_2159_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v_a_2160_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2170_, lean_object* v_post_2171_, lean_object* v_usedLetOnly_2172_, lean_object* v_skipConstInApp_2173_, lean_object* v_skipInstances_2174_, lean_object* v_sz_2175_, lean_object* v_i_2176_, lean_object* v_bs_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v_usedLetOnly_boxed_2184_; uint8_t v_skipConstInApp_boxed_2185_; uint8_t v_skipInstances_boxed_2186_; size_t v_sz_boxed_2187_; size_t v_i_boxed_2188_; lean_object* v_res_2189_; 
v_usedLetOnly_boxed_2184_ = lean_unbox(v_usedLetOnly_2172_);
v_skipConstInApp_boxed_2185_ = lean_unbox(v_skipConstInApp_2173_);
v_skipInstances_boxed_2186_ = lean_unbox(v_skipInstances_2174_);
v_sz_boxed_2187_ = lean_unbox_usize(v_sz_2175_);
lean_dec(v_sz_2175_);
v_i_boxed_2188_ = lean_unbox_usize(v_i_2176_);
lean_dec(v_i_2176_);
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2170_, v_post_2171_, v_usedLetOnly_boxed_2184_, v_skipConstInApp_boxed_2185_, v_skipInstances_boxed_2186_, v_sz_boxed_2187_, v_i_boxed_2188_, v_bs_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2190_, lean_object* v_post_2191_, lean_object* v_usedLetOnly_2192_, lean_object* v_skipConstInApp_2193_, lean_object* v_skipInstances_2194_, lean_object* v_e_2195_, lean_object* v_a_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
uint8_t v_usedLetOnly_boxed_2202_; uint8_t v_skipConstInApp_boxed_2203_; uint8_t v_skipInstances_boxed_2204_; lean_object* v_res_2205_; 
v_usedLetOnly_boxed_2202_ = lean_unbox(v_usedLetOnly_2192_);
v_skipConstInApp_boxed_2203_ = lean_unbox(v_skipConstInApp_2193_);
v_skipInstances_boxed_2204_ = lean_unbox(v_skipInstances_2194_);
v_res_2205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2190_, v_post_2191_, v_usedLetOnly_boxed_2202_, v_skipConstInApp_boxed_2203_, v_skipInstances_boxed_2204_, v_e_2195_, v_a_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v_a_2196_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2206_, lean_object* v_post_2207_, lean_object* v_usedLetOnly_2208_, lean_object* v_skipConstInApp_2209_, lean_object* v_skipInstances_2210_, lean_object* v_fvars_2211_, lean_object* v_e_2212_, lean_object* v_a_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
uint8_t v_usedLetOnly_boxed_2219_; uint8_t v_skipConstInApp_boxed_2220_; uint8_t v_skipInstances_boxed_2221_; lean_object* v_res_2222_; 
v_usedLetOnly_boxed_2219_ = lean_unbox(v_usedLetOnly_2208_);
v_skipConstInApp_boxed_2220_ = lean_unbox(v_skipConstInApp_2209_);
v_skipInstances_boxed_2221_ = lean_unbox(v_skipInstances_2210_);
v_res_2222_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2206_, v_post_2207_, v_usedLetOnly_boxed_2219_, v_skipConstInApp_boxed_2220_, v_skipInstances_boxed_2221_, v_fvars_2211_, v_e_2212_, v_a_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v_a_2213_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2223_, lean_object* v_post_2224_, lean_object* v_usedLetOnly_2225_, lean_object* v_skipConstInApp_2226_, lean_object* v_skipInstances_2227_, lean_object* v_fvars_2228_, lean_object* v_e_2229_, lean_object* v_a_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
uint8_t v_usedLetOnly_boxed_2236_; uint8_t v_skipConstInApp_boxed_2237_; uint8_t v_skipInstances_boxed_2238_; lean_object* v_res_2239_; 
v_usedLetOnly_boxed_2236_ = lean_unbox(v_usedLetOnly_2225_);
v_skipConstInApp_boxed_2237_ = lean_unbox(v_skipConstInApp_2226_);
v_skipInstances_boxed_2238_ = lean_unbox(v_skipInstances_2227_);
v_res_2239_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2223_, v_post_2224_, v_usedLetOnly_boxed_2236_, v_skipConstInApp_boxed_2237_, v_skipInstances_boxed_2238_, v_fvars_2228_, v_e_2229_, v_a_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v_a_2230_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2240_, lean_object* v_post_2241_, lean_object* v_usedLetOnly_2242_, lean_object* v_skipConstInApp_2243_, lean_object* v_skipInstances_2244_, lean_object* v_fvars_2245_, lean_object* v_e_2246_, lean_object* v_a_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint8_t v_usedLetOnly_boxed_2253_; uint8_t v_skipConstInApp_boxed_2254_; uint8_t v_skipInstances_boxed_2255_; lean_object* v_res_2256_; 
v_usedLetOnly_boxed_2253_ = lean_unbox(v_usedLetOnly_2242_);
v_skipConstInApp_boxed_2254_ = lean_unbox(v_skipConstInApp_2243_);
v_skipInstances_boxed_2255_ = lean_unbox(v_skipInstances_2244_);
v_res_2256_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2240_, v_post_2241_, v_usedLetOnly_boxed_2253_, v_skipConstInApp_boxed_2254_, v_skipInstances_boxed_2255_, v_fvars_2245_, v_e_2246_, v_a_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v_a_2247_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2257_, lean_object* v___x_2258_, lean_object* v_pre_2259_, lean_object* v_post_2260_, lean_object* v_usedLetOnly_2261_, lean_object* v_skipConstInApp_2262_, lean_object* v_skipInstances_2263_, lean_object* v_a_2264_, lean_object* v_b_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v_usedLetOnly_boxed_2272_; uint8_t v_skipConstInApp_boxed_2273_; uint8_t v_skipInstances_boxed_2274_; lean_object* v_res_2275_; 
v_usedLetOnly_boxed_2272_ = lean_unbox(v_usedLetOnly_2261_);
v_skipConstInApp_boxed_2273_ = lean_unbox(v_skipConstInApp_2262_);
v_skipInstances_boxed_2274_ = lean_unbox(v_skipInstances_2263_);
v_res_2275_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2257_, v___x_2258_, v_pre_2259_, v_post_2260_, v_usedLetOnly_boxed_2272_, v_skipConstInApp_boxed_2273_, v_skipInstances_boxed_2274_, v_a_2264_, v_b_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___x_2258_);
lean_dec(v_upperBound_2257_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2276_, lean_object* v_pre_2277_, lean_object* v_post_2278_, lean_object* v_usedLetOnly_2279_, lean_object* v_skipConstInApp_2280_, lean_object* v_x_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
uint8_t v_skipInstances_boxed_2290_; uint8_t v_usedLetOnly_boxed_2291_; uint8_t v_skipConstInApp_boxed_2292_; lean_object* v_res_2293_; 
v_skipInstances_boxed_2290_ = lean_unbox(v_skipInstances_2276_);
v_usedLetOnly_boxed_2291_ = lean_unbox(v_usedLetOnly_2279_);
v_skipConstInApp_boxed_2292_ = lean_unbox(v_skipConstInApp_2280_);
v_res_2293_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2290_, v_pre_2277_, v_post_2278_, v_usedLetOnly_boxed_2291_, v_skipConstInApp_boxed_2292_, v_x_2281_, v_x_2282_, v_x_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
return v_res_2293_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2295_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2295_, 0, lean_box(0));
lean_closure_set(v___x_2295_, 1, lean_box(0));
lean_closure_set(v___x_2295_, 2, v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2296_, lean_object* v_pre_2297_, lean_object* v_post_2298_, uint8_t v_usedLetOnly_2299_, uint8_t v_skipConstInApp_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_a_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2306_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2307_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2306_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = 0;
v___x_2310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2297_, v_post_2298_, v_usedLetOnly_2299_, v_skipConstInApp_2300_, v___x_2309_, v_input_2296_, v_a_2308_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2312_, 0, lean_box(0));
lean_closure_set(v___x_2312_, 1, lean_box(0));
lean_closure_set(v___x_2312_, 2, v_a_2308_);
v___x_2313_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2312_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v___x_2313_, 0);
lean_dec(v_unused_2321_);
v___x_2315_ = v___x_2313_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_dec(v___x_2313_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v_a_2311_);
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2311_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_dec(v_a_2308_);
return v___x_2310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2322_, lean_object* v_pre_2323_, lean_object* v_post_2324_, lean_object* v_usedLetOnly_2325_, lean_object* v_skipConstInApp_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
uint8_t v_usedLetOnly_boxed_2332_; uint8_t v_skipConstInApp_boxed_2333_; lean_object* v_res_2334_; 
v_usedLetOnly_boxed_2332_ = lean_unbox(v_usedLetOnly_2325_);
v_skipConstInApp_boxed_2333_ = lean_unbox(v_skipConstInApp_2326_);
v_res_2334_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2322_, v_pre_2323_, v_post_2324_, v_usedLetOnly_boxed_2332_, v_skipConstInApp_boxed_2333_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2335_, lean_object* v_as_2336_, lean_object* v_j_2337_){
_start:
{
lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = lean_array_get_size(v_as_2336_);
v___x_2339_ = lean_nat_dec_lt(v_j_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
lean_dec(v_j_2337_);
v___x_2340_ = lean_box(0);
return v___x_2340_;
}
else
{
lean_object* v___x_2341_; lean_object* v_declName_2342_; uint8_t v___x_2343_; 
v___x_2341_ = lean_array_fget_borrowed(v_as_2336_, v_j_2337_);
v_declName_2342_ = lean_ctor_get(v___x_2341_, 3);
v___x_2343_ = lean_name_eq(v_declName_2342_, v___x_2335_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_unsigned_to_nat(1u);
v___x_2345_ = lean_nat_add(v_j_2337_, v___x_2344_);
lean_dec(v_j_2337_);
v_j_2337_ = v___x_2345_;
goto _start;
}
else
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2347_, 0, v_j_2337_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2348_, lean_object* v_as_2349_, lean_object* v_j_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2348_, v_as_2349_, v_j_2350_);
lean_dec_ref(v_as_2349_);
lean_dec(v___x_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_st_ref_get(v_val_2352_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v_val_2360_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2367_, lean_object* v_val_2368_, lean_object* v_a_2369_, lean_object* v___x_2370_, lean_object* v_____r_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2377_ = lean_st_ref_take(v_val_2367_);
v___x_2378_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2368_, v_a_2369_, v___x_2377_);
v___x_2379_ = lean_st_ref_put(v_val_2367_, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2370_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2382_, lean_object* v_val_2383_, lean_object* v_a_2384_, lean_object* v___x_2385_, lean_object* v_____r_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2382_, v_val_2383_, v_a_2384_, v___x_2385_, v_____r_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_val_2383_);
lean_dec(v_val_2382_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2393_, lean_object* v_val_2394_, lean_object* v_next_2395_, lean_object* v_next_2396_, lean_object* v___x_2397_, lean_object* v___x_2398_, lean_object* v_upperBound_2399_, lean_object* v_params_2400_, lean_object* v___x_2401_, lean_object* v_a_2402_, uint8_t v_b_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v_a_2410_; uint8_t v___x_2414_; 
v___x_2414_ = lean_nat_dec_lt(v_a_2402_, v_upperBound_2399_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_dec(v_a_2402_);
lean_dec_ref(v___x_2401_);
lean_dec(v_next_2395_);
v___x_2415_ = lean_box(v_b_2403_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
return v___x_2416_;
}
else
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = lean_st_ref_get(v_val_2393_);
v___x_2418_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2396_, v_a_2402_, v___x_2417_);
lean_dec(v___x_2417_);
if (v___x_2418_ == 0)
{
v_a_2410_ = v_b_2403_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2419_; uint8_t v_foApprox_2420_; uint8_t v_ctxApprox_2421_; uint8_t v_quasiPatternApprox_2422_; uint8_t v_constApprox_2423_; uint8_t v_isDefEqStuckEx_2424_; uint8_t v_unificationHints_2425_; uint8_t v_assignSyntheticOpaque_2426_; uint8_t v_offsetCnstrs_2427_; uint8_t v_transparency_2428_; uint8_t v_etaStruct_2429_; uint8_t v_univApprox_2430_; uint8_t v_iota_2431_; uint8_t v_beta_2432_; uint8_t v_proj_2433_; uint8_t v_zeta_2434_; uint8_t v_zetaDelta_2435_; uint8_t v_zetaUnused_2436_; uint8_t v_zetaHave_2437_; uint8_t v_canUnfoldPredicateConfig_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2484_; 
v___x_2419_ = l_Lean_Meta_Context_config(v___y_2404_);
v_foApprox_2420_ = lean_ctor_get_uint8(v___x_2419_, 0);
v_ctxApprox_2421_ = lean_ctor_get_uint8(v___x_2419_, 1);
v_quasiPatternApprox_2422_ = lean_ctor_get_uint8(v___x_2419_, 2);
v_constApprox_2423_ = lean_ctor_get_uint8(v___x_2419_, 3);
v_isDefEqStuckEx_2424_ = lean_ctor_get_uint8(v___x_2419_, 4);
v_unificationHints_2425_ = lean_ctor_get_uint8(v___x_2419_, 5);
v_assignSyntheticOpaque_2426_ = lean_ctor_get_uint8(v___x_2419_, 7);
v_offsetCnstrs_2427_ = lean_ctor_get_uint8(v___x_2419_, 8);
v_transparency_2428_ = lean_ctor_get_uint8(v___x_2419_, 9);
v_etaStruct_2429_ = lean_ctor_get_uint8(v___x_2419_, 10);
v_univApprox_2430_ = lean_ctor_get_uint8(v___x_2419_, 11);
v_iota_2431_ = lean_ctor_get_uint8(v___x_2419_, 12);
v_beta_2432_ = lean_ctor_get_uint8(v___x_2419_, 13);
v_proj_2433_ = lean_ctor_get_uint8(v___x_2419_, 14);
v_zeta_2434_ = lean_ctor_get_uint8(v___x_2419_, 15);
v_zetaDelta_2435_ = lean_ctor_get_uint8(v___x_2419_, 16);
v_zetaUnused_2436_ = lean_ctor_get_uint8(v___x_2419_, 17);
v_zetaHave_2437_ = lean_ctor_get_uint8(v___x_2419_, 18);
v_canUnfoldPredicateConfig_2438_ = lean_ctor_get_uint8(v___x_2419_, 19);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2440_ = v___x_2419_;
v_isShared_2441_ = v_isSharedCheck_2484_;
goto v_resetjp_2439_;
}
else
{
lean_dec(v___x_2419_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2484_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
uint8_t v_trackZetaDelta_2442_; lean_object* v_zetaDeltaSet_2443_; lean_object* v_lctx_2444_; lean_object* v_localInstances_2445_; lean_object* v_defEqCtx_x3f_2446_; lean_object* v_synthPendingDepth_2447_; lean_object* v_customCanUnfoldPredicate_x3f_2448_; uint8_t v_univApprox_2449_; uint8_t v_inTypeClassResolution_2450_; uint8_t v_cacheInferType_2451_; uint8_t v___x_2452_; lean_object* v___x_2454_; 
v_trackZetaDelta_2442_ = lean_ctor_get_uint8(v___y_2404_, sizeof(void*)*7);
v_zetaDeltaSet_2443_ = lean_ctor_get(v___y_2404_, 1);
v_lctx_2444_ = lean_ctor_get(v___y_2404_, 2);
v_localInstances_2445_ = lean_ctor_get(v___y_2404_, 3);
v_defEqCtx_x3f_2446_ = lean_ctor_get(v___y_2404_, 4);
v_synthPendingDepth_2447_ = lean_ctor_get(v___y_2404_, 5);
v_customCanUnfoldPredicate_x3f_2448_ = lean_ctor_get(v___y_2404_, 6);
v_univApprox_2449_ = lean_ctor_get_uint8(v___y_2404_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2450_ = lean_ctor_get_uint8(v___y_2404_, sizeof(void*)*7 + 2);
v_cacheInferType_2451_ = lean_ctor_get_uint8(v___y_2404_, sizeof(void*)*7 + 3);
v___x_2452_ = 0;
if (v_isShared_2441_ == 0)
{
v___x_2454_ = v___x_2440_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 0, v_foApprox_2420_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 1, v_ctxApprox_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 2, v_quasiPatternApprox_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 3, v_constApprox_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 4, v_isDefEqStuckEx_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 5, v_unificationHints_2425_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 7, v_assignSyntheticOpaque_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 8, v_offsetCnstrs_2427_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 9, v_transparency_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 10, v_etaStruct_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 11, v_univApprox_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 12, v_iota_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 13, v_beta_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 14, v_proj_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 15, v_zeta_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 16, v_zetaDelta_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 17, v_zetaUnused_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 18, v_zetaHave_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 19, v_canUnfoldPredicateConfig_2438_);
v___x_2454_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
uint64_t v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v_transparency_2459_; uint8_t v___x_2460_; lean_object* v___y_2462_; lean_object* v___x_2476_; uint8_t v___x_2477_; uint8_t v___x_2478_; 
lean_ctor_set_uint8(v___x_2454_, 6, v___x_2452_);
v___x_2455_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2454_);
v___x_2456_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set_uint64(v___x_2456_, sizeof(void*)*1, v___x_2455_);
lean_inc(v_customCanUnfoldPredicate_x3f_2448_);
lean_inc(v_synthPendingDepth_2447_);
lean_inc(v_defEqCtx_x3f_2446_);
lean_inc_ref(v_localInstances_2445_);
lean_inc_ref(v_lctx_2444_);
lean_inc(v_zetaDeltaSet_2443_);
lean_inc_ref(v___x_2456_);
v___x_2457_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v_zetaDeltaSet_2443_);
lean_ctor_set(v___x_2457_, 2, v_lctx_2444_);
lean_ctor_set(v___x_2457_, 3, v_localInstances_2445_);
lean_ctor_set(v___x_2457_, 4, v_defEqCtx_x3f_2446_);
lean_ctor_set(v___x_2457_, 5, v_synthPendingDepth_2447_);
lean_ctor_set(v___x_2457_, 6, v_customCanUnfoldPredicate_x3f_2448_);
lean_ctor_set_uint8(v___x_2457_, sizeof(void*)*7, v_trackZetaDelta_2442_);
lean_ctor_set_uint8(v___x_2457_, sizeof(void*)*7 + 1, v_univApprox_2449_);
lean_ctor_set_uint8(v___x_2457_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2450_);
lean_ctor_set_uint8(v___x_2457_, sizeof(void*)*7 + 3, v_cacheInferType_2451_);
v___x_2458_ = l_Lean_Meta_Context_config(v___x_2457_);
v_transparency_2459_ = lean_ctor_get_uint8(v___x_2458_, 9);
lean_dec_ref(v___x_2458_);
v___x_2460_ = lean_nat_dec_eq(v___x_2397_, v___x_2398_);
v___x_2476_ = lean_array_fget_borrowed(v_params_2400_, v_a_2402_);
v___x_2477_ = 2;
v___x_2478_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2459_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec_ref_known(v___x_2457_, 7);
v___x_2479_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2477_, v___x_2456_);
lean_inc(v_customCanUnfoldPredicate_x3f_2448_);
lean_inc(v_synthPendingDepth_2447_);
lean_inc(v_defEqCtx_x3f_2446_);
lean_inc_ref(v_localInstances_2445_);
lean_inc_ref(v_lctx_2444_);
lean_inc(v_zetaDeltaSet_2443_);
v___x_2480_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v_zetaDeltaSet_2443_);
lean_ctor_set(v___x_2480_, 2, v_lctx_2444_);
lean_ctor_set(v___x_2480_, 3, v_localInstances_2445_);
lean_ctor_set(v___x_2480_, 4, v_defEqCtx_x3f_2446_);
lean_ctor_set(v___x_2480_, 5, v_synthPendingDepth_2447_);
lean_ctor_set(v___x_2480_, 6, v_customCanUnfoldPredicate_x3f_2448_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*7, v_trackZetaDelta_2442_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*7 + 1, v_univApprox_2449_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2450_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*7 + 3, v_cacheInferType_2451_);
lean_inc_ref(v___x_2401_);
lean_inc(v___x_2476_);
v___x_2481_ = l_Lean_Meta_isExprDefEq(v___x_2476_, v___x_2401_, v___x_2480_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref_known(v___x_2480_, 7);
v___y_2462_ = v___x_2481_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2482_; 
lean_dec_ref_known(v___x_2456_, 1);
lean_inc_ref(v___x_2401_);
lean_inc(v___x_2476_);
v___x_2482_ = l_Lean_Meta_isExprDefEq(v___x_2476_, v___x_2401_, v___x_2457_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref_known(v___x_2457_, 7);
v___y_2462_ = v___x_2482_;
goto v___jp_2461_;
}
v___jp_2461_:
{
if (lean_obj_tag(v___y_2462_) == 0)
{
lean_object* v_a_2463_; uint8_t v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___y_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___y_2462_, 1);
v___x_2464_ = lean_unbox(v_a_2463_);
lean_dec(v_a_2463_);
if (v___x_2464_ == 0)
{
v_a_2410_ = v_b_2403_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_st_ref_take(v_val_2393_);
lean_inc(v_a_2402_);
lean_inc(v_next_2395_);
v___x_2466_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2394_, v_next_2395_, v_next_2396_, v_a_2402_, v___x_2465_);
v___x_2467_ = lean_st_ref_put(v_val_2393_, v___x_2466_);
v_a_2410_ = v___x_2460_;
goto v___jp_2409_;
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_a_2402_);
lean_dec_ref(v___x_2401_);
lean_dec(v_next_2395_);
v_a_2468_ = lean_ctor_get(v___y_2462_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___y_2462_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___y_2462_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___y_2462_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
}
}
}
v___jp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_unsigned_to_nat(1u);
v___x_2412_ = lean_nat_add(v_a_2402_, v___x_2411_);
lean_dec(v_a_2402_);
v_a_2402_ = v___x_2412_;
v_b_2403_ = v_a_2410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2485_, lean_object* v_val_2486_, lean_object* v_next_2487_, lean_object* v_next_2488_, lean_object* v___x_2489_, lean_object* v___x_2490_, lean_object* v_upperBound_2491_, lean_object* v_params_2492_, lean_object* v___x_2493_, lean_object* v_a_2494_, lean_object* v_b_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
uint8_t v_b_boxed_2501_; lean_object* v_res_2502_; 
v_b_boxed_2501_ = lean_unbox(v_b_2495_);
v_res_2502_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2485_, v_val_2486_, v_next_2487_, v_next_2488_, v___x_2489_, v___x_2490_, v_upperBound_2491_, v_params_2492_, v___x_2493_, v_a_2494_, v_b_boxed_2501_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v_params_2492_);
lean_dec(v_upperBound_2491_);
lean_dec(v___x_2490_);
lean_dec(v___x_2489_);
lean_dec(v_next_2488_);
lean_dec(v_val_2486_);
lean_dec(v_val_2485_);
return v_res_2502_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2514_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2515_ = l_Lean_Name_append(v___x_2514_, v___x_2513_);
return v___x_2515_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2518_ = l_Lean_stringToMessageData(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2520_ = l_Lean_stringToMessageData(v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2526_ = l_Lean_stringToMessageData(v___x_2525_);
return v___x_2526_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2529_ = l_Lean_stringToMessageData(v___x_2528_);
return v___x_2529_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2532_ = l_Lean_stringToMessageData(v___x_2531_);
return v___x_2532_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2535_ = l_Lean_stringToMessageData(v___x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2536_, lean_object* v_val_2537_, lean_object* v_upperBound_2538_, lean_object* v_args_2539_, lean_object* v_e_2540_, lean_object* v_next_2541_, lean_object* v_params_2542_, lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v_a_2545_, lean_object* v_b_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_a_2553_; lean_object* v___y_2558_; uint8_t v___x_2577_; 
v___x_2577_ = lean_nat_dec_lt(v_a_2545_, v_upperBound_2538_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_b_2546_);
return v___x_2578_;
}
else
{
lean_object* v___x_2579_; 
v___x_2579_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2536_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = lean_box(0);
v___x_2582_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2537_, v_a_2545_, v_a_2580_);
lean_dec(v_a_2580_);
if (v___x_2582_ == 0)
{
v_a_2553_ = v___x_2581_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = lean_array_get_size(v_args_2539_);
v___x_2584_ = lean_nat_dec_lt(v_a_2545_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v_toCold_2585_; lean_object* v_options_2586_; lean_object* v_inheritedTraceOptions_2587_; uint8_t v_hasTrace_2588_; 
v_toCold_2585_ = lean_ctor_get(v___y_2549_, 0);
v_options_2586_ = lean_ctor_get(v_toCold_2585_, 2);
v_inheritedTraceOptions_2587_ = lean_ctor_get(v_toCold_2585_, 11);
v_hasTrace_2588_ = lean_ctor_get_uint8(v_options_2586_, sizeof(void*)*1);
if (v_hasTrace_2588_ == 0)
{
goto v___jp_2589_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2591_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2592_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2587_, v_options_2586_, v___x_2592_);
if (v___x_2593_ == 0)
{
goto v___jp_2589_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2594_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2537_);
v___x_2595_ = l_Nat_reprFast(v_val_2537_);
v___x_2596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
v___x_2597_ = l_Lean_MessageData_ofFormat(v___x_2596_);
v___x_2598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2594_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2598_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
lean_inc(v_a_2545_);
v___x_2601_ = l_Nat_reprFast(v_a_2545_);
v___x_2602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
v___x_2603_ = l_Lean_MessageData_ofFormat(v___x_2602_);
lean_inc_ref(v___x_2603_);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2600_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
lean_inc_ref(v_e_2540_);
v___x_2607_ = l_Lean_MessageData_ofExpr(v_e_2540_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2603_);
v___x_2612_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2591_, v___x_2611_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
lean_inc(v_a_2545_);
v___x_2614_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2581_, v_a_2613_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2614_;
goto v___jp_2557_;
}
else
{
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
return v___x_2612_;
}
}
}
v___jp_2589_:
{
lean_object* v___x_2590_; 
lean_inc(v_a_2545_);
v___x_2590_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2581_, v___x_2581_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2590_;
goto v___jp_2557_;
}
}
else
{
lean_object* v___x_2615_; 
v___x_2615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2536_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v___x_2617_ = lean_array_fget_borrowed(v_args_2539_, v_a_2545_);
v___x_2618_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2537_, v_a_2545_, v_next_2541_, v_a_2616_);
lean_dec(v_a_2616_);
if (lean_obj_tag(v___x_2618_) == 1)
{
lean_object* v_val_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2723_; 
v_val_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2723_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_val_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2723_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; uint8_t v_foApprox_2624_; uint8_t v_ctxApprox_2625_; uint8_t v_quasiPatternApprox_2626_; uint8_t v_constApprox_2627_; uint8_t v_isDefEqStuckEx_2628_; uint8_t v_unificationHints_2629_; uint8_t v_assignSyntheticOpaque_2630_; uint8_t v_offsetCnstrs_2631_; uint8_t v_transparency_2632_; uint8_t v_etaStruct_2633_; uint8_t v_univApprox_2634_; uint8_t v_iota_2635_; uint8_t v_beta_2636_; uint8_t v_proj_2637_; uint8_t v_zeta_2638_; uint8_t v_zetaDelta_2639_; uint8_t v_zetaUnused_2640_; uint8_t v_zetaHave_2641_; uint8_t v_canUnfoldPredicateConfig_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2722_; 
v___x_2623_ = l_Lean_Meta_Context_config(v___y_2547_);
v_foApprox_2624_ = lean_ctor_get_uint8(v___x_2623_, 0);
v_ctxApprox_2625_ = lean_ctor_get_uint8(v___x_2623_, 1);
v_quasiPatternApprox_2626_ = lean_ctor_get_uint8(v___x_2623_, 2);
v_constApprox_2627_ = lean_ctor_get_uint8(v___x_2623_, 3);
v_isDefEqStuckEx_2628_ = lean_ctor_get_uint8(v___x_2623_, 4);
v_unificationHints_2629_ = lean_ctor_get_uint8(v___x_2623_, 5);
v_assignSyntheticOpaque_2630_ = lean_ctor_get_uint8(v___x_2623_, 7);
v_offsetCnstrs_2631_ = lean_ctor_get_uint8(v___x_2623_, 8);
v_transparency_2632_ = lean_ctor_get_uint8(v___x_2623_, 9);
v_etaStruct_2633_ = lean_ctor_get_uint8(v___x_2623_, 10);
v_univApprox_2634_ = lean_ctor_get_uint8(v___x_2623_, 11);
v_iota_2635_ = lean_ctor_get_uint8(v___x_2623_, 12);
v_beta_2636_ = lean_ctor_get_uint8(v___x_2623_, 13);
v_proj_2637_ = lean_ctor_get_uint8(v___x_2623_, 14);
v_zeta_2638_ = lean_ctor_get_uint8(v___x_2623_, 15);
v_zetaDelta_2639_ = lean_ctor_get_uint8(v___x_2623_, 16);
v_zetaUnused_2640_ = lean_ctor_get_uint8(v___x_2623_, 17);
v_zetaHave_2641_ = lean_ctor_get_uint8(v___x_2623_, 18);
v_canUnfoldPredicateConfig_2642_ = lean_ctor_get_uint8(v___x_2623_, 19);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2644_ = v___x_2623_;
v_isShared_2645_ = v_isSharedCheck_2722_;
goto v_resetjp_2643_;
}
else
{
lean_dec(v___x_2623_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2722_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v_trackZetaDelta_2646_; lean_object* v_zetaDeltaSet_2647_; lean_object* v_lctx_2648_; lean_object* v_localInstances_2649_; lean_object* v_defEqCtx_x3f_2650_; lean_object* v_synthPendingDepth_2651_; lean_object* v_customCanUnfoldPredicate_x3f_2652_; uint8_t v_univApprox_2653_; uint8_t v_inTypeClassResolution_2654_; uint8_t v_cacheInferType_2655_; uint8_t v___x_2656_; lean_object* v___x_2658_; 
v_trackZetaDelta_2646_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7);
v_zetaDeltaSet_2647_ = lean_ctor_get(v___y_2547_, 1);
v_lctx_2648_ = lean_ctor_get(v___y_2547_, 2);
v_localInstances_2649_ = lean_ctor_get(v___y_2547_, 3);
v_defEqCtx_x3f_2650_ = lean_ctor_get(v___y_2547_, 4);
v_synthPendingDepth_2651_ = lean_ctor_get(v___y_2547_, 5);
v_customCanUnfoldPredicate_x3f_2652_ = lean_ctor_get(v___y_2547_, 6);
v_univApprox_2653_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2654_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 2);
v_cacheInferType_2655_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 3);
v___x_2656_ = 0;
if (v_isShared_2645_ == 0)
{
v___x_2658_ = v___x_2644_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 0, v_foApprox_2624_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 1, v_ctxApprox_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 2, v_quasiPatternApprox_2626_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 3, v_constApprox_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 4, v_isDefEqStuckEx_2628_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 5, v_unificationHints_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 7, v_assignSyntheticOpaque_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 8, v_offsetCnstrs_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 9, v_transparency_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 10, v_etaStruct_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 11, v_univApprox_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 12, v_iota_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 13, v_beta_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 14, v_proj_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 15, v_zeta_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 16, v_zetaDelta_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 17, v_zetaUnused_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 18, v_zetaHave_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2721_, 19, v_canUnfoldPredicateConfig_2642_);
v___x_2658_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
uint64_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v_transparency_2663_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___y_2669_; uint8_t v___x_2715_; uint8_t v___x_2716_; 
lean_ctor_set_uint8(v___x_2658_, 6, v___x_2656_);
v___x_2659_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2658_);
v___x_2660_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set_uint64(v___x_2660_, sizeof(void*)*1, v___x_2659_);
lean_inc(v_customCanUnfoldPredicate_x3f_2652_);
lean_inc(v_synthPendingDepth_2651_);
lean_inc(v_defEqCtx_x3f_2650_);
lean_inc_ref(v_localInstances_2649_);
lean_inc_ref(v_lctx_2648_);
lean_inc(v_zetaDeltaSet_2647_);
lean_inc_ref(v___x_2660_);
v___x_2661_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
lean_ctor_set(v___x_2661_, 1, v_zetaDeltaSet_2647_);
lean_ctor_set(v___x_2661_, 2, v_lctx_2648_);
lean_ctor_set(v___x_2661_, 3, v_localInstances_2649_);
lean_ctor_set(v___x_2661_, 4, v_defEqCtx_x3f_2650_);
lean_ctor_set(v___x_2661_, 5, v_synthPendingDepth_2651_);
lean_ctor_set(v___x_2661_, 6, v_customCanUnfoldPredicate_x3f_2652_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*7, v_trackZetaDelta_2646_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*7 + 1, v_univApprox_2653_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2654_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*7 + 3, v_cacheInferType_2655_);
v___x_2662_ = l_Lean_Meta_Context_config(v___x_2661_);
v_transparency_2663_ = lean_ctor_get_uint8(v___x_2662_, 9);
lean_dec_ref(v___x_2662_);
v___x_2666_ = l_Lean_instInhabitedExpr;
v___x_2667_ = lean_array_get_borrowed(v___x_2666_, v_params_2542_, v_val_2619_);
lean_dec(v_val_2619_);
v___x_2715_ = 2;
v___x_2716_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2663_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_dec_ref_known(v___x_2661_, 7);
v___x_2717_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2715_, v___x_2660_);
lean_inc(v_customCanUnfoldPredicate_x3f_2652_);
lean_inc(v_synthPendingDepth_2651_);
lean_inc(v_defEqCtx_x3f_2650_);
lean_inc_ref(v_localInstances_2649_);
lean_inc_ref(v_lctx_2648_);
lean_inc(v_zetaDeltaSet_2647_);
v___x_2718_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v_zetaDeltaSet_2647_);
lean_ctor_set(v___x_2718_, 2, v_lctx_2648_);
lean_ctor_set(v___x_2718_, 3, v_localInstances_2649_);
lean_ctor_set(v___x_2718_, 4, v_defEqCtx_x3f_2650_);
lean_ctor_set(v___x_2718_, 5, v_synthPendingDepth_2651_);
lean_ctor_set(v___x_2718_, 6, v_customCanUnfoldPredicate_x3f_2652_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*7, v_trackZetaDelta_2646_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*7 + 1, v_univApprox_2653_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2654_);
lean_ctor_set_uint8(v___x_2718_, sizeof(void*)*7 + 3, v_cacheInferType_2655_);
lean_inc(v___x_2617_);
lean_inc(v___x_2667_);
v___x_2719_ = l_Lean_Meta_isExprDefEq(v___x_2667_, v___x_2617_, v___x_2718_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref_known(v___x_2718_, 7);
v___y_2669_ = v___x_2719_;
goto v___jp_2668_;
}
else
{
lean_object* v___x_2720_; 
lean_dec_ref_known(v___x_2660_, 1);
lean_inc(v___x_2617_);
lean_inc(v___x_2667_);
v___x_2720_ = l_Lean_Meta_isExprDefEq(v___x_2667_, v___x_2617_, v___x_2661_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref_known(v___x_2661_, 7);
v___y_2669_ = v___x_2720_;
goto v___jp_2668_;
}
v___jp_2664_:
{
lean_object* v___x_2665_; 
lean_inc(v_a_2545_);
v___x_2665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2581_, v___x_2581_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2665_;
goto v___jp_2557_;
}
v___jp_2668_:
{
if (lean_obj_tag(v___y_2669_) == 0)
{
lean_object* v_a_2670_; uint8_t v___x_2671_; 
v_a_2670_ = lean_ctor_get(v___y_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___y_2669_, 1);
v___x_2671_ = lean_unbox(v_a_2670_);
lean_dec(v_a_2670_);
if (v___x_2671_ == 0)
{
lean_object* v_toCold_2672_; lean_object* v_options_2673_; uint8_t v_hasTrace_2674_; 
v_toCold_2672_ = lean_ctor_get(v___y_2549_, 0);
v_options_2673_ = lean_ctor_get(v_toCold_2672_, 2);
v_hasTrace_2674_ = lean_ctor_get_uint8(v_options_2673_, sizeof(void*)*1);
if (v_hasTrace_2674_ == 0)
{
lean_del_object(v___x_2621_);
goto v___jp_2664_;
}
else
{
lean_object* v_inheritedTraceOptions_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_inheritedTraceOptions_2675_ = lean_ctor_get(v_toCold_2672_, 11);
v___x_2676_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2677_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2675_, v_options_2673_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_del_object(v___x_2621_);
goto v___jp_2664_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2679_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2537_);
v___x_2680_ = l_Nat_reprFast(v_val_2537_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set_tag(v___x_2621_, 3);
lean_ctor_set(v___x_2621_, 0, v___x_2680_);
v___x_2682_ = v___x_2621_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2683_ = l_Lean_MessageData_ofFormat(v___x_2682_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2679_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
lean_inc(v_a_2545_);
v___x_2687_ = l_Nat_reprFast(v_a_2545_);
v___x_2688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
v___x_2689_ = l_Lean_MessageData_ofFormat(v___x_2688_);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2686_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
lean_inc_ref(v_e_2540_);
v___x_2693_ = l_Lean_MessageData_ofExpr(v_e_2540_);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
lean_inc(v___x_2667_);
v___x_2697_ = l_Lean_MessageData_ofExpr(v___x_2667_);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
lean_inc(v___x_2617_);
v___x_2701_ = l_Lean_MessageData_ofExpr(v___x_2617_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2676_, v___x_2702_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2705_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
lean_inc(v_a_2545_);
v___x_2705_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2581_, v_a_2704_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2705_;
goto v___jp_2557_;
}
else
{
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
return v___x_2703_;
}
}
}
}
}
else
{
lean_del_object(v___x_2621_);
v_a_2553_ = v___x_2581_;
goto v___jp_2552_;
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_del_object(v___x_2621_);
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v_a_2707_ = lean_ctor_get(v___y_2669_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___y_2669_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___y_2669_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___y_2669_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
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
lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; 
lean_dec(v___x_2618_);
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = 0;
lean_inc(v___x_2617_);
lean_inc(v_a_2545_);
v___x_2726_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2536_, v_val_2537_, v_a_2545_, v_next_2541_, v___x_2543_, v___x_2544_, v___x_2543_, v_params_2542_, v___x_2617_, v___x_2724_, v___x_2725_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; uint8_t v___x_2728_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2728_ = lean_unbox(v_a_2727_);
lean_dec(v_a_2727_);
if (v___x_2728_ == 0)
{
lean_object* v_toCold_2729_; lean_object* v_options_2730_; lean_object* v_inheritedTraceOptions_2731_; uint8_t v_hasTrace_2732_; 
v_toCold_2729_ = lean_ctor_get(v___y_2549_, 0);
v_options_2730_ = lean_ctor_get(v_toCold_2729_, 2);
v_inheritedTraceOptions_2731_ = lean_ctor_get(v_toCold_2729_, 11);
v_hasTrace_2732_ = lean_ctor_get_uint8(v_options_2730_, sizeof(void*)*1);
if (v_hasTrace_2732_ == 0)
{
goto v___jp_2733_;
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2736_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2731_, v_options_2730_, v___x_2736_);
if (v___x_2737_ == 0)
{
goto v___jp_2733_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2738_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2537_);
v___x_2739_ = l_Nat_reprFast(v_val_2537_);
v___x_2740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
v___x_2741_ = l_Lean_MessageData_ofFormat(v___x_2740_);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2738_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
lean_inc(v_a_2545_);
v___x_2745_ = l_Nat_reprFast(v_a_2545_);
v___x_2746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
v___x_2747_ = l_Lean_MessageData_ofFormat(v___x_2746_);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2744_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
lean_inc_ref(v_e_2540_);
v___x_2751_ = l_Lean_MessageData_ofExpr(v_e_2540_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
lean_inc(v___x_2617_);
v___x_2755_ = l_Lean_MessageData_ofExpr(v___x_2617_);
v___x_2756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2735_, v___x_2758_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
lean_inc(v_a_2545_);
v___x_2761_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2581_, v_a_2760_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2761_;
goto v___jp_2557_;
}
else
{
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
return v___x_2759_;
}
}
}
v___jp_2733_:
{
lean_object* v___x_2734_; 
lean_inc(v_a_2545_);
v___x_2734_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2581_, v___x_2581_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2734_;
goto v___jp_2557_;
}
}
else
{
v_a_2553_ = v___x_2581_;
goto v___jp_2552_;
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v_a_2762_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2726_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2726_);
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
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v_a_2770_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2615_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2615_);
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
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v_a_2778_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2579_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2579_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
v___jp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_nat_add(v_a_2545_, v___x_2554_);
lean_dec(v_a_2545_);
v_a_2545_ = v___x_2555_;
v_b_2546_ = v_a_2553_;
goto _start;
}
v___jp_2557_:
{
if (lean_obj_tag(v___y_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2568_; 
v_a_2559_ = lean_ctor_get(v___y_2558_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___y_2558_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2561_ = v___y_2558_;
v_isShared_2562_ = v_isSharedCheck_2568_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___y_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2568_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
if (lean_obj_tag(v_a_2559_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v_a_2563_ = lean_ctor_get(v_a_2559_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v_a_2559_, 1);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v_a_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
else
{
lean_object* v_a_2567_; 
lean_del_object(v___x_2561_);
v_a_2567_ = lean_ctor_get(v_a_2559_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v_a_2559_, 1);
v_a_2553_ = v_a_2567_;
goto v___jp_2552_;
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v_a_2569_ = lean_ctor_get(v___y_2558_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___y_2558_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___y_2558_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___y_2558_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2786_, lean_object* v_val_2787_, lean_object* v_upperBound_2788_, lean_object* v_args_2789_, lean_object* v_e_2790_, lean_object* v_next_2791_, lean_object* v_params_2792_, lean_object* v___x_2793_, lean_object* v___x_2794_, lean_object* v_a_2795_, lean_object* v_b_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2786_, v_val_2787_, v_upperBound_2788_, v_args_2789_, v_e_2790_, v_next_2791_, v_params_2792_, v___x_2793_, v___x_2794_, v_a_2795_, v_b_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___x_2794_);
lean_dec(v___x_2793_);
lean_dec_ref(v_params_2792_);
lean_dec(v_next_2791_);
lean_dec_ref(v_args_2789_);
lean_dec(v_upperBound_2788_);
lean_dec(v_val_2786_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2805_, lean_object* v___x_2806_, lean_object* v_val_2807_, lean_object* v_e_2808_, lean_object* v_next_2809_, lean_object* v_params_2810_, lean_object* v___x_2811_, lean_object* v___x_2812_, lean_object* v_x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
if (lean_obj_tag(v_x_2813_) == 5)
{
lean_object* v_fn_2821_; lean_object* v_arg_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_fn_2821_ = lean_ctor_get(v_x_2813_, 0);
lean_inc_ref(v_fn_2821_);
v_arg_2822_ = lean_ctor_get(v_x_2813_, 1);
lean_inc_ref(v_arg_2822_);
lean_dec_ref_known(v_x_2813_, 2);
v___x_2823_ = lean_array_set(v_x_2814_, v_x_2815_, v_arg_2822_);
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_nat_sub(v_x_2815_, v___x_2824_);
lean_dec(v_x_2815_);
v_x_2813_ = v_fn_2821_;
v_x_2814_ = v___x_2823_;
v_x_2815_ = v___x_2825_;
goto _start;
}
else
{
uint8_t v___x_2827_; 
lean_dec(v_x_2815_);
v___x_2827_ = l_Lean_Expr_isConst(v_x_2813_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_dec_ref(v_x_2814_);
lean_dec_ref(v_x_2813_);
lean_dec_ref(v_e_2808_);
v___x_2828_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = l_Lean_Expr_constName_x21(v_x_2813_);
lean_dec_ref(v_x_2813_);
v___x_2831_ = lean_unsigned_to_nat(0u);
v___x_2832_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2830_, v_preDefs_2805_, v___x_2831_);
lean_dec(v___x_2830_);
if (lean_obj_tag(v___x_2832_) == 1)
{
lean_object* v_val_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_val_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = lean_box(0);
v___x_2835_ = lean_array_get_borrowed(v___x_2831_, v___x_2806_, v_val_2833_);
v___x_2836_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2807_, v_val_2833_, v___x_2835_, v_x_2814_, v_e_2808_, v_next_2809_, v_params_2810_, v___x_2811_, v___x_2812_, v___x_2831_, v___x_2834_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec_ref(v_x_2814_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2844_; 
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2845_);
v___x_2838_ = v___x_2836_;
v_isShared_2839_ = v_isSharedCheck_2844_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v___x_2836_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2844_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2840_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2840_);
v___x_2842_ = v___x_2838_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
v_a_2846_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2836_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2836_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec(v___x_2832_);
lean_dec_ref(v_x_2814_);
lean_dec_ref(v_e_2808_);
v___x_2854_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2856_, lean_object* v___x_2857_, lean_object* v_val_2858_, lean_object* v_e_2859_, lean_object* v_next_2860_, lean_object* v_params_2861_, lean_object* v___x_2862_, lean_object* v___x_2863_, lean_object* v_x_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2856_, v___x_2857_, v_val_2858_, v_e_2859_, v_next_2860_, v_params_2861_, v___x_2862_, v___x_2863_, v_x_2864_, v_x_2865_, v_x_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___x_2863_);
lean_dec(v___x_2862_);
lean_dec_ref(v_params_2861_);
lean_dec(v_next_2860_);
lean_dec(v_val_2858_);
lean_dec_ref(v___x_2857_);
lean_dec_ref(v_preDefs_2856_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2873_, lean_object* v___x_2874_, lean_object* v_val_2875_, lean_object* v_a_2876_, lean_object* v_params_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, lean_object* v_e_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_dummy_2886_; lean_object* v_nargs_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_dummy_2886_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2887_ = l_Lean_Expr_getAppNumArgs(v_e_2880_);
lean_inc(v_nargs_2887_);
v___x_2888_ = lean_mk_array(v_nargs_2887_, v_dummy_2886_);
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_sub(v_nargs_2887_, v___x_2889_);
lean_dec(v_nargs_2887_);
lean_inc_ref(v_e_2880_);
v___x_2891_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2873_, v___x_2874_, v_val_2875_, v_e_2880_, v_a_2876_, v_params_2877_, v___x_2878_, v___x_2879_, v_e_2880_, v___x_2888_, v___x_2890_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2892_, lean_object* v___x_2893_, lean_object* v_val_2894_, lean_object* v_a_2895_, lean_object* v_params_2896_, lean_object* v___x_2897_, lean_object* v___x_2898_, lean_object* v_e_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2892_, v___x_2893_, v_val_2894_, v_a_2895_, v_params_2896_, v___x_2897_, v___x_2898_, v_e_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___x_2898_);
lean_dec(v___x_2897_);
lean_dec_ref(v_params_2896_);
lean_dec(v_a_2895_);
lean_dec(v_val_2894_);
lean_dec_ref(v___x_2893_);
lean_dec_ref(v_preDefs_2892_);
return v_res_2905_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2909_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2910_ = lean_unsigned_to_nat(6u);
v___x_2911_ = lean_unsigned_to_nat(201u);
v___x_2912_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2913_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2914_ = l_mkPanicMessageWithDecl(v___x_2913_, v___x_2912_, v___x_2911_, v___x_2910_, v___x_2909_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2915_, lean_object* v___x_2916_, lean_object* v_a_2917_, lean_object* v_preDefs_2918_, lean_object* v_val_2919_, lean_object* v___f_2920_, lean_object* v___x_2921_, lean_object* v_params_2922_, lean_object* v_body_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = lean_array_get_size(v_params_2922_);
v___x_2930_ = lean_array_get(v___x_2915_, v___x_2916_, v_a_2917_);
v___x_2931_ = lean_nat_dec_eq(v___x_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v___x_2930_);
lean_dec_ref(v_body_2923_);
lean_dec_ref(v_params_2922_);
lean_dec_ref(v___f_2920_);
lean_dec(v_val_2919_);
lean_dec_ref(v_preDefs_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v___x_2916_);
v___x_2932_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2933_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2932_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2933_;
}
else
{
lean_object* v___f_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; 
v___f_2934_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2934_, 0, v_preDefs_2918_);
lean_closure_set(v___f_2934_, 1, v___x_2916_);
lean_closure_set(v___f_2934_, 2, v_val_2919_);
lean_closure_set(v___f_2934_, 3, v_a_2917_);
lean_closure_set(v___f_2934_, 4, v_params_2922_);
lean_closure_set(v___f_2934_, 5, v___x_2929_);
lean_closure_set(v___f_2934_, 6, v___x_2930_);
v___x_2935_ = 0;
v___x_2936_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2923_, v___f_2934_, v___f_2920_, v___x_2935_, v___x_2931_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; 
v_unused_2944_ = lean_ctor_get(v___x_2936_, 0);
lean_dec(v_unused_2944_);
v___x_2938_ = v___x_2936_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_dec(v___x_2936_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2921_);
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2921_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_a_2945_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2936_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2936_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2953_, lean_object* v___x_2954_, lean_object* v_a_2955_, lean_object* v_preDefs_2956_, lean_object* v_val_2957_, lean_object* v___f_2958_, lean_object* v___x_2959_, lean_object* v_params_2960_, lean_object* v_body_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2953_, v___x_2954_, v_a_2955_, v_preDefs_2956_, v_val_2957_, v___f_2958_, v___x_2959_, v_params_2960_, v_body_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___x_2953_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2974_, 0, v_e_2968_);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v___x_2984_, lean_object* v_preDefs_2985_, lean_object* v_val_2986_, lean_object* v_upperBound_2987_, lean_object* v_a_2988_, lean_object* v_b_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_nat_dec_lt(v_a_2988_, v_upperBound_2987_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_dec(v_a_2988_);
lean_dec(v_val_2986_);
lean_dec_ref(v_preDefs_2985_);
lean_dec_ref(v___x_2984_);
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v_b_2989_);
return v___x_2996_;
}
else
{
lean_object* v___x_2997_; lean_object* v_value_2998_; lean_object* v___f_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___f_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; 
v___x_2997_ = lean_array_fget_borrowed(v_preDefs_2985_, v_a_2988_);
v_value_2998_ = lean_ctor_get(v___x_2997_, 7);
v___f_2999_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = lean_box(0);
lean_inc(v_val_2986_);
lean_inc_ref(v_preDefs_2985_);
lean_inc(v_a_2988_);
lean_inc_ref(v___x_2984_);
v___f_3002_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3002_, 0, v___x_3000_);
lean_closure_set(v___f_3002_, 1, v___x_2984_);
lean_closure_set(v___f_3002_, 2, v_a_2988_);
lean_closure_set(v___f_3002_, 3, v_preDefs_2985_);
lean_closure_set(v___f_3002_, 4, v_val_2986_);
lean_closure_set(v___f_3002_, 5, v___f_2999_);
lean_closure_set(v___f_3002_, 6, v___x_3001_);
v___x_3003_ = 0;
lean_inc_ref(v_value_2998_);
v___x_3004_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_2998_, v___f_3002_, v___x_3003_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
lean_dec_ref_known(v___x_3004_, 1);
v___x_3005_ = lean_unsigned_to_nat(1u);
v___x_3006_ = lean_nat_add(v_a_2988_, v___x_3005_);
lean_dec(v_a_2988_);
v_a_2988_ = v___x_3006_;
v_b_2989_ = v___x_3001_;
goto _start;
}
else
{
lean_dec(v_a_2988_);
lean_dec(v_val_2986_);
lean_dec_ref(v_preDefs_2985_);
lean_dec_ref(v___x_2984_);
return v___x_3004_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v___x_3008_, lean_object* v_preDefs_3009_, lean_object* v_val_3010_, lean_object* v_upperBound_3011_, lean_object* v_a_3012_, lean_object* v_b_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3008_, v_preDefs_3009_, v_val_3010_, v_upperBound_3011_, v_a_3012_, v_b_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v_upperBound_3011_);
return v_res_3019_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3022_ = l_Lean_stringToMessageData(v___x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
size_t v_sz_3029_; size_t v___x_3030_; lean_object* v___x_3031_; 
v_sz_3029_ = lean_array_size(v_preDefs_3023_);
v___x_3030_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3023_);
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3029_, v___x_3030_, v_preDefs_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; size_t v_sz_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc_n(v_a_3032_, 2);
lean_dec_ref_known(v___x_3031_, 1);
v_sz_3033_ = lean_array_size(v_a_3032_);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3033_, v___x_3030_, v_a_3032_);
v___x_3035_ = l_Lean_Elab_FixedParams_Info_init(v_a_3032_);
v___x_3036_ = lean_st_mk_ref(v___x_3035_);
v___x_3037_ = lean_st_ref_take(v___x_3036_);
v___x_3038_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3037_);
v___x_3039_ = lean_st_ref_put(v___x_3036_, v___x_3038_);
v___x_3040_ = lean_array_get_size(v_preDefs_3023_);
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = lean_box(0);
lean_inc(v___x_3036_);
v___x_3043_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3034_, v_preDefs_3023_, v___x_3036_, v___x_3040_, v___x_3041_, v___x_3042_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3083_; 
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; 
v_unused_3084_ = lean_ctor_get(v___x_3043_, 0);
lean_dec(v_unused_3084_);
v___x_3045_ = v___x_3043_;
v_isShared_3046_ = v_isSharedCheck_3083_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v___x_3043_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3083_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v_toCold_3048_; lean_object* v_options_3049_; uint8_t v_hasTrace_3050_; 
v___x_3047_ = lean_st_ref_get(v___x_3036_);
lean_dec(v___x_3036_);
v_toCold_3048_ = lean_ctor_get(v_a_3026_, 0);
v_options_3049_ = lean_ctor_get(v_toCold_3048_, 2);
v_hasTrace_3050_ = lean_ctor_get_uint8(v_options_3049_, sizeof(void*)*1);
if (v_hasTrace_3050_ == 0)
{
lean_object* v___x_3052_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3052_ = v___x_3045_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v_inheritedTraceOptions_3054_ = lean_ctor_get(v_toCold_3048_, 11);
v___x_3055_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3056_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3054_, v_options_3049_, v___x_3056_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3059_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3059_ = v___x_3045_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3047_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_del_object(v___x_3045_);
v___x_3061_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3047_);
v___x_3062_ = l_Lean_Elab_FixedParams_Info_format(v___x_3047_);
v___x_3063_ = l_Std_Format_indentD(v___x_3062_);
v___x_3064_ = l_Lean_MessageData_ofFormat(v___x_3063_);
v___x_3065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3061_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3055_, v___x_3065_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v___x_3066_, 0);
lean_dec(v_unused_3074_);
v___x_3068_ = v___x_3066_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_dec(v___x_3066_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3047_);
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3047_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v___x_3047_);
v_a_3075_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3066_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3066_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v___x_3036_);
v_a_3085_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3043_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3043_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec_ref(v_preDefs_3023_);
v_a_3093_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3031_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3031_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3108_, lean_object* v_val_3109_, lean_object* v_next_3110_, lean_object* v_next_3111_, lean_object* v___x_3112_, lean_object* v___x_3113_, lean_object* v_upperBound_3114_, lean_object* v_params_3115_, lean_object* v___x_3116_, lean_object* v_inst_3117_, lean_object* v_R_3118_, lean_object* v_a_3119_, uint8_t v_b_3120_, lean_object* v_c_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3108_, v_val_3109_, v_next_3110_, v_next_3111_, v___x_3112_, v___x_3113_, v_upperBound_3114_, v_params_3115_, v___x_3116_, v_a_3119_, v_b_3120_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3128_ = _args[0];
lean_object* v_val_3129_ = _args[1];
lean_object* v_next_3130_ = _args[2];
lean_object* v_next_3131_ = _args[3];
lean_object* v___x_3132_ = _args[4];
lean_object* v___x_3133_ = _args[5];
lean_object* v_upperBound_3134_ = _args[6];
lean_object* v_params_3135_ = _args[7];
lean_object* v___x_3136_ = _args[8];
lean_object* v_inst_3137_ = _args[9];
lean_object* v_R_3138_ = _args[10];
lean_object* v_a_3139_ = _args[11];
lean_object* v_b_3140_ = _args[12];
lean_object* v_c_3141_ = _args[13];
lean_object* v___y_3142_ = _args[14];
lean_object* v___y_3143_ = _args[15];
lean_object* v___y_3144_ = _args[16];
lean_object* v___y_3145_ = _args[17];
lean_object* v___y_3146_ = _args[18];
_start:
{
uint8_t v_b_boxed_3147_; lean_object* v_res_3148_; 
v_b_boxed_3147_ = lean_unbox(v_b_3140_);
v_res_3148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3128_, v_val_3129_, v_next_3130_, v_next_3131_, v___x_3132_, v___x_3133_, v_upperBound_3134_, v_params_3135_, v___x_3136_, v_inst_3137_, v_R_3138_, v_a_3139_, v_b_boxed_3147_, v_c_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec_ref(v_params_3135_);
lean_dec(v_upperBound_3134_);
lean_dec(v___x_3133_);
lean_dec(v___x_3132_);
lean_dec(v_next_3131_);
lean_dec(v_val_3129_);
lean_dec(v_val_3128_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3149_, lean_object* v_val_3150_, lean_object* v_upperBound_3151_, lean_object* v_args_3152_, lean_object* v_e_3153_, lean_object* v_next_3154_, lean_object* v_params_3155_, lean_object* v___x_3156_, lean_object* v___x_3157_, lean_object* v_inst_3158_, lean_object* v_R_3159_, lean_object* v_a_3160_, lean_object* v_b_3161_, lean_object* v_c_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3149_, v_val_3150_, v_upperBound_3151_, v_args_3152_, v_e_3153_, v_next_3154_, v_params_3155_, v___x_3156_, v___x_3157_, v_a_3160_, v_b_3161_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3169_ = _args[0];
lean_object* v_val_3170_ = _args[1];
lean_object* v_upperBound_3171_ = _args[2];
lean_object* v_args_3172_ = _args[3];
lean_object* v_e_3173_ = _args[4];
lean_object* v_next_3174_ = _args[5];
lean_object* v_params_3175_ = _args[6];
lean_object* v___x_3176_ = _args[7];
lean_object* v___x_3177_ = _args[8];
lean_object* v_inst_3178_ = _args[9];
lean_object* v_R_3179_ = _args[10];
lean_object* v_a_3180_ = _args[11];
lean_object* v_b_3181_ = _args[12];
lean_object* v_c_3182_ = _args[13];
lean_object* v___y_3183_ = _args[14];
lean_object* v___y_3184_ = _args[15];
lean_object* v___y_3185_ = _args[16];
lean_object* v___y_3186_ = _args[17];
lean_object* v___y_3187_ = _args[18];
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3169_, v_val_3170_, v_upperBound_3171_, v_args_3172_, v_e_3173_, v_next_3174_, v_params_3175_, v___x_3176_, v___x_3177_, v_inst_3178_, v_R_3179_, v_a_3180_, v_b_3181_, v_c_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___x_3177_);
lean_dec(v___x_3176_);
lean_dec_ref(v_params_3175_);
lean_dec(v_next_3174_);
lean_dec_ref(v_args_3172_);
lean_dec(v_upperBound_3171_);
lean_dec(v_val_3169_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v___x_3189_, lean_object* v_preDefs_3190_, lean_object* v_val_3191_, lean_object* v_upperBound_3192_, lean_object* v_inst_3193_, lean_object* v_R_3194_, lean_object* v_a_3195_, lean_object* v_b_3196_, lean_object* v_c_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3189_, v_preDefs_3190_, v_val_3191_, v_upperBound_3192_, v_a_3195_, v_b_3196_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v___x_3204_, lean_object* v_preDefs_3205_, lean_object* v_val_3206_, lean_object* v_upperBound_3207_, lean_object* v_inst_3208_, lean_object* v_R_3209_, lean_object* v_a_3210_, lean_object* v_b_3211_, lean_object* v_c_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3204_, v_preDefs_3205_, v_val_3206_, v_upperBound_3207_, v_inst_3208_, v_R_3209_, v_a_3210_, v_b_3211_, v_c_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v_upperBound_3207_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3219_, lean_object* v___x_3220_, lean_object* v_pre_3221_, lean_object* v_post_3222_, uint8_t v_usedLetOnly_3223_, uint8_t v_skipConstInApp_3224_, uint8_t v_skipInstances_3225_, lean_object* v___x_3226_, lean_object* v_inst_3227_, lean_object* v_R_3228_, lean_object* v_a_3229_, lean_object* v_b_3230_, lean_object* v_c_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3219_, v___x_3220_, v_pre_3221_, v_post_3222_, v_usedLetOnly_3223_, v_skipConstInApp_3224_, v_skipInstances_3225_, v_a_3229_, v_b_3230_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3239_ = _args[0];
lean_object* v___x_3240_ = _args[1];
lean_object* v_pre_3241_ = _args[2];
lean_object* v_post_3242_ = _args[3];
lean_object* v_usedLetOnly_3243_ = _args[4];
lean_object* v_skipConstInApp_3244_ = _args[5];
lean_object* v_skipInstances_3245_ = _args[6];
lean_object* v___x_3246_ = _args[7];
lean_object* v_inst_3247_ = _args[8];
lean_object* v_R_3248_ = _args[9];
lean_object* v_a_3249_ = _args[10];
lean_object* v_b_3250_ = _args[11];
lean_object* v_c_3251_ = _args[12];
lean_object* v___y_3252_ = _args[13];
lean_object* v___y_3253_ = _args[14];
lean_object* v___y_3254_ = _args[15];
lean_object* v___y_3255_ = _args[16];
lean_object* v___y_3256_ = _args[17];
lean_object* v___y_3257_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3258_; uint8_t v_skipConstInApp_boxed_3259_; uint8_t v_skipInstances_boxed_3260_; lean_object* v_res_3261_; 
v_usedLetOnly_boxed_3258_ = lean_unbox(v_usedLetOnly_3243_);
v_skipConstInApp_boxed_3259_ = lean_unbox(v_skipConstInApp_3244_);
v_skipInstances_boxed_3260_ = lean_unbox(v_skipInstances_3245_);
v_res_3261_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3239_, v___x_3240_, v_pre_3241_, v_post_3242_, v_usedLetOnly_boxed_3258_, v_skipConstInApp_boxed_3259_, v_skipInstances_boxed_3260_, v___x_3246_, v_inst_3247_, v_R_3248_, v_a_3249_, v_b_3250_, v_c_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___x_3246_);
lean_dec_ref(v___x_3240_);
lean_dec(v_upperBound_3239_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3262_, lean_object* v_m_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3263_, v_a_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3266_, lean_object* v_m_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3266_, v_m_3267_, v_a_3268_);
lean_dec_ref(v_a_3268_);
lean_dec_ref(v_m_3267_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3270_, lean_object* v_name_3271_, uint8_t v_bi_3272_, lean_object* v_type_3273_, lean_object* v_k_3274_, uint8_t v_kind_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3271_, v_bi_3272_, v_type_3273_, v_k_3274_, v_kind_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3283_, lean_object* v_name_3284_, lean_object* v_bi_3285_, lean_object* v_type_3286_, lean_object* v_k_3287_, lean_object* v_kind_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
uint8_t v_bi_boxed_3295_; uint8_t v_kind_boxed_3296_; lean_object* v_res_3297_; 
v_bi_boxed_3295_ = lean_unbox(v_bi_3285_);
v_kind_boxed_3296_ = lean_unbox(v_kind_3288_);
v_res_3297_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3283_, v_name_3284_, v_bi_boxed_3295_, v_type_3286_, v_k_3287_, v_kind_boxed_3296_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3298_, lean_object* v_name_3299_, lean_object* v_type_3300_, lean_object* v_val_3301_, lean_object* v_k_3302_, uint8_t v_nondep_3303_, uint8_t v_kind_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3299_, v_type_3300_, v_val_3301_, v_k_3302_, v_nondep_3303_, v_kind_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3312_, lean_object* v_name_3313_, lean_object* v_type_3314_, lean_object* v_val_3315_, lean_object* v_k_3316_, lean_object* v_nondep_3317_, lean_object* v_kind_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
uint8_t v_nondep_boxed_3325_; uint8_t v_kind_boxed_3326_; lean_object* v_res_3327_; 
v_nondep_boxed_3325_ = lean_unbox(v_nondep_3317_);
v_kind_boxed_3326_ = lean_unbox(v_kind_3318_);
v_res_3327_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3312_, v_name_3313_, v_type_3314_, v_val_3315_, v_k_3316_, v_nondep_boxed_3325_, v_kind_boxed_3326_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3328_, lean_object* v_ref_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3329_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3336_, lean_object* v_ref_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3336_, v_ref_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3353_, lean_object* v_x_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3353_, v_x_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3362_, lean_object* v_m_3363_, lean_object* v_a_3364_, lean_object* v_b_3365_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3363_, v_a_3364_, v_b_3365_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3367_, lean_object* v_a_3368_, lean_object* v_x_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3368_, v_x_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3371_, lean_object* v_a_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3371_, v_a_3372_, v_x_3373_);
lean_dec(v_x_3373_);
lean_dec_ref(v_a_3372_);
return v_res_3374_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3375_, lean_object* v_a_3376_, lean_object* v_x_3377_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3376_, v_x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3379_, lean_object* v_a_3380_, lean_object* v_x_3381_){
_start:
{
uint8_t v_res_3382_; lean_object* v_r_3383_; 
v_res_3382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3379_, v_a_3380_, v_x_3381_);
lean_dec(v_x_3381_);
lean_dec_ref(v_a_3380_);
v_r_3383_ = lean_box(v_res_3382_);
return v_r_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3384_, lean_object* v_data_3385_){
_start:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3387_, lean_object* v_a_3388_, lean_object* v_b_3389_, lean_object* v_x_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3388_, v_b_3389_, v_x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3392_, lean_object* v_i_3393_, lean_object* v_source_3394_, lean_object* v_target_3395_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3393_, v_source_3394_, v_target_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3397_, lean_object* v_x_3398_, lean_object* v_x_3399_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3398_, v_x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3414_, lean_object* v_x_3415_){
_start:
{
if (lean_obj_tag(v_x_3414_) == 0)
{
lean_object* v___x_3416_; 
v___x_3416_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3416_;
}
else
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3428_; 
v_val_3417_ = lean_ctor_get(v_x_3414_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_x_3414_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3419_ = v_x_3414_;
v_isShared_3420_ = v_isSharedCheck_3428_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v_x_3414_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3428_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3421_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3422_ = l_Nat_reprFast(v_val_3417_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 3);
lean_ctor_set(v___x_3419_, 0, v___x_3422_);
v___x_3424_ = v___x_3419_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3421_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Repr_addAppParen(v___x_3425_, v_x_3415_);
return v___x_3426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3429_, lean_object* v_x_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3429_, v_x_3430_);
lean_dec(v_x_3430_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3432_, lean_object* v_x_3433_, lean_object* v_x_3434_){
_start:
{
if (lean_obj_tag(v_x_3434_) == 0)
{
lean_dec(v_x_3432_);
return v_x_3433_;
}
else
{
lean_object* v_head_3435_; lean_object* v_tail_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3447_; 
v_head_3435_ = lean_ctor_get(v_x_3434_, 0);
v_tail_3436_ = lean_ctor_get(v_x_3434_, 1);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_x_3434_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3438_ = v_x_3434_;
v_isShared_3439_ = v_isSharedCheck_3447_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_tail_3436_);
lean_inc(v_head_3435_);
lean_dec(v_x_3434_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3447_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
lean_inc(v_x_3432_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 5);
lean_ctor_set(v___x_3438_, 1, v_x_3432_);
lean_ctor_set(v___x_3438_, 0, v_x_3433_);
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_x_3433_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_x_3432_);
v___x_3441_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = lean_unsigned_to_nat(0u);
v___x_3443_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3435_, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3441_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v_x_3433_ = v___x_3444_;
v_x_3434_ = v_tail_3436_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3448_, lean_object* v_x_3449_, lean_object* v_x_3450_){
_start:
{
if (lean_obj_tag(v_x_3450_) == 0)
{
lean_dec(v_x_3448_);
return v_x_3449_;
}
else
{
lean_object* v_head_3451_; lean_object* v_tail_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3463_; 
v_head_3451_ = lean_ctor_get(v_x_3450_, 0);
v_tail_3452_ = lean_ctor_get(v_x_3450_, 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_x_3450_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3454_ = v_x_3450_;
v_isShared_3455_ = v_isSharedCheck_3463_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_tail_3452_);
lean_inc(v_head_3451_);
lean_dec(v_x_3450_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3463_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
lean_inc(v_x_3448_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set_tag(v___x_3454_, 5);
lean_ctor_set(v___x_3454_, 1, v_x_3448_);
lean_ctor_set(v___x_3454_, 0, v_x_3449_);
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_x_3449_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_x_3448_);
v___x_3457_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3458_ = lean_unsigned_to_nat(0u);
v___x_3459_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3451_, v___x_3458_);
v___x_3460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3457_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3448_, v___x_3460_, v_tail_3452_);
return v___x_3461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3464_){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = lean_unsigned_to_nat(0u);
v___x_3466_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3464_, v___x_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3467_, lean_object* v_x_3468_){
_start:
{
if (lean_obj_tag(v_x_3467_) == 0)
{
lean_object* v___x_3469_; 
lean_dec(v_x_3468_);
v___x_3469_ = lean_box(0);
return v___x_3469_;
}
else
{
lean_object* v_tail_3470_; 
v_tail_3470_ = lean_ctor_get(v_x_3467_, 1);
if (lean_obj_tag(v_tail_3470_) == 0)
{
lean_object* v_head_3471_; lean_object* v___x_3472_; 
lean_dec(v_x_3468_);
v_head_3471_ = lean_ctor_get(v_x_3467_, 0);
lean_inc(v_head_3471_);
lean_dec_ref_known(v_x_3467_, 2);
v___x_3472_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3471_);
return v___x_3472_;
}
else
{
lean_object* v_head_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_inc(v_tail_3470_);
v_head_3473_ = lean_ctor_get(v_x_3467_, 0);
lean_inc(v_head_3473_);
lean_dec_ref_known(v_x_3467_, 2);
v___x_3474_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3473_);
v___x_3475_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3468_, v___x_3474_, v_tail_3470_);
return v___x_3475_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3484_ = lean_string_length(v___x_3483_);
return v___x_3484_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3486_ = lean_nat_to_int(v___x_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3492_){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3493_ = lean_array_get_size(v_xs_3492_);
v___x_3494_ = lean_unsigned_to_nat(0u);
v___x_3495_ = lean_nat_dec_eq(v___x_3493_, v___x_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3496_ = lean_array_to_list(v_xs_3492_);
v___x_3497_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3498_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3496_, v___x_3497_);
v___x_3499_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3500_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3501_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v___x_3498_);
v___x_3502_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3501_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3499_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = l_Std_Format_fill(v___x_3504_);
return v___x_3505_;
}
else
{
lean_object* v___x_3506_; 
lean_dec_ref(v_xs_3492_);
v___x_3506_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3507_, lean_object* v_x_3508_, lean_object* v_x_3509_){
_start:
{
if (lean_obj_tag(v_x_3509_) == 0)
{
lean_dec(v_x_3507_);
return v_x_3508_;
}
else
{
lean_object* v_head_3510_; lean_object* v_tail_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3521_; 
v_head_3510_ = lean_ctor_get(v_x_3509_, 0);
v_tail_3511_ = lean_ctor_get(v_x_3509_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_x_3509_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3513_ = v_x_3509_;
v_isShared_3514_ = v_isSharedCheck_3521_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_tail_3511_);
lean_inc(v_head_3510_);
lean_dec(v_x_3509_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3521_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
lean_inc(v_x_3507_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set_tag(v___x_3513_, 5);
lean_ctor_set(v___x_3513_, 1, v_x_3507_);
lean_ctor_set(v___x_3513_, 0, v_x_3508_);
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_x_3508_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_x_3507_);
v___x_3516_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3510_);
v___x_3518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3516_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v_x_3508_ = v___x_3518_;
v_x_3509_ = v_tail_3511_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3522_, lean_object* v_x_3523_){
_start:
{
if (lean_obj_tag(v_x_3522_) == 0)
{
lean_object* v___x_3524_; 
lean_dec(v_x_3523_);
v___x_3524_ = lean_box(0);
return v___x_3524_;
}
else
{
lean_object* v_tail_3525_; 
v_tail_3525_ = lean_ctor_get(v_x_3522_, 1);
if (lean_obj_tag(v_tail_3525_) == 0)
{
lean_object* v_head_3526_; lean_object* v___x_3527_; 
lean_dec(v_x_3523_);
v_head_3526_ = lean_ctor_get(v_x_3522_, 0);
lean_inc(v_head_3526_);
lean_dec_ref_known(v_x_3522_, 2);
v___x_3527_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3526_);
return v___x_3527_;
}
else
{
lean_object* v_head_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_inc(v_tail_3525_);
v_head_3528_ = lean_ctor_get(v_x_3522_, 0);
lean_inc(v_head_3528_);
lean_dec_ref_known(v_x_3522_, 2);
v___x_3529_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3528_);
v___x_3530_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3523_, v___x_3529_, v_tail_3525_);
return v___x_3530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3531_){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v___x_3532_ = lean_array_get_size(v_xs_3531_);
v___x_3533_ = lean_unsigned_to_nat(0u);
v___x_3534_ = lean_nat_dec_eq(v___x_3532_, v___x_3533_);
if (v___x_3534_ == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3535_ = lean_array_to_list(v_xs_3531_);
v___x_3536_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3537_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3535_, v___x_3536_);
v___x_3538_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3539_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
lean_ctor_set(v___x_3540_, 1, v___x_3537_);
v___x_3541_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3538_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = l_Std_Format_fill(v___x_3543_);
return v___x_3544_;
}
else
{
lean_object* v___x_3545_; 
lean_dec_ref(v_xs_3531_);
v___x_3545_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3545_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3546_, lean_object* v_x_3547_, lean_object* v_x_3548_){
_start:
{
if (lean_obj_tag(v_x_3548_) == 0)
{
lean_dec(v_x_3546_);
return v_x_3547_;
}
else
{
lean_object* v_head_3549_; lean_object* v_tail_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3561_; 
v_head_3549_ = lean_ctor_get(v_x_3548_, 0);
v_tail_3550_ = lean_ctor_get(v_x_3548_, 1);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_x_3548_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3552_ = v_x_3548_;
v_isShared_3553_ = v_isSharedCheck_3561_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_tail_3550_);
lean_inc(v_head_3549_);
lean_dec(v_x_3548_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3561_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3555_; 
lean_inc(v_x_3546_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set_tag(v___x_3552_, 5);
lean_ctor_set(v___x_3552_, 1, v_x_3546_);
lean_ctor_set(v___x_3552_, 0, v_x_3547_);
v___x_3555_ = v___x_3552_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_x_3547_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_x_3546_);
v___x_3555_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3556_ = l_Nat_reprFast(v_head_3549_);
v___x_3557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
v___x_3558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3555_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v_x_3547_ = v___x_3558_;
v_x_3548_ = v_tail_3550_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3562_, lean_object* v_x_3563_, lean_object* v_x_3564_){
_start:
{
if (lean_obj_tag(v_x_3564_) == 0)
{
lean_dec(v_x_3562_);
return v_x_3563_;
}
else
{
lean_object* v_head_3565_; lean_object* v_tail_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3577_; 
v_head_3565_ = lean_ctor_get(v_x_3564_, 0);
v_tail_3566_ = lean_ctor_get(v_x_3564_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_x_3564_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3568_ = v_x_3564_;
v_isShared_3569_ = v_isSharedCheck_3577_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_tail_3566_);
lean_inc(v_head_3565_);
lean_dec(v_x_3564_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3577_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
lean_inc(v_x_3562_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set_tag(v___x_3568_, 5);
lean_ctor_set(v___x_3568_, 1, v_x_3562_);
lean_ctor_set(v___x_3568_, 0, v_x_3563_);
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_x_3563_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_x_3562_);
v___x_3571_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3572_ = l_Nat_reprFast(v_head_3565_);
v___x_3573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
v___x_3574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3571_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3562_, v___x_3574_, v_tail_3566_);
return v___x_3575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = l_Nat_reprFast(v___y_3578_);
v___x_3580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3581_, lean_object* v_x_3582_){
_start:
{
if (lean_obj_tag(v_x_3581_) == 0)
{
lean_object* v___x_3583_; 
lean_dec(v_x_3582_);
v___x_3583_ = lean_box(0);
return v___x_3583_;
}
else
{
lean_object* v_tail_3584_; 
v_tail_3584_ = lean_ctor_get(v_x_3581_, 1);
if (lean_obj_tag(v_tail_3584_) == 0)
{
lean_object* v_head_3585_; lean_object* v___x_3586_; 
lean_dec(v_x_3582_);
v_head_3585_ = lean_ctor_get(v_x_3581_, 0);
lean_inc(v_head_3585_);
lean_dec_ref_known(v_x_3581_, 2);
v___x_3586_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3585_);
return v___x_3586_;
}
else
{
lean_object* v_head_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_inc(v_tail_3584_);
v_head_3587_ = lean_ctor_get(v_x_3581_, 0);
lean_inc(v_head_3587_);
lean_dec_ref_known(v_x_3581_, 2);
v___x_3588_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3587_);
v___x_3589_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3582_, v___x_3588_, v_tail_3584_);
return v___x_3589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3590_){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3591_ = lean_array_get_size(v_xs_3590_);
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3593_ = lean_nat_dec_eq(v___x_3591_, v___x_3592_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3594_ = lean_array_to_list(v_xs_3590_);
v___x_3595_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3596_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3594_, v___x_3595_);
v___x_3597_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3598_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
lean_ctor_set(v___x_3599_, 1, v___x_3596_);
v___x_3600_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3597_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = l_Std_Format_fill(v___x_3602_);
return v___x_3603_;
}
else
{
lean_object* v___x_3604_; 
lean_dec_ref(v_xs_3590_);
v___x_3604_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3604_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3605_, lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
if (lean_obj_tag(v_x_3607_) == 0)
{
lean_dec(v_x_3605_);
return v_x_3606_;
}
else
{
lean_object* v_head_3608_; lean_object* v_tail_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3619_; 
v_head_3608_ = lean_ctor_get(v_x_3607_, 0);
v_tail_3609_ = lean_ctor_get(v_x_3607_, 1);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_x_3607_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3611_ = v_x_3607_;
v_isShared_3612_ = v_isSharedCheck_3619_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_tail_3609_);
lean_inc(v_head_3608_);
lean_dec(v_x_3607_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3619_;
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
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_x_3606_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_x_3605_);
v___x_3614_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3608_);
v___x_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v_x_3606_ = v___x_3616_;
v_x_3607_ = v_tail_3609_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
if (lean_obj_tag(v_x_3620_) == 0)
{
lean_object* v___x_3622_; 
lean_dec(v_x_3621_);
v___x_3622_ = lean_box(0);
return v___x_3622_;
}
else
{
lean_object* v_tail_3623_; 
v_tail_3623_ = lean_ctor_get(v_x_3620_, 1);
if (lean_obj_tag(v_tail_3623_) == 0)
{
lean_object* v_head_3624_; lean_object* v___x_3625_; 
lean_dec(v_x_3621_);
v_head_3624_ = lean_ctor_get(v_x_3620_, 0);
lean_inc(v_head_3624_);
lean_dec_ref_known(v_x_3620_, 2);
v___x_3625_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3624_);
return v___x_3625_;
}
else
{
lean_object* v_head_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
lean_inc(v_tail_3623_);
v_head_3626_ = lean_ctor_get(v_x_3620_, 0);
lean_inc(v_head_3626_);
lean_dec_ref_known(v_x_3620_, 2);
v___x_3627_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3626_);
v___x_3628_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3621_, v___x_3627_, v_tail_3623_);
return v___x_3628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3629_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3630_ = lean_array_get_size(v_xs_3629_);
v___x_3631_ = lean_unsigned_to_nat(0u);
v___x_3632_ = lean_nat_dec_eq(v___x_3630_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3633_ = lean_array_to_list(v_xs_3629_);
v___x_3634_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3635_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3633_, v___x_3634_);
v___x_3636_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3637_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
lean_ctor_set(v___x_3638_, 1, v___x_3635_);
v___x_3639_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3638_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3636_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = l_Std_Format_fill(v___x_3641_);
return v___x_3642_;
}
else
{
lean_object* v___x_3643_; 
lean_dec_ref(v_xs_3629_);
v___x_3643_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3643_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3644_, lean_object* v_x_3645_, lean_object* v_x_3646_){
_start:
{
if (lean_obj_tag(v_x_3646_) == 0)
{
lean_dec(v_x_3644_);
return v_x_3645_;
}
else
{
lean_object* v_head_3647_; lean_object* v_tail_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3658_; 
v_head_3647_ = lean_ctor_get(v_x_3646_, 0);
v_tail_3648_ = lean_ctor_get(v_x_3646_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_x_3646_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3650_ = v_x_3646_;
v_isShared_3651_ = v_isSharedCheck_3658_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_tail_3648_);
lean_inc(v_head_3647_);
lean_dec(v_x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3658_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
lean_inc(v_x_3644_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 5);
lean_ctor_set(v___x_3650_, 1, v_x_3644_);
lean_ctor_set(v___x_3650_, 0, v_x_3645_);
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_x_3645_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_x_3644_);
v___x_3653_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3647_);
v___x_3655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v_x_3645_ = v___x_3655_;
v_x_3646_ = v_tail_3648_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3659_, lean_object* v_x_3660_){
_start:
{
if (lean_obj_tag(v_x_3659_) == 0)
{
lean_object* v___x_3661_; 
lean_dec(v_x_3660_);
v___x_3661_ = lean_box(0);
return v___x_3661_;
}
else
{
lean_object* v_tail_3662_; 
v_tail_3662_ = lean_ctor_get(v_x_3659_, 1);
if (lean_obj_tag(v_tail_3662_) == 0)
{
lean_object* v_head_3663_; lean_object* v___x_3664_; 
lean_dec(v_x_3660_);
v_head_3663_ = lean_ctor_get(v_x_3659_, 0);
lean_inc(v_head_3663_);
lean_dec_ref_known(v_x_3659_, 2);
v___x_3664_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3663_);
return v___x_3664_;
}
else
{
lean_object* v_head_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_inc(v_tail_3662_);
v_head_3665_ = lean_ctor_get(v_x_3659_, 0);
lean_inc(v_head_3665_);
lean_dec_ref_known(v_x_3659_, 2);
v___x_3666_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3665_);
v___x_3667_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3660_, v___x_3666_, v_tail_3662_);
return v___x_3667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3668_){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3669_ = lean_array_get_size(v_xs_3668_);
v___x_3670_ = lean_unsigned_to_nat(0u);
v___x_3671_ = lean_nat_dec_eq(v___x_3669_, v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3672_ = lean_array_to_list(v_xs_3668_);
v___x_3673_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3674_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3672_, v___x_3673_);
v___x_3675_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3676_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
lean_ctor_set(v___x_3677_, 1, v___x_3674_);
v___x_3678_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3675_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = l_Std_Format_fill(v___x_3680_);
return v___x_3681_;
}
else
{
lean_object* v___x_3682_; 
lean_dec_ref(v_xs_3668_);
v___x_3682_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3682_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = lean_unsigned_to_nat(12u);
v___x_3697_ = lean_nat_to_int(v___x_3696_);
return v___x_3697_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = lean_unsigned_to_nat(9u);
v___x_3702_ = lean_nat_to_int(v___x_3701_);
return v___x_3702_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = lean_unsigned_to_nat(11u);
v___x_3707_ = lean_nat_to_int(v___x_3706_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3710_ = lean_string_length(v___x_3709_);
return v___x_3710_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3712_ = lean_nat_to_int(v___x_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3717_){
_start:
{
lean_object* v_numFixed_3718_; lean_object* v_perms_3719_; lean_object* v_revDeps_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_numFixed_3718_ = lean_ctor_get(v_x_3717_, 0);
lean_inc(v_numFixed_3718_);
v_perms_3719_ = lean_ctor_get(v_x_3717_, 1);
lean_inc_ref(v_perms_3719_);
v_revDeps_3720_ = lean_ctor_get(v_x_3717_, 2);
lean_inc_ref(v_revDeps_3720_);
lean_dec_ref(v_x_3717_);
v___x_3721_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3722_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3723_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3724_ = l_Nat_reprFast(v_numFixed_3718_);
v___x_3725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3723_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = 0;
v___x_3728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set_uint8(v___x_3728_, sizeof(void*)*1, v___x_3727_);
v___x_3729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3722_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = lean_box(1);
v___x_3733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v___x_3721_);
v___x_3737_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3738_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3719_);
v___x_3739_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
lean_ctor_set_uint8(v___x_3740_, sizeof(void*)*1, v___x_3727_);
v___x_3741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3736_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set(v___x_3742_, 1, v___x_3730_);
v___x_3743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
lean_ctor_set(v___x_3743_, 1, v___x_3732_);
v___x_3744_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3743_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v___x_3721_);
v___x_3747_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3748_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3720_);
v___x_3749_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
lean_ctor_set_uint8(v___x_3750_, sizeof(void*)*1, v___x_3727_);
v___x_3751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3746_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3753_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
lean_ctor_set(v___x_3754_, 1, v___x_3751_);
v___x_3755_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3752_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*1, v___x_3727_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3759_, lean_object* v_prec_3760_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3759_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3762_, lean_object* v_prec_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3762_, v_prec_3763_);
lean_dec(v_prec_3763_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___f_3773_; lean_object* v___x_5728__overap_3774_; lean_object* v___x_3775_; 
v___f_3773_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5728__overap_3774_ = lean_panic_fn_borrowed(v___f_3773_, v_msg_3767_);
lean_inc(v___y_3771_);
lean_inc_ref(v___y_3770_);
lean_inc(v___y_3769_);
lean_inc_ref(v___y_3768_);
v___x_3775_ = lean_apply_5(v___x_5728__overap_3774_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, lean_box(0));
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___f_3789_; lean_object* v___x_5738__overap_3790_; lean_object* v___x_3791_; 
v___f_3789_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5738__overap_3790_ = lean_panic_fn_borrowed(v___f_3789_, v_msg_3783_);
lean_inc(v___y_3787_);
lean_inc_ref(v___y_3786_);
lean_inc(v___y_3785_);
lean_inc_ref(v___y_3784_);
v___x_3791_ = lean_apply_5(v___x_5738__overap_3790_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, lean_box(0));
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___f_3805_; lean_object* v___x_5748__overap_3806_; lean_object* v___x_3807_; 
v___f_3805_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5748__overap_3806_ = lean_panic_fn_borrowed(v___f_3805_, v_msg_3799_);
lean_inc(v___y_3803_);
lean_inc_ref(v___y_3802_);
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
v___x_3807_ = lean_apply_5(v___x_5748__overap_3806_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, lean_box(0));
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
return v_res_3814_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3818_ = lean_unsigned_to_nat(12u);
v___x_3819_ = lean_unsigned_to_nat(294u);
v___x_3820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3821_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3822_ = l_mkPanicMessageWithDecl(v___x_3821_, v___x_3820_, v___x_3819_, v___x_3818_, v___x_3817_);
return v___x_3822_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3825_ = lean_unsigned_to_nat(12u);
v___x_3826_ = lean_unsigned_to_nat(297u);
v___x_3827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3828_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3829_ = l_mkPanicMessageWithDecl(v___x_3828_, v___x_3827_, v___x_3826_, v___x_3825_, v___x_3824_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3830_, lean_object* v_as_3831_, size_t v_sz_3832_, size_t v_i_3833_, lean_object* v_b_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_a_3841_; uint8_t v___x_3845_; 
v___x_3845_ = lean_usize_dec_lt(v_i_3833_, v_sz_3832_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v_b_3834_);
return v___x_3846_;
}
else
{
lean_object* v_a_3847_; 
v_a_3847_ = lean_array_uget_borrowed(v_as_3831_, v_i_3833_);
if (lean_obj_tag(v_a_3847_) == 1)
{
lean_object* v_val_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v_val_3848_ = lean_ctor_get(v_a_3847_, 0);
v___x_3849_ = lean_box(0);
v___x_3850_ = lean_unsigned_to_nat(0u);
v___x_3851_ = lean_array_get_borrowed(v___x_3849_, v_val_3848_, v___x_3850_);
if (lean_obj_tag(v___x_3851_) == 1)
{
lean_object* v_val_3852_; lean_object* v___x_3853_; 
v_val_3852_ = lean_ctor_get(v___x_3851_, 0);
v___x_3853_ = lean_array_get_borrowed(v___x_3849_, v___x_3830_, v_val_3852_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec_ref(v_b_3834_);
v___x_3854_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3855_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3854_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3865_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3858_ = v___x_3855_;
v_isShared_3859_ = v_isSharedCheck_3865_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3865_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
if (lean_obj_tag(v_a_3856_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; 
v_a_3860_ = lean_ctor_get(v_a_3856_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v_a_3856_, 1);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v_a_3860_);
v___x_3862_ = v___x_3858_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
else
{
lean_object* v_a_3864_; 
lean_del_object(v___x_3858_);
v_a_3864_ = lean_ctor_get(v_a_3856_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v_a_3856_, 1);
v_a_3841_ = v_a_3864_;
goto v___jp_3840_;
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
v_a_3866_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3855_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3855_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v___x_3874_; 
lean_inc_ref(v___x_3853_);
v___x_3874_ = lean_array_push(v_b_3834_, v___x_3853_);
v_a_3841_ = v___x_3874_;
goto v___jp_3840_;
}
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3876_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3875_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_dec_ref_known(v___x_3876_, 1);
v_a_3841_ = v_b_3834_;
goto v___jp_3840_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v_b_3834_);
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3876_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3876_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_box(0);
v___x_3886_ = lean_array_push(v_b_3834_, v___x_3885_);
v_a_3841_ = v___x_3886_;
goto v___jp_3840_;
}
}
v___jp_3840_:
{
size_t v___x_3842_; size_t v___x_3843_; 
v___x_3842_ = ((size_t)1ULL);
v___x_3843_ = lean_usize_add(v_i_3833_, v___x_3842_);
v_i_3833_ = v___x_3843_;
v_b_3834_ = v_a_3841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3887_, lean_object* v_as_3888_, lean_object* v_sz_3889_, lean_object* v_i_3890_, lean_object* v_b_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
size_t v_sz_boxed_3897_; size_t v_i_boxed_3898_; lean_object* v_res_3899_; 
v_sz_boxed_3897_ = lean_unbox_usize(v_sz_3889_);
lean_dec(v_sz_3889_);
v_i_boxed_3898_ = lean_unbox_usize(v_i_3890_);
lean_dec(v_i_3890_);
v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3887_, v_as_3888_, v_sz_boxed_3897_, v_i_boxed_3898_, v_b_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec_ref(v_as_3888_);
lean_dec_ref(v___x_3887_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3902_, lean_object* v___x_3903_, lean_object* v___x_3904_, lean_object* v_a_3905_, lean_object* v_b_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
uint8_t v___x_3912_; 
v___x_3912_ = lean_nat_dec_lt(v_a_3905_, v_upperBound_3902_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; 
lean_dec(v_a_3905_);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v_b_3906_);
return v___x_3913_;
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3915_; size_t v_sz_3916_; size_t v___x_3917_; lean_object* v___x_3918_; 
v___x_3914_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3915_ = lean_array_fget_borrowed(v___x_3903_, v_a_3905_);
v_sz_3916_ = lean_array_size(v___x_3915_);
v___x_3917_ = ((size_t)0ULL);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3904_, v___x_3915_, v_sz_3916_, v___x_3917_, v___x_3914_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = lean_array_push(v_b_3906_, v_a_3919_);
v___x_3921_ = lean_unsigned_to_nat(1u);
v___x_3922_ = lean_nat_add(v_a_3905_, v___x_3921_);
lean_dec(v_a_3905_);
v_a_3905_ = v___x_3922_;
v_b_3906_ = v___x_3920_;
goto _start;
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref(v_b_3906_);
lean_dec(v_a_3905_);
v_a_3924_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3918_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3918_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3932_, lean_object* v___x_3933_, lean_object* v___x_3934_, lean_object* v_a_3935_, lean_object* v_b_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3932_, v___x_3933_, v___x_3934_, v_a_3935_, v_b_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec_ref(v___x_3934_);
lean_dec_ref(v___x_3933_);
lean_dec(v_upperBound_3932_);
return v_res_3942_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3944_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3945_ = lean_unsigned_to_nat(8u);
v___x_3946_ = lean_unsigned_to_nat(281u);
v___x_3947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3949_ = l_mkPanicMessageWithDecl(v___x_3948_, v___x_3947_, v___x_3946_, v___x_3945_, v___x_3944_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3950_, lean_object* v_a_3951_, lean_object* v_b_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_a_3959_; uint8_t v___x_3963_; 
v___x_3963_ = lean_nat_dec_lt(v_a_3951_, v_upperBound_3950_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; 
lean_dec(v_a_3951_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v_b_3952_);
return v___x_3964_;
}
else
{
lean_object* v_snd_3965_; lean_object* v_snd_3966_; lean_object* v_snd_3967_; lean_object* v_fst_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_4092_; 
v_snd_3965_ = lean_ctor_get(v_b_3952_, 1);
lean_inc(v_snd_3965_);
v_snd_3966_ = lean_ctor_get(v_snd_3965_, 1);
lean_inc(v_snd_3966_);
v_snd_3967_ = lean_ctor_get(v_snd_3966_, 1);
lean_inc(v_snd_3967_);
v_fst_3968_ = lean_ctor_get(v_b_3952_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_b_3952_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v_b_3952_, 1);
lean_dec(v_unused_4093_);
v___x_3970_ = v_b_3952_;
v_isShared_3971_ = v_isSharedCheck_4092_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_fst_3968_);
lean_dec(v_b_3952_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_4092_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v_fst_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4090_; 
v_fst_3972_ = lean_ctor_get(v_snd_3965_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_snd_3965_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v_snd_3965_, 1);
lean_dec(v_unused_4091_);
v___x_3974_ = v_snd_3965_;
v_isShared_3975_ = v_isSharedCheck_4090_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_fst_3972_);
lean_dec(v_snd_3965_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4090_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v_fst_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_4088_; 
v_fst_3976_ = lean_ctor_get(v_snd_3966_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_snd_3966_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; 
v_unused_4089_ = lean_ctor_get(v_snd_3966_, 1);
lean_dec(v_unused_4089_);
v___x_3978_ = v_snd_3966_;
v_isShared_3979_ = v_isSharedCheck_4088_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_fst_3976_);
lean_dec(v_snd_3966_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_4088_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v_array_3980_; lean_object* v_start_3981_; lean_object* v_stop_3982_; uint8_t v___x_3983_; 
v_array_3980_ = lean_ctor_get(v_snd_3967_, 0);
v_start_3981_ = lean_ctor_get(v_snd_3967_, 1);
v_stop_3982_ = lean_ctor_get(v_snd_3967_, 2);
v___x_3983_ = lean_nat_dec_lt(v_start_3981_, v_stop_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3985_; 
lean_dec(v_a_3951_);
if (v_isShared_3979_ == 0)
{
v___x_3985_ = v___x_3978_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_fst_3976_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_snd_3967_);
v___x_3985_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3987_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_3985_);
v___x_3987_ = v___x_3974_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_fst_3972_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3989_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 1, v___x_3987_);
v___x_3989_ = v___x_3970_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_fst_3968_);
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
lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4084_; 
lean_inc(v_stop_3982_);
lean_inc(v_start_3981_);
lean_inc_ref(v_array_3980_);
v_isSharedCheck_4084_ = !lean_is_exclusive(v_snd_3967_);
if (v_isSharedCheck_4084_ == 0)
{
lean_object* v_unused_4085_; lean_object* v_unused_4086_; lean_object* v_unused_4087_; 
v_unused_4085_ = lean_ctor_get(v_snd_3967_, 2);
lean_dec(v_unused_4085_);
v_unused_4086_ = lean_ctor_get(v_snd_3967_, 1);
lean_dec(v_unused_4086_);
v_unused_4087_ = lean_ctor_get(v_snd_3967_, 0);
lean_dec(v_unused_4087_);
v___x_3995_ = v_snd_3967_;
v_isShared_3996_ = v_isSharedCheck_4084_;
goto v_resetjp_3994_;
}
else
{
lean_dec(v_snd_3967_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4084_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v_array_3997_; lean_object* v_start_3998_; lean_object* v_stop_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4004_; 
v_array_3997_ = lean_ctor_get(v_fst_3976_, 0);
v_start_3998_ = lean_ctor_get(v_fst_3976_, 1);
v_stop_3999_ = lean_ctor_get(v_fst_3976_, 2);
v___x_4000_ = lean_array_fget(v_array_3980_, v_start_3981_);
v___x_4001_ = lean_unsigned_to_nat(1u);
v___x_4002_ = lean_nat_add(v_start_3981_, v___x_4001_);
lean_dec(v_start_3981_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 1, v___x_4002_);
v___x_4004_ = v___x_3995_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_array_3980_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4002_);
lean_ctor_set(v_reuseFailAlloc_4083_, 2, v_stop_3982_);
v___x_4004_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
uint8_t v___x_4005_; 
v___x_4005_ = lean_nat_dec_lt(v_start_3998_, v_stop_3999_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4007_; 
lean_dec(v___x_4000_);
lean_dec(v_a_3951_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_4004_);
v___x_4007_ = v___x_3978_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_fst_3976_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v___x_4004_);
v___x_4007_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4009_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_4007_);
v___x_4009_ = v___x_3974_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_fst_3972_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4011_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 1, v___x_4009_);
v___x_4011_ = v___x_3970_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_fst_3968_);
lean_ctor_set(v_reuseFailAlloc_4013_, 1, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4012_; 
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
return v___x_4012_;
}
}
}
}
else
{
lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4079_; 
lean_inc(v_stop_3999_);
lean_inc(v_start_3998_);
lean_inc_ref(v_array_3997_);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_fst_3976_);
if (v_isSharedCheck_4079_ == 0)
{
lean_object* v_unused_4080_; lean_object* v_unused_4081_; lean_object* v_unused_4082_; 
v_unused_4080_ = lean_ctor_get(v_fst_3976_, 2);
lean_dec(v_unused_4080_);
v_unused_4081_ = lean_ctor_get(v_fst_3976_, 1);
lean_dec(v_unused_4081_);
v_unused_4082_ = lean_ctor_get(v_fst_3976_, 0);
lean_dec(v_unused_4082_);
v___x_4017_ = v_fst_3976_;
v_isShared_4018_ = v_isSharedCheck_4079_;
goto v_resetjp_4016_;
}
else
{
lean_dec(v_fst_3976_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4079_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4019_ = lean_nat_add(v_start_3998_, v___x_4001_);
lean_dec(v_start_3998_);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v___x_4019_);
v___x_4021_ = v___x_4017_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_array_3997_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4078_, 2, v_stop_3999_);
v___x_4021_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
if (lean_obj_tag(v___x_4000_) == 1)
{
lean_object* v_val_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4066_; 
v_val_4022_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4024_ = v___x_4000_;
v_isShared_4025_ = v_isSharedCheck_4066_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_val_4022_);
lean_dec(v___x_4000_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4066_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4031_; 
v___x_4026_ = lean_box(0);
v___x_4027_ = lean_unsigned_to_nat(0u);
v___x_4028_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4029_ = lean_array_get(v___x_4026_, v_val_4022_, v___x_4027_);
lean_dec(v_val_4022_);
lean_inc(v_a_3951_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v_a_3951_);
v___x_4031_ = v___x_4024_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_3951_);
v___x_4031_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
uint8_t v___x_4032_; 
v___x_4032_ = l_Option_instDecidableEq___redArg(v___x_4028_, v___x_4029_, v___x_4031_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
lean_dec_ref(v___x_4021_);
lean_dec_ref(v___x_4004_);
lean_del_object(v___x_3978_);
lean_del_object(v___x_3974_);
lean_dec(v_fst_3972_);
lean_del_object(v___x_3970_);
lean_dec(v_fst_3968_);
v___x_4033_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4034_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4033_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4044_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4037_ = v___x_4034_;
v_isShared_4038_ = v_isSharedCheck_4044_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4034_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4044_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
if (lean_obj_tag(v_a_4035_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4041_; 
lean_dec(v_a_3951_);
v_a_4039_ = lean_ctor_get(v_a_4035_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v_a_4035_, 1);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v_a_4039_);
v___x_4041_ = v___x_4037_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4039_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
else
{
lean_object* v_a_4043_; 
lean_del_object(v___x_4037_);
v_a_4043_ = lean_ctor_get(v_a_4035_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v_a_4035_, 1);
v_a_3959_ = v_a_4043_;
goto v___jp_3958_;
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v_a_3951_);
v_a_4045_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4034_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4034_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
lean_inc(v_fst_3972_);
v___x_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4053_, 0, v_fst_3972_);
v___x_4054_ = lean_array_push(v_fst_3968_, v___x_4053_);
v___x_4055_ = lean_nat_add(v_fst_3972_, v___x_4001_);
lean_dec(v_fst_3972_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_4004_);
lean_ctor_set(v___x_3978_, 0, v___x_4021_);
v___x_4057_ = v___x_3978_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4004_);
v___x_4057_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
lean_object* v___x_4059_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_4057_);
lean_ctor_set(v___x_3974_, 0, v___x_4055_);
v___x_4059_ = v___x_3974_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4055_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4061_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 1, v___x_4059_);
lean_ctor_set(v___x_3970_, 0, v___x_4054_);
v___x_4061_ = v___x_3970_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
v_a_3959_ = v___x_4061_;
goto v___jp_3958_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
lean_dec(v___x_4000_);
v___x_4067_ = lean_box(0);
v___x_4068_ = lean_array_push(v_fst_3968_, v___x_4067_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_4004_);
lean_ctor_set(v___x_3978_, 0, v___x_4021_);
v___x_4070_ = v___x_3978_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4004_);
v___x_4070_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4072_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_4070_);
v___x_4072_ = v___x_3974_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_fst_3972_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4074_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 1, v___x_4072_);
lean_ctor_set(v___x_3970_, 0, v___x_4068_);
v___x_4074_ = v___x_3970_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
v_a_3959_ = v___x_4074_;
goto v___jp_3958_;
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
v___jp_3958_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_unsigned_to_nat(1u);
v___x_3961_ = lean_nat_add(v_a_3951_, v___x_3960_);
lean_dec(v_a_3951_);
v_a_3951_ = v___x_3961_;
v_b_3952_ = v_a_3959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4094_, lean_object* v_a_4095_, lean_object* v_b_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4094_, v_a_4095_, v_b_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v_upperBound_4094_);
return v_res_4102_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4104_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4105_ = lean_unsigned_to_nat(4u);
v___x_4106_ = lean_unsigned_to_nat(275u);
v___x_4107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4108_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4109_ = l_mkPanicMessageWithDecl(v___x_4108_, v___x_4107_, v___x_4106_, v___x_4105_, v___x_4104_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4110_, lean_object* v___x_4111_, lean_object* v___x_4112_, lean_object* v_xs_4113_, lean_object* v_x_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_graph_4120_; lean_object* v_revDeps_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4174_; 
v_graph_4120_ = lean_ctor_get(v_a_4110_, 0);
v_revDeps_4121_ = lean_ctor_get(v_a_4110_, 1);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_a_4110_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4123_ = v_a_4110_;
v_isShared_4124_ = v_isSharedCheck_4174_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_revDeps_4121_);
lean_inc(v_graph_4120_);
lean_dec(v_a_4110_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4174_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
v___x_4125_ = lean_array_get_borrowed(v___x_4111_, v_graph_4120_, v___x_4112_);
v___x_4126_ = lean_array_get_size(v_xs_4113_);
v___x_4127_ = lean_array_get_size(v___x_4125_);
v___x_4128_ = lean_nat_dec_eq(v___x_4126_, v___x_4127_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_del_object(v___x_4123_);
lean_dec_ref(v_revDeps_4121_);
lean_dec_ref(v_graph_4120_);
lean_dec_ref(v_xs_4113_);
lean_dec(v___x_4112_);
v___x_4129_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4130_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4129_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
return v___x_4130_;
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4131_ = lean_mk_empty_array_with_capacity(v___x_4112_);
lean_inc_n(v___x_4112_, 2);
v___x_4132_ = l_Array_toSubarray___redArg(v_xs_4113_, v___x_4112_, v___x_4126_);
lean_inc(v___x_4125_);
v___x_4133_ = l_Array_toSubarray___redArg(v___x_4125_, v___x_4112_, v___x_4127_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 1, v___x_4133_);
lean_ctor_set(v___x_4123_, 0, v___x_4132_);
v___x_4135_ = v___x_4123_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4132_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_inc(v___x_4112_);
v___x_4136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4112_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4131_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4126_, v___x_4112_, v___x_4137_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v_snd_4140_; lean_object* v_fst_4141_; lean_object* v_fst_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v_snd_4140_ = lean_ctor_get(v_a_4139_, 1);
lean_inc(v_snd_4140_);
v_fst_4141_ = lean_ctor_get(v_a_4139_, 0);
lean_inc_n(v_fst_4141_, 2);
lean_dec(v_a_4139_);
v_fst_4142_ = lean_ctor_get(v_snd_4140_, 0);
lean_inc(v_fst_4142_);
lean_dec(v_snd_4140_);
v___x_4143_ = lean_unsigned_to_nat(1u);
v___x_4144_ = lean_array_get_size(v_graph_4120_);
v___x_4145_ = lean_mk_empty_array_with_capacity(v___x_4143_);
v___x_4146_ = lean_array_push(v___x_4145_, v_fst_4141_);
v___x_4147_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4144_, v_graph_4120_, v_fst_4141_, v___x_4143_, v___x_4146_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v_fst_4141_);
lean_dec_ref(v_graph_4120_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4156_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4150_ = v___x_4147_;
v_isShared_4151_ = v_isSharedCheck_4156_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4156_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4152_; lean_object* v___x_4154_; 
v___x_4152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4152_, 0, v_fst_4142_);
lean_ctor_set(v___x_4152_, 1, v_a_4148_);
lean_ctor_set(v___x_4152_, 2, v_revDeps_4121_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 0, v___x_4152_);
v___x_4154_ = v___x_4150_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4152_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec(v_fst_4142_);
lean_dec_ref(v_revDeps_4121_);
v_a_4157_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4147_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4147_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec_ref(v_revDeps_4121_);
lean_dec_ref(v_graph_4120_);
v_a_4165_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4138_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4138_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4175_, lean_object* v___x_4176_, lean_object* v___x_4177_, lean_object* v_xs_4178_, lean_object* v_x_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4175_, v___x_4176_, v___x_4177_, v_xs_4178_, v_x_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec_ref(v_x_4179_);
lean_dec_ref(v___x_4176_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v___x_4192_; 
lean_inc_ref(v_preDefs_4186_);
v___x_4192_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v_value_4197_; lean_object* v___x_4198_; lean_object* v___f_4199_; uint8_t v___x_4200_; lean_object* v___x_4201_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4192_, 1);
v___x_4194_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4195_ = lean_unsigned_to_nat(0u);
v___x_4196_ = lean_array_get(v___x_4194_, v_preDefs_4186_, v___x_4195_);
lean_dec_ref(v_preDefs_4186_);
v_value_4197_ = lean_ctor_get(v___x_4196_, 7);
lean_inc_ref(v_value_4197_);
lean_dec(v___x_4196_);
v___x_4198_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4199_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4199_, 0, v_a_4193_);
lean_closure_set(v___f_4199_, 1, v___x_4198_);
lean_closure_set(v___f_4199_, 2, v___x_4195_);
v___x_4200_ = 0;
v___x_4201_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4197_, v___f_4199_, v___x_4200_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
return v___x_4201_;
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v_preDefs_4186_);
v_a_4202_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4192_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4192_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4217_, lean_object* v___x_4218_, lean_object* v___x_4219_, lean_object* v_inst_4220_, lean_object* v_R_4221_, lean_object* v_a_4222_, lean_object* v_b_4223_, lean_object* v_c_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4217_, v___x_4218_, v___x_4219_, v_a_4222_, v_b_4223_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4231_, lean_object* v___x_4232_, lean_object* v___x_4233_, lean_object* v_inst_4234_, lean_object* v_R_4235_, lean_object* v_a_4236_, lean_object* v_b_4237_, lean_object* v_c_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4231_, v___x_4232_, v___x_4233_, v_inst_4234_, v_R_4235_, v_a_4236_, v_b_4237_, v_c_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec_ref(v___x_4233_);
lean_dec_ref(v___x_4232_);
lean_dec(v_upperBound_4231_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4245_, lean_object* v_inst_4246_, lean_object* v_R_4247_, lean_object* v_a_4248_, lean_object* v_b_4249_, lean_object* v_c_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4245_, v_a_4248_, v_b_4249_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4257_, lean_object* v_inst_4258_, lean_object* v_R_4259_, lean_object* v_a_4260_, lean_object* v_b_4261_, lean_object* v_c_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4257_, v_inst_4258_, v_R_4259_, v_a_4260_, v_b_4261_, v_c_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v_upperBound_4257_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4269_, size_t v_i_4270_, size_t v_stop_4271_, lean_object* v_b_4272_){
_start:
{
uint8_t v___x_4273_; 
v___x_4273_ = lean_usize_dec_eq(v_i_4270_, v_stop_4271_);
if (v___x_4273_ == 0)
{
size_t v___x_4274_; size_t v___x_4275_; lean_object* v___x_4276_; 
v___x_4274_ = ((size_t)1ULL);
v___x_4275_ = lean_usize_sub(v_i_4270_, v___x_4274_);
v___x_4276_ = lean_array_uget_borrowed(v_as_4269_, v___x_4275_);
if (lean_obj_tag(v___x_4276_) == 0)
{
v_i_4270_ = v___x_4275_;
goto _start;
}
else
{
lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4278_ = lean_unsigned_to_nat(1u);
v___x_4279_ = lean_nat_add(v_b_4272_, v___x_4278_);
lean_dec(v_b_4272_);
v_i_4270_ = v___x_4275_;
v_b_4272_ = v___x_4279_;
goto _start;
}
}
else
{
return v_b_4272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4281_, lean_object* v_i_4282_, lean_object* v_stop_4283_, lean_object* v_b_4284_){
_start:
{
size_t v_i_boxed_4285_; size_t v_stop_boxed_4286_; lean_object* v_res_4287_; 
v_i_boxed_4285_ = lean_unbox_usize(v_i_4282_);
lean_dec(v_i_4282_);
v_stop_boxed_4286_ = lean_unbox_usize(v_stop_4283_);
lean_dec(v_stop_4283_);
v_res_4287_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4281_, v_i_boxed_4285_, v_stop_boxed_4286_, v_b_4284_);
lean_dec_ref(v_as_4281_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4288_){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v___x_4289_ = lean_unsigned_to_nat(0u);
v___x_4290_ = lean_array_get_size(v_perm_4288_);
v___x_4291_ = lean_nat_dec_lt(v___x_4289_, v___x_4290_);
if (v___x_4291_ == 0)
{
return v___x_4289_;
}
else
{
size_t v___x_4292_; size_t v___x_4293_; lean_object* v___x_4294_; 
v___x_4292_ = lean_usize_of_nat(v___x_4290_);
v___x_4293_ = ((size_t)0ULL);
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4288_, v___x_4292_, v___x_4293_, v___x_4289_);
return v___x_4294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4295_);
lean_dec_ref(v_perm_4295_);
return v_res_4296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4297_, lean_object* v_i_4298_){
_start:
{
lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4299_ = lean_array_get_size(v_perm_4297_);
v___x_4300_ = lean_nat_dec_lt(v_i_4298_, v___x_4299_);
if (v___x_4300_ == 0)
{
return v___x_4300_;
}
else
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_array_fget_borrowed(v_perm_4297_, v_i_4298_);
if (lean_obj_tag(v___x_4301_) == 0)
{
uint8_t v___x_4302_; 
v___x_4302_ = 0;
return v___x_4302_;
}
else
{
return v___x_4300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4303_, lean_object* v_i_4304_){
_start:
{
uint8_t v_res_4305_; lean_object* v_r_4306_; 
v_res_4305_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4303_, v_i_4304_);
lean_dec(v_i_4304_);
lean_dec_ref(v_perm_4303_);
v_r_4306_ = lean_box(v_res_4305_);
return v_r_4306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___f_4313_; lean_object* v___x_907__overap_4314_; lean_object* v___x_4315_; 
v___f_4313_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_907__overap_4314_ = lean_panic_fn_borrowed(v___f_4313_, v_msg_4307_);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
lean_inc(v___y_4309_);
lean_inc_ref(v___y_4308_);
v___x_4315_ = lean_apply_5(v___x_907__overap_4314_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, lean_box(0));
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4323_, lean_object* v_msg_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4331_, lean_object* v_msg_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4331_, v_msg_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4339_, lean_object* v_maxFVars_x3f_4340_, lean_object* v_k_4341_, uint8_t v_cleanupAnnotations_4342_, uint8_t v_whnfType_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v___f_4349_; lean_object* v___x_4350_; 
v___f_4349_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4349_, 0, v_k_4341_);
v___x_4350_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4339_, v_maxFVars_x3f_4340_, v___f_4349_, v_cleanupAnnotations_4342_, v_whnfType_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
v_a_4359_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4350_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4350_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4367_, lean_object* v_maxFVars_x3f_4368_, lean_object* v_k_4369_, lean_object* v_cleanupAnnotations_4370_, lean_object* v_whnfType_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4377_; uint8_t v_whnfType_boxed_4378_; lean_object* v_res_4379_; 
v_cleanupAnnotations_boxed_4377_ = lean_unbox(v_cleanupAnnotations_4370_);
v_whnfType_boxed_4378_ = lean_unbox(v_whnfType_4371_);
v_res_4379_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4367_, v_maxFVars_x3f_4368_, v_k_4369_, v_cleanupAnnotations_boxed_4377_, v_whnfType_boxed_4378_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4380_, lean_object* v_type_4381_, lean_object* v_maxFVars_x3f_4382_, lean_object* v_k_4383_, uint8_t v_cleanupAnnotations_4384_, uint8_t v_whnfType_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4381_, v_maxFVars_x3f_4382_, v_k_4383_, v_cleanupAnnotations_4384_, v_whnfType_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4392_, lean_object* v_type_4393_, lean_object* v_maxFVars_x3f_4394_, lean_object* v_k_4395_, lean_object* v_cleanupAnnotations_4396_, lean_object* v_whnfType_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4403_; uint8_t v_whnfType_boxed_4404_; lean_object* v_res_4405_; 
v_cleanupAnnotations_boxed_4403_ = lean_unbox(v_cleanupAnnotations_4396_);
v_whnfType_boxed_4404_ = lean_unbox(v_whnfType_4397_);
v_res_4405_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4392_, v_type_4393_, v_maxFVars_x3f_4394_, v_k_4395_, v_cleanupAnnotations_boxed_4403_, v_whnfType_boxed_4404_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
return v_res_4405_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4409_ = lean_unsigned_to_nat(6u);
v___x_4410_ = lean_unsigned_to_nat(329u);
v___x_4411_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4412_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4413_ = l_mkPanicMessageWithDecl(v___x_4412_, v___x_4411_, v___x_4410_, v___x_4409_, v___x_4408_);
return v___x_4413_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4417_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4418_ = lean_unsigned_to_nat(8u);
v___x_4419_ = lean_unsigned_to_nat(322u);
v___x_4420_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4421_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4422_ = l_mkPanicMessageWithDecl(v___x_4421_, v___x_4420_, v___x_4419_, v___x_4418_, v___x_4417_);
return v___x_4422_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4424_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4425_ = lean_unsigned_to_nat(8u);
v___x_4426_ = lean_unsigned_to_nat(325u);
v___x_4427_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4428_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4429_ = l_mkPanicMessageWithDecl(v___x_4428_, v___x_4427_, v___x_4426_, v___x_4425_, v___x_4424_);
return v___x_4429_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4431_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4432_ = lean_unsigned_to_nat(8u);
v___x_4433_ = lean_unsigned_to_nat(324u);
v___x_4434_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4435_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4436_ = l_mkPanicMessageWithDecl(v___x_4435_, v___x_4434_, v___x_4433_, v___x_4432_, v___x_4431_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4437_, lean_object* v___x_4438_, lean_object* v_xs_4439_, lean_object* v_val_4440_, lean_object* v_i_4441_, lean_object* v_perm_4442_, lean_object* v_k_4443_, lean_object* v_xs_x27_4444_, lean_object* v_type_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; uint8_t v___x_4452_; 
v___x_4451_ = lean_array_get_size(v_xs_x27_4444_);
v___x_4452_ = lean_nat_dec_eq(v___x_4451_, v___x_4437_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
lean_dec_ref(v_type_4445_);
lean_dec_ref(v_k_4443_);
lean_dec_ref(v_perm_4442_);
lean_dec_ref(v_xs_4439_);
v___x_4453_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4454_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4453_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4454_;
}
else
{
lean_object* v___x_4455_; lean_object* v_x_4456_; lean_object* v___x_4457_; 
v___x_4455_ = lean_unsigned_to_nat(0u);
v_x_4456_ = lean_array_get_borrowed(v___x_4438_, v_xs_x27_4444_, v___x_4455_);
lean_inc(v___y_4449_);
lean_inc_ref(v___y_4448_);
lean_inc(v___y_4447_);
lean_inc_ref(v___y_4446_);
lean_inc(v_x_4456_);
v___x_4457_ = lean_infer_type(v_x_4456_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; uint8_t v___x_4459_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4458_);
lean_dec_ref_known(v___x_4457_, 1);
v___x_4459_ = l_Lean_Expr_hasLooseBVars(v_a_4458_);
lean_dec(v_a_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4460_; uint8_t v___x_4461_; 
v___x_4460_ = lean_array_get_size(v_xs_4439_);
v___x_4461_ = lean_nat_dec_lt(v_val_4440_, v___x_4460_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
lean_dec_ref(v_type_4445_);
lean_dec_ref(v_k_4443_);
lean_dec_ref(v_perm_4442_);
lean_dec_ref(v_xs_4439_);
v___x_4462_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4463_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4462_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4463_;
}
else
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4464_ = lean_nat_add(v_i_4441_, v___x_4437_);
lean_inc(v_x_4456_);
v___x_4465_ = lean_array_set(v_xs_4439_, v_val_4440_, v_x_4456_);
v___x_4466_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4442_, v_k_4443_, v___x_4464_, v_type_4445_, v___x_4465_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4466_;
}
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref(v_type_4445_);
lean_dec_ref(v_k_4443_);
lean_dec_ref(v_perm_4442_);
lean_dec_ref(v_xs_4439_);
v___x_4467_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4468_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4467_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
return v___x_4468_;
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec_ref(v_type_4445_);
lean_dec_ref(v_k_4443_);
lean_dec_ref(v_perm_4442_);
lean_dec_ref(v_xs_4439_);
v_a_4469_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4457_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4457_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4477_, lean_object* v___x_4478_, lean_object* v_xs_4479_, lean_object* v_val_4480_, lean_object* v_i_4481_, lean_object* v_perm_4482_, lean_object* v_k_4483_, lean_object* v_xs_x27_4484_, lean_object* v_type_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4477_, v___x_4478_, v_xs_4479_, v_val_4480_, v_i_4481_, v_perm_4482_, v_k_4483_, v_xs_x27_4484_, v_type_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v_xs_x27_4484_);
lean_dec(v_i_4481_);
lean_dec(v_val_4480_);
lean_dec_ref(v___x_4478_);
lean_dec(v___x_4477_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4492_, lean_object* v_k_4493_, lean_object* v_i_4494_, lean_object* v_type_4495_, lean_object* v_xs_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_){
_start:
{
lean_object* v___x_4502_; uint8_t v___x_4503_; 
v___x_4502_ = lean_array_get_size(v_perm_4492_);
v___x_4503_ = lean_nat_dec_lt(v_i_4494_, v___x_4502_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4504_; 
lean_dec_ref(v_type_4495_);
lean_dec(v_i_4494_);
lean_dec_ref(v_perm_4492_);
lean_inc(v_a_4500_);
lean_inc_ref(v_a_4499_);
lean_inc(v_a_4498_);
lean_inc_ref(v_a_4497_);
v___x_4504_ = lean_apply_6(v_k_4493_, v_xs_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, lean_box(0));
return v___x_4504_;
}
else
{
lean_object* v___x_4505_; 
v___x_4505_ = lean_array_fget_borrowed(v_perm_4492_, v_i_4494_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v___x_4506_; 
lean_inc(v_a_4500_);
lean_inc_ref(v_a_4499_);
lean_inc(v_a_4498_);
lean_inc_ref(v_a_4497_);
v___x_4506_ = lean_whnf(v_type_4495_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; uint8_t v___x_4508_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_a_4507_);
lean_dec_ref_known(v___x_4506_, 1);
v___x_4508_ = l_Lean_Expr_isForall(v_a_4507_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec(v_a_4507_);
lean_dec_ref(v_xs_4496_);
lean_dec(v_i_4494_);
lean_dec_ref(v_k_4493_);
lean_dec_ref(v_perm_4492_);
v___x_4509_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4510_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4509_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
return v___x_4510_;
}
else
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4511_ = lean_unsigned_to_nat(1u);
v___x_4512_ = lean_nat_add(v_i_4494_, v___x_4511_);
lean_dec(v_i_4494_);
v___x_4513_ = l_Lean_Expr_bindingBody_x21(v_a_4507_);
lean_dec(v_a_4507_);
v_i_4494_ = v___x_4512_;
v_type_4495_ = v___x_4513_;
goto _start;
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec_ref(v_xs_4496_);
lean_dec(v_i_4494_);
lean_dec_ref(v_k_4493_);
lean_dec_ref(v_perm_4492_);
v_a_4515_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4506_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4506_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
else
{
lean_object* v_val_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___f_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; lean_object* v___x_4529_; 
v_val_4523_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_val_4523_);
v___x_4524_ = l_Lean_instInhabitedExpr;
v___x_4525_ = lean_unsigned_to_nat(1u);
v___f_4526_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4526_, 0, v___x_4525_);
lean_closure_set(v___f_4526_, 1, v___x_4524_);
lean_closure_set(v___f_4526_, 2, v_xs_4496_);
lean_closure_set(v___f_4526_, 3, v_val_4523_);
lean_closure_set(v___f_4526_, 4, v_i_4494_);
lean_closure_set(v___f_4526_, 5, v_perm_4492_);
lean_closure_set(v___f_4526_, 6, v_k_4493_);
v___x_4527_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4528_ = 0;
v___x_4529_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4495_, v___x_4527_, v___f_4526_, v___x_4503_, v___x_4528_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
return v___x_4529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4530_, lean_object* v_k_4531_, lean_object* v_i_4532_, lean_object* v_type_4533_, lean_object* v_xs_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4530_, v_k_4531_, v_i_4532_, v_type_4533_, v_xs_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4541_, lean_object* v_perm_4542_, lean_object* v_k_4543_, lean_object* v_i_4544_, lean_object* v_type_4545_, lean_object* v_xs_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4542_, v_k_4543_, v_i_4544_, v_type_4545_, v_xs_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4553_, lean_object* v_perm_4554_, lean_object* v_k_4555_, lean_object* v_i_4556_, lean_object* v_type_4557_, lean_object* v_xs_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4553_, v_perm_4554_, v_k_4555_, v_i_4556_, v_type_4557_, v_xs_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
lean_dec(v_a_4560_);
lean_dec_ref(v_a_4559_);
return v_res_4564_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = lean_unsigned_to_nat(0u);
v___x_4566_ = l_Lean_Level_ofNat(v___x_4565_);
return v___x_4566_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4567_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4568_ = l_Lean_mkSort(v___x_4567_);
return v___x_4568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4569_, lean_object* v_type_4570_, lean_object* v_k_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4577_ = lean_unsigned_to_nat(0u);
v___x_4578_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4569_);
v___x_4579_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4580_ = lean_mk_array(v___x_4578_, v___x_4579_);
v___x_4581_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4569_, v_k_4571_, v___x_4577_, v_type_4570_, v___x_4580_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4582_, lean_object* v_type_4583_, lean_object* v_k_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4582_, v_type_4583_, v_k_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4591_, lean_object* v_perm_4592_, lean_object* v_type_4593_, lean_object* v_k_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_){
_start:
{
lean_object* v___x_4600_; 
v___x_4600_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4592_, v_type_4593_, v_k_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4601_, lean_object* v_perm_4602_, lean_object* v_type_4603_, lean_object* v_k_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4601_, v_perm_4602_, v_type_4603_, v_k_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4605_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4611_, lean_object* v_runInBase_4612_, lean_object* v_b_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = lean_apply_1(v_k_4611_, v_b_4613_);
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
v___x_4620_ = lean_apply_7(v_runInBase_4612_, lean_box(0), v___x_4619_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, lean_box(0));
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4621_, lean_object* v_runInBase_4622_, lean_object* v_b_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4621_, v_runInBase_4622_, v_b_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4630_, lean_object* v_perm_4631_, lean_object* v_type_4632_, lean_object* v_runInBase_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v___f_4639_; lean_object* v___x_4640_; 
v___f_4639_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4639_, 0, v_k_4630_);
lean_closure_set(v___f_4639_, 1, v_runInBase_4633_);
v___x_4640_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4631_, v_type_4632_, v___f_4639_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4641_, lean_object* v_perm_4642_, lean_object* v_type_4643_, lean_object* v_runInBase_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4641_, v_perm_4642_, v_type_4643_, v_runInBase_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4651_, lean_object* v_inst_4652_, lean_object* v_perm_4653_, lean_object* v_type_4654_, lean_object* v_k_4655_){
_start:
{
lean_object* v_toBind_4656_; lean_object* v_liftWith_4657_; lean_object* v_restoreM_4658_; lean_object* v___f_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v_toBind_4656_ = lean_ctor_get(v_inst_4652_, 1);
lean_inc(v_toBind_4656_);
lean_dec_ref(v_inst_4652_);
v_liftWith_4657_ = lean_ctor_get(v_inst_4651_, 0);
lean_inc(v_liftWith_4657_);
v_restoreM_4658_ = lean_ctor_get(v_inst_4651_, 1);
lean_inc(v_restoreM_4658_);
lean_dec_ref(v_inst_4651_);
v___f_4659_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4659_, 0, v_k_4655_);
lean_closure_set(v___f_4659_, 1, v_perm_4653_);
lean_closure_set(v___f_4659_, 2, v_type_4654_);
v___x_4660_ = lean_apply_2(v_liftWith_4657_, lean_box(0), v___f_4659_);
v___x_4661_ = lean_apply_1(v_restoreM_4658_, lean_box(0));
v___x_4662_ = lean_apply_4(v_toBind_4656_, lean_box(0), lean_box(0), v___x_4660_, v___x_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4663_, lean_object* v_00_u03b1_4664_, lean_object* v_inst_4665_, lean_object* v_inst_4666_, lean_object* v_perm_4667_, lean_object* v_type_4668_, lean_object* v_k_4669_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4665_, v_inst_4666_, v_perm_4667_, v_type_4668_, v_k_4669_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v___f_4677_; lean_object* v___x_598__overap_4678_; lean_object* v___x_4679_; 
v___f_4677_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_598__overap_4678_ = lean_panic_fn_borrowed(v___f_4677_, v_msg_4671_);
lean_inc(v___y_4675_);
lean_inc_ref(v___y_4674_);
lean_inc(v___y_4673_);
lean_inc_ref(v___y_4672_);
v___x_4679_ = lean_apply_5(v___x_598__overap_4678_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, lean_box(0));
return v___x_4679_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
return v_res_4686_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4689_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4690_ = lean_unsigned_to_nat(10u);
v___x_4691_ = lean_unsigned_to_nat(353u);
v___x_4692_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4693_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4694_ = l_mkPanicMessageWithDecl(v___x_4693_, v___x_4692_, v___x_4691_, v___x_4690_, v___x_4689_);
return v___x_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4695_, lean_object* v_xs_4696_, lean_object* v_tail_4697_, lean_object* v_ys_4698_, lean_object* v_type_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4695_, v_xs_4696_, v_tail_4697_, v_ys_4698_, v_type_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec_ref(v_ys_4698_);
lean_dec(v___x_4695_);
return v_res_4705_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4706_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4707_ = lean_unsigned_to_nat(8u);
v___x_4708_ = lean_unsigned_to_nat(349u);
v___x_4709_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4710_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4711_ = l_mkPanicMessageWithDecl(v___x_4710_, v___x_4709_, v___x_4708_, v___x_4707_, v___x_4706_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4712_, lean_object* v_x_4713_, lean_object* v_x_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
if (lean_obj_tag(v_x_4713_) == 0)
{
lean_object* v___x_4720_; 
lean_dec_ref(v_xs_4712_);
v___x_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4720_, 0, v_x_4714_);
return v___x_4720_;
}
else
{
lean_object* v_head_4721_; 
v_head_4721_ = lean_ctor_get(v_x_4713_, 0);
if (lean_obj_tag(v_head_4721_) == 0)
{
lean_object* v_tail_4722_; lean_object* v___x_4723_; lean_object* v___f_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; lean_object* v___x_4727_; 
v_tail_4722_ = lean_ctor_get(v_x_4713_, 1);
lean_inc(v_tail_4722_);
lean_dec_ref_known(v_x_4713_, 2);
v___x_4723_ = lean_unsigned_to_nat(1u);
v___f_4724_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4724_, 0, v___x_4723_);
lean_closure_set(v___f_4724_, 1, v_xs_4712_);
lean_closure_set(v___f_4724_, 2, v_tail_4722_);
v___x_4725_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4726_ = 0;
v___x_4727_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4714_, v___x_4725_, v___f_4724_, v___x_4726_, v___x_4726_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_);
return v___x_4727_;
}
else
{
lean_object* v_tail_4728_; lean_object* v_val_4729_; lean_object* v___x_4730_; uint8_t v___x_4731_; 
lean_inc_ref(v_head_4721_);
v_tail_4728_ = lean_ctor_get(v_x_4713_, 1);
lean_inc(v_tail_4728_);
lean_dec_ref_known(v_x_4713_, 2);
v_val_4729_ = lean_ctor_get(v_head_4721_, 0);
lean_inc(v_val_4729_);
lean_dec_ref_known(v_head_4721_, 1);
v___x_4730_ = lean_array_get_size(v_xs_4712_);
v___x_4731_ = lean_nat_dec_lt(v_val_4729_, v___x_4730_);
if (v___x_4731_ == 0)
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
lean_dec(v_val_4729_);
lean_dec(v_tail_4728_);
lean_dec_ref(v_x_4714_);
lean_dec_ref(v_xs_4712_);
v___x_4732_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4733_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4732_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_);
return v___x_4733_;
}
else
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4734_ = l_Lean_instInhabitedExpr;
v___x_4735_ = lean_array_get_borrowed(v___x_4734_, v_xs_4712_, v_val_4729_);
lean_dec(v_val_4729_);
v___x_4736_ = lean_unsigned_to_nat(1u);
v___x_4737_ = lean_mk_empty_array_with_capacity(v___x_4736_);
lean_inc(v___x_4735_);
v___x_4738_ = lean_array_push(v___x_4737_, v___x_4735_);
v___x_4739_ = l_Lean_Meta_instantiateForall(v_x_4714_, v___x_4738_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_);
lean_dec_ref(v___x_4738_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
lean_inc(v_a_4740_);
lean_dec_ref_known(v___x_4739_, 1);
v_x_4713_ = v_tail_4728_;
v_x_4714_ = v_a_4740_;
goto _start;
}
else
{
lean_dec(v_tail_4728_);
lean_dec_ref(v_xs_4712_);
return v___x_4739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4742_, lean_object* v_xs_4743_, lean_object* v_tail_4744_, lean_object* v_ys_4745_, lean_object* v_type_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v___x_4752_; uint8_t v___x_4753_; 
v___x_4752_ = lean_array_get_size(v_ys_4745_);
v___x_4753_ = lean_nat_dec_eq(v___x_4752_, v___x_4742_);
if (v___x_4753_ == 0)
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
lean_dec_ref(v_type_4746_);
lean_dec(v_tail_4744_);
lean_dec_ref(v_xs_4743_);
v___x_4754_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4755_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4754_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
return v___x_4755_;
}
else
{
lean_object* v___x_4756_; 
v___x_4756_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4743_, v_tail_4744_, v_type_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; uint8_t v___x_4758_; uint8_t v___x_4759_; lean_object* v___x_4760_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4757_);
lean_dec_ref_known(v___x_4756_, 1);
v___x_4758_ = 0;
v___x_4759_ = 1;
v___x_4760_ = l_Lean_Meta_mkForallFVars(v_ys_4745_, v_a_4757_, v___x_4758_, v___x_4753_, v___x_4753_, v___x_4759_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
return v___x_4760_;
}
else
{
return v___x_4756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4761_, lean_object* v_x_4762_, lean_object* v_x_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4761_, v_x_4762_, v_x_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
return v_res_4769_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4772_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4773_ = lean_unsigned_to_nat(2u);
v___x_4774_ = lean_unsigned_to_nat(343u);
v___x_4775_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4776_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4777_ = l_mkPanicMessageWithDecl(v___x_4776_, v___x_4775_, v___x_4774_, v___x_4773_, v___x_4772_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4778_, lean_object* v_type_u2080_4779_, lean_object* v_xs_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4786_ = lean_array_get_size(v_xs_4780_);
v___x_4787_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4778_);
v___x_4788_ = lean_nat_dec_eq(v___x_4786_, v___x_4787_);
lean_dec(v___x_4787_);
if (v___x_4788_ == 0)
{
lean_object* v___x_4789_; lean_object* v___x_4790_; 
lean_dec_ref(v_xs_4780_);
lean_dec_ref(v_type_u2080_4779_);
lean_dec_ref(v_perm_4778_);
v___x_4789_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4790_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4789_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
return v___x_4790_;
}
else
{
lean_object* v_mask_4791_; lean_object* v___x_4792_; 
v_mask_4791_ = lean_array_to_list(v_perm_4778_);
v___x_4792_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4780_, v_mask_4791_, v_type_u2080_4779_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_);
return v___x_4792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4793_, lean_object* v_type_u2080_4794_, lean_object* v_xs_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v_res_4801_; 
v_res_4801_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4793_, v_type_u2080_4794_, v_xs_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_);
lean_dec(v_a_4799_);
lean_dec_ref(v_a_4798_);
lean_dec(v_a_4797_);
lean_dec_ref(v_a_4796_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4802_, lean_object* v_maxFVars_4803_, lean_object* v_k_4804_, uint8_t v_cleanupAnnotations_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_){
_start:
{
lean_object* v___f_4811_; uint8_t v___x_4812_; uint8_t v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___f_4811_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4811_, 0, v_k_4804_);
v___x_4812_ = 1;
v___x_4813_ = 0;
v___x_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4814_, 0, v_maxFVars_4803_);
v___x_4815_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4802_, v___x_4812_, v___x_4813_, v___x_4812_, v___x_4813_, v___x_4814_, v___f_4811_, v_cleanupAnnotations_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_);
lean_dec_ref_known(v___x_4814_, 1);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4815_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4815_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4831_; 
v_a_4824_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4826_ = v___x_4815_;
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4815_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4832_, lean_object* v_maxFVars_4833_, lean_object* v_k_4834_, lean_object* v_cleanupAnnotations_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4841_; lean_object* v_res_4842_; 
v_cleanupAnnotations_boxed_4841_ = lean_unbox(v_cleanupAnnotations_4835_);
v_res_4842_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4832_, v_maxFVars_4833_, v_k_4834_, v_cleanupAnnotations_boxed_4841_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4843_, lean_object* v_e_4844_, lean_object* v_maxFVars_4845_, lean_object* v_k_4846_, uint8_t v_cleanupAnnotations_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4844_, v_maxFVars_4845_, v_k_4846_, v_cleanupAnnotations_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4854_, lean_object* v_e_4855_, lean_object* v_maxFVars_4856_, lean_object* v_k_4857_, lean_object* v_cleanupAnnotations_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4864_; lean_object* v_res_4865_; 
v_cleanupAnnotations_boxed_4864_ = lean_unbox(v_cleanupAnnotations_4858_);
v_res_4865_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4854_, v_e_4855_, v_maxFVars_4856_, v_k_4857_, v_cleanupAnnotations_boxed_4864_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
return v_res_4865_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4866_){
_start:
{
if (lean_obj_tag(v_x_4866_) == 0)
{
uint8_t v___x_4867_; 
v___x_4867_ = 1;
return v___x_4867_;
}
else
{
lean_object* v_head_4868_; 
v_head_4868_ = lean_ctor_get(v_x_4866_, 0);
if (lean_obj_tag(v_head_4868_) == 0)
{
lean_object* v_tail_4869_; 
v_tail_4869_ = lean_ctor_get(v_x_4866_, 1);
v_x_4866_ = v_tail_4869_;
goto _start;
}
else
{
uint8_t v___x_4871_; 
v___x_4871_ = 0;
return v___x_4871_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4872_){
_start:
{
uint8_t v_res_4873_; lean_object* v_r_4874_; 
v_res_4873_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4872_);
lean_dec(v_x_4872_);
v_r_4874_ = lean_box(v_res_4873_);
return v_r_4874_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4877_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4878_ = lean_unsigned_to_nat(12u);
v___x_4879_ = lean_unsigned_to_nat(376u);
v___x_4880_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4881_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4882_ = l_mkPanicMessageWithDecl(v___x_4881_, v___x_4880_, v___x_4879_, v___x_4878_, v___x_4877_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4883_, lean_object* v_xs_4884_, lean_object* v_tail_4885_, lean_object* v___x_4886_, lean_object* v___x_4887_, lean_object* v_ys_4888_, lean_object* v_value_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
uint8_t v___x_1213__boxed_4895_; uint8_t v___x_1214__boxed_4896_; lean_object* v_res_4897_; 
v___x_1213__boxed_4895_ = lean_unbox(v___x_4886_);
v___x_1214__boxed_4896_ = lean_unbox(v___x_4887_);
v_res_4897_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4883_, v_xs_4884_, v_tail_4885_, v___x_1213__boxed_4895_, v___x_1214__boxed_4896_, v_ys_4888_, v_value_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
lean_dec_ref(v_ys_4888_);
lean_dec(v___x_4883_);
return v_res_4897_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4898_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4899_ = lean_unsigned_to_nat(8u);
v___x_4900_ = lean_unsigned_to_nat(368u);
v___x_4901_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4902_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4903_ = l_mkPanicMessageWithDecl(v___x_4902_, v___x_4901_, v___x_4900_, v___x_4899_, v___x_4898_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4904_, lean_object* v_x_4905_, lean_object* v_x_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
if (lean_obj_tag(v_x_4905_) == 0)
{
lean_object* v___x_4912_; 
lean_dec_ref(v_xs_4904_);
v___x_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4912_, 0, v_x_4906_);
return v___x_4912_;
}
else
{
lean_object* v_head_4913_; 
v_head_4913_ = lean_ctor_get(v_x_4905_, 0);
if (lean_obj_tag(v_head_4913_) == 0)
{
lean_object* v_tail_4914_; uint8_t v___x_4915_; 
v_tail_4914_ = lean_ctor_get(v_x_4905_, 1);
lean_inc(v_tail_4914_);
lean_dec_ref_known(v_x_4905_, 2);
v___x_4915_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4914_);
if (v___x_4915_ == 0)
{
uint8_t v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___f_4920_; lean_object* v___x_4921_; 
v___x_4916_ = 1;
v___x_4917_ = lean_unsigned_to_nat(1u);
v___x_4918_ = lean_box(v___x_4915_);
v___x_4919_ = lean_box(v___x_4916_);
v___f_4920_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4920_, 0, v___x_4917_);
lean_closure_set(v___f_4920_, 1, v_xs_4904_);
lean_closure_set(v___f_4920_, 2, v_tail_4914_);
lean_closure_set(v___f_4920_, 3, v___x_4918_);
lean_closure_set(v___f_4920_, 4, v___x_4919_);
v___x_4921_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4906_, v___x_4917_, v___f_4920_, v___x_4915_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_);
return v___x_4921_;
}
else
{
lean_object* v___x_4922_; 
lean_dec(v_tail_4914_);
lean_dec_ref(v_xs_4904_);
v___x_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4922_, 0, v_x_4906_);
return v___x_4922_;
}
}
else
{
lean_object* v_tail_4923_; lean_object* v_val_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; 
lean_inc_ref(v_head_4913_);
v_tail_4923_ = lean_ctor_get(v_x_4905_, 1);
lean_inc(v_tail_4923_);
lean_dec_ref_known(v_x_4905_, 2);
v_val_4924_ = lean_ctor_get(v_head_4913_, 0);
lean_inc(v_val_4924_);
lean_dec_ref_known(v_head_4913_, 1);
v___x_4925_ = lean_array_get_size(v_xs_4904_);
v___x_4926_ = lean_nat_dec_lt(v_val_4924_, v___x_4925_);
if (v___x_4926_ == 0)
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
lean_dec(v_val_4924_);
lean_dec(v_tail_4923_);
lean_dec_ref(v_x_4906_);
lean_dec_ref(v_xs_4904_);
v___x_4927_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4928_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4927_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_);
return v___x_4928_;
}
else
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; 
v___x_4929_ = l_Lean_instInhabitedExpr;
v___x_4930_ = lean_array_get_borrowed(v___x_4929_, v_xs_4904_, v_val_4924_);
lean_dec(v_val_4924_);
v___x_4931_ = lean_unsigned_to_nat(1u);
v___x_4932_ = lean_mk_empty_array_with_capacity(v___x_4931_);
lean_inc(v___x_4930_);
v___x_4933_ = lean_array_push(v___x_4932_, v___x_4930_);
v___x_4934_ = l_Lean_Meta_instantiateLambda(v_x_4906_, v___x_4933_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_);
lean_dec_ref(v___x_4933_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___x_4934_, 1);
v_x_4905_ = v_tail_4923_;
v_x_4906_ = v_a_4935_;
goto _start;
}
else
{
lean_dec(v_tail_4923_);
lean_dec_ref(v_xs_4904_);
return v___x_4934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4937_, lean_object* v_xs_4938_, lean_object* v_tail_4939_, uint8_t v___x_4940_, uint8_t v___x_4941_, lean_object* v_ys_4942_, lean_object* v_value_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v___x_4949_; uint8_t v___x_4950_; 
v___x_4949_ = lean_array_get_size(v_ys_4942_);
v___x_4950_ = lean_nat_dec_eq(v___x_4949_, v___x_4937_);
if (v___x_4950_ == 0)
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
lean_dec_ref(v_value_4943_);
lean_dec(v_tail_4939_);
lean_dec_ref(v_xs_4938_);
v___x_4951_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4952_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4951_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
return v___x_4952_;
}
else
{
lean_object* v___x_4953_; 
v___x_4953_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4938_, v_tail_4939_, v_value_4943_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v_a_4954_; uint8_t v___x_4955_; lean_object* v___x_4956_; 
v_a_4954_ = lean_ctor_get(v___x_4953_, 0);
lean_inc(v_a_4954_);
lean_dec_ref_known(v___x_4953_, 1);
v___x_4955_ = 1;
v___x_4956_ = l_Lean_Meta_mkLambdaFVars(v_ys_4942_, v_a_4954_, v___x_4940_, v___x_4941_, v___x_4940_, v___x_4941_, v___x_4955_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
return v___x_4956_;
}
else
{
return v___x_4953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4957_, lean_object* v_x_4958_, lean_object* v_x_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4957_, v_x_4958_, v_x_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
return v_res_4965_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4967_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4968_ = lean_unsigned_to_nat(2u);
v___x_4969_ = lean_unsigned_to_nat(362u);
v___x_4970_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_4971_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4972_ = l_mkPanicMessageWithDecl(v___x_4971_, v___x_4970_, v___x_4969_, v___x_4968_, v___x_4967_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_4973_, lean_object* v_value_u2080_4974_, lean_object* v_xs_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; uint8_t v___x_4983_; 
v___x_4981_ = lean_array_get_size(v_xs_4975_);
v___x_4982_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4973_);
v___x_4983_ = lean_nat_dec_eq(v___x_4981_, v___x_4982_);
lean_dec(v___x_4982_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
lean_dec_ref(v_xs_4975_);
lean_dec_ref(v_value_u2080_4974_);
lean_dec_ref(v_perm_4973_);
v___x_4984_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_4985_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4984_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
return v___x_4985_;
}
else
{
lean_object* v_mask_4986_; lean_object* v___x_4987_; 
v_mask_4986_ = lean_array_to_list(v_perm_4973_);
v___x_4987_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4975_, v_mask_4986_, v_value_u2080_4974_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_);
return v___x_4987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_4988_, lean_object* v_value_u2080_4989_, lean_object* v_xs_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_4988_, v_value_u2080_4989_, v_xs_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
lean_dec(v_a_4992_);
lean_dec_ref(v_a_4991_);
return v_res_4996_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = l_Array_instInhabited(lean_box(0));
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5005_){
_start:
{
lean_object* v___f_5006_; lean_object* v___f_5007_; lean_object* v___f_5008_; lean_object* v___f_5009_; lean_object* v___f_5010_; lean_object* v___f_5011_; lean_object* v___f_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___f_5006_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5007_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5008_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5009_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5010_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5011_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5012_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5013_, 0, v___f_5006_);
lean_ctor_set(v___x_5013_, 1, v___f_5007_);
v___x_5014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5013_);
lean_ctor_set(v___x_5014_, 1, v___f_5008_);
lean_ctor_set(v___x_5014_, 2, v___f_5009_);
lean_ctor_set(v___x_5014_, 3, v___f_5010_);
lean_ctor_set(v___x_5014_, 4, v___f_5011_);
v___x_5015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5014_);
lean_ctor_set(v___x_5015_, 1, v___f_5012_);
v___x_5016_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5017_ = l_instInhabitedOfMonad___redArg(v___x_5015_, v___x_5016_);
v___x_5018_ = lean_panic_fn_borrowed(v___x_5017_, v_msg_5005_);
lean_dec(v___x_5017_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5019_, lean_object* v_msg_5020_){
_start:
{
lean_object* v___x_5021_; 
v___x_5021_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5020_);
return v___x_5021_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; 
v___x_5024_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5025_ = lean_unsigned_to_nat(8u);
v___x_5026_ = lean_unsigned_to_nat(394u);
v___x_5027_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5028_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5029_ = l_mkPanicMessageWithDecl(v___x_5028_, v___x_5027_, v___x_5026_, v___x_5025_, v___x_5024_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5030_, lean_object* v_x_5031_){
_start:
{
if (lean_obj_tag(v_x_5030_) == 0)
{
return v_x_5031_;
}
else
{
lean_object* v_head_5032_; lean_object* v_fst_5033_; 
v_head_5032_ = lean_ctor_get(v_x_5030_, 0);
v_fst_5033_ = lean_ctor_get(v_head_5032_, 0);
if (lean_obj_tag(v_fst_5033_) == 0)
{
lean_object* v_tail_5034_; 
v_tail_5034_ = lean_ctor_get(v_x_5030_, 1);
lean_inc(v_tail_5034_);
lean_dec_ref_known(v_x_5030_, 2);
v_x_5030_ = v_tail_5034_;
goto _start;
}
else
{
lean_object* v_tail_5036_; lean_object* v_snd_5037_; lean_object* v_val_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
lean_inc_ref(v_fst_5033_);
lean_inc(v_head_5032_);
v_tail_5036_ = lean_ctor_get(v_x_5030_, 1);
lean_inc(v_tail_5036_);
lean_dec_ref_known(v_x_5030_, 2);
v_snd_5037_ = lean_ctor_get(v_head_5032_, 1);
lean_inc(v_snd_5037_);
lean_dec(v_head_5032_);
v_val_5038_ = lean_ctor_get(v_fst_5033_, 0);
lean_inc(v_val_5038_);
lean_dec_ref_known(v_fst_5033_, 1);
v___x_5039_ = lean_array_get_size(v_x_5031_);
v___x_5040_ = lean_nat_dec_lt(v_val_5038_, v___x_5039_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
lean_dec(v_val_5038_);
lean_dec(v_snd_5037_);
lean_dec(v_tail_5036_);
lean_dec_ref(v_x_5031_);
v___x_5041_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5042_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5041_);
return v___x_5042_;
}
else
{
lean_object* v___x_5043_; 
v___x_5043_ = lean_array_set(v_x_5031_, v_val_5038_, v_snd_5037_);
lean_dec(v_val_5038_);
v_x_5030_ = v_tail_5036_;
v_x_5031_ = v___x_5043_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5045_, lean_object* v_x_5046_, lean_object* v_x_5047_){
_start:
{
lean_object* v___x_5048_; 
v___x_5048_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5046_, v_x_5047_);
return v___x_5048_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5051_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5052_ = lean_unsigned_to_nat(2u);
v___x_5053_ = lean_unsigned_to_nat(384u);
v___x_5054_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5055_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5056_ = l_mkPanicMessageWithDecl(v___x_5055_, v___x_5054_, v___x_5053_, v___x_5052_, v___x_5051_);
return v___x_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5059_, lean_object* v_xs_5060_){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; uint8_t v___x_5063_; 
v___x_5061_ = lean_array_get_size(v_xs_5060_);
v___x_5062_ = lean_array_get_size(v_perm_5059_);
v___x_5063_ = lean_nat_dec_eq(v___x_5061_, v___x_5062_);
if (v___x_5063_ == 0)
{
lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5064_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5065_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5064_);
return v___x_5065_;
}
else
{
lean_object* v___x_5066_; uint8_t v___x_5067_; 
v___x_5066_ = lean_unsigned_to_nat(0u);
v___x_5067_ = lean_nat_dec_eq(v___x_5061_, v___x_5066_);
if (v___x_5067_ == 0)
{
lean_object* v_dummy_5068_; lean_object* v___x_5069_; lean_object* v_ys_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v_dummy_5068_ = lean_array_fget_borrowed(v_xs_5060_, v___x_5066_);
v___x_5069_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5059_);
lean_inc(v_dummy_5068_);
v_ys_5070_ = lean_mk_array(v___x_5069_, v_dummy_5068_);
v___x_5071_ = l_Array_zip___redArg(v_perm_5059_, v_xs_5060_);
v___x_5072_ = lean_array_to_list(v___x_5071_);
v___x_5073_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5072_, v_ys_5070_);
return v___x_5073_;
}
else
{
lean_object* v___x_5074_; 
v___x_5074_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5075_, lean_object* v_xs_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5075_, v_xs_5076_);
lean_dec_ref(v_xs_5076_);
lean_dec_ref(v_perm_5075_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5078_, lean_object* v_perm_5079_, lean_object* v_xs_5080_){
_start:
{
lean_object* v___x_5081_; 
v___x_5081_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5079_, v_xs_5080_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5082_, lean_object* v_perm_5083_, lean_object* v_xs_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5082_, v_perm_5083_, v_xs_5084_);
lean_dec_ref(v_xs_5084_);
lean_dec_ref(v_perm_5083_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5086_, lean_object* v_upperBound_5087_, lean_object* v_perm_5088_, lean_object* v_a_5089_, lean_object* v_b_5090_){
_start:
{
lean_object* v_a_5092_; uint8_t v___x_5099_; 
v___x_5099_ = lean_nat_dec_lt(v_a_5089_, v_upperBound_5087_);
if (v___x_5099_ == 0)
{
lean_dec(v_a_5089_);
return v_b_5090_;
}
else
{
lean_object* v___x_5100_; uint8_t v___x_5101_; 
v___x_5100_ = lean_array_get_size(v_perm_5088_);
v___x_5101_ = lean_nat_dec_lt(v_a_5089_, v___x_5100_);
if (v___x_5101_ == 0)
{
goto v___jp_5096_;
}
else
{
lean_object* v___x_5102_; 
v___x_5102_ = lean_array_fget_borrowed(v_perm_5088_, v_a_5089_);
if (lean_obj_tag(v___x_5102_) == 0)
{
goto v___jp_5096_;
}
else
{
v_a_5092_ = v_b_5090_;
goto v___jp_5091_;
}
}
}
v___jp_5091_:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = lean_unsigned_to_nat(1u);
v___x_5094_ = lean_nat_add(v_a_5089_, v___x_5093_);
lean_dec(v_a_5089_);
v_a_5089_ = v___x_5094_;
v_b_5090_ = v_a_5092_;
goto _start;
}
v___jp_5096_:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = lean_array_fget_borrowed(v_xs_5086_, v_a_5089_);
lean_inc(v___x_5097_);
v___x_5098_ = lean_array_push(v_b_5090_, v___x_5097_);
v_a_5092_ = v___x_5098_;
goto v___jp_5091_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5103_, lean_object* v_upperBound_5104_, lean_object* v_perm_5105_, lean_object* v_a_5106_, lean_object* v_b_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5103_, v_upperBound_5104_, v_perm_5105_, v_a_5106_, v_b_5107_);
lean_dec_ref(v_perm_5105_);
lean_dec(v_upperBound_5104_);
lean_dec_ref(v_xs_5103_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5109_, lean_object* v_xs_5110_){
_start:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v_ys_5113_; lean_object* v___x_5114_; 
v___x_5111_ = lean_array_get_size(v_xs_5110_);
v___x_5112_ = lean_unsigned_to_nat(0u);
v_ys_5113_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5110_, v___x_5111_, v_perm_5109_, v___x_5112_, v_ys_5113_);
return v___x_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5115_, lean_object* v_xs_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5115_, v_xs_5116_);
lean_dec_ref(v_xs_5116_);
lean_dec_ref(v_perm_5115_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5118_, lean_object* v_perm_5119_, lean_object* v_xs_5120_){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5119_, v_xs_5120_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5122_, lean_object* v_perm_5123_, lean_object* v_xs_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5122_, v_perm_5123_, v_xs_5124_);
lean_dec_ref(v_xs_5124_);
lean_dec_ref(v_perm_5123_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5126_, lean_object* v_xs_5127_, lean_object* v_upperBound_5128_, lean_object* v_perm_5129_, lean_object* v_inst_5130_, lean_object* v_R_5131_, lean_object* v_a_5132_, lean_object* v_b_5133_, lean_object* v_c_5134_){
_start:
{
lean_object* v___x_5135_; 
v___x_5135_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5127_, v_upperBound_5128_, v_perm_5129_, v_a_5132_, v_b_5133_);
return v___x_5135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5136_, lean_object* v_xs_5137_, lean_object* v_upperBound_5138_, lean_object* v_perm_5139_, lean_object* v_inst_5140_, lean_object* v_R_5141_, lean_object* v_a_5142_, lean_object* v_b_5143_, lean_object* v_c_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5136_, v_xs_5137_, v_upperBound_5138_, v_perm_5139_, v_inst_5140_, v_R_5141_, v_a_5142_, v_b_5143_, v_c_5144_);
lean_dec_ref(v_perm_5139_);
lean_dec(v_upperBound_5138_);
lean_dec_ref(v_xs_5137_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5146_){
_start:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5147_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5148_ = lean_panic_fn_borrowed(v___x_5147_, v_msg_5146_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5149_, lean_object* v_msg_5150_){
_start:
{
lean_object* v___x_5151_; 
v___x_5151_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5150_);
return v___x_5151_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5152_, lean_object* v___x_5153_, lean_object* v_i_5154_, lean_object* v___x_5155_, lean_object* v_as_5156_, size_t v_i_5157_, size_t v_stop_5158_){
_start:
{
uint8_t v___x_5159_; 
v___x_5159_ = lean_usize_dec_eq(v_i_5157_, v_stop_5158_);
if (v___x_5159_ == 0)
{
uint8_t v___x_5160_; uint8_t v___y_5162_; lean_object* v___x_5166_; 
v___x_5160_ = 1;
v___x_5166_ = lean_array_uget_borrowed(v_as_5156_, v_i_5157_);
if (lean_obj_tag(v___x_5166_) == 0)
{
uint8_t v___x_5167_; 
v___x_5167_ = lean_nat_dec_lt(v_j_5152_, v___x_5153_);
v___y_5162_ = v___x_5167_;
goto v___jp_5161_;
}
else
{
uint8_t v___x_5168_; 
v___x_5168_ = lean_nat_dec_lt(v_i_5154_, v___x_5155_);
v___y_5162_ = v___x_5168_;
goto v___jp_5161_;
}
v___jp_5161_:
{
if (v___y_5162_ == 0)
{
size_t v___x_5163_; size_t v___x_5164_; 
v___x_5163_ = ((size_t)1ULL);
v___x_5164_ = lean_usize_add(v_i_5157_, v___x_5163_);
v_i_5157_ = v___x_5164_;
goto _start;
}
else
{
return v___x_5160_;
}
}
}
else
{
uint8_t v___x_5169_; 
v___x_5169_ = 0;
return v___x_5169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5170_, lean_object* v___x_5171_, lean_object* v_i_5172_, lean_object* v___x_5173_, lean_object* v_as_5174_, lean_object* v_i_5175_, lean_object* v_stop_5176_){
_start:
{
size_t v_i_boxed_5177_; size_t v_stop_boxed_5178_; uint8_t v_res_5179_; lean_object* v_r_5180_; 
v_i_boxed_5177_ = lean_unbox_usize(v_i_5175_);
lean_dec(v_i_5175_);
v_stop_boxed_5178_ = lean_unbox_usize(v_stop_5176_);
lean_dec(v_stop_5176_);
v_res_5179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5170_, v___x_5171_, v_i_5172_, v___x_5173_, v_as_5174_, v_i_boxed_5177_, v_stop_boxed_5178_);
lean_dec_ref(v_as_5174_);
lean_dec(v___x_5173_);
lean_dec(v_i_5172_);
lean_dec(v___x_5171_);
lean_dec(v_j_5170_);
v_r_5180_ = lean_box(v_res_5179_);
return v_r_5180_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v___x_5183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5184_ = lean_unsigned_to_nat(10u);
v___x_5185_ = lean_unsigned_to_nat(425u);
v___x_5186_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5187_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5188_ = l_mkPanicMessageWithDecl(v___x_5187_, v___x_5186_, v___x_5185_, v___x_5184_, v___x_5183_);
return v___x_5188_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v___x_5190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5191_ = lean_unsigned_to_nat(12u);
v___x_5192_ = lean_unsigned_to_nat(433u);
v___x_5193_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5194_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5195_ = l_mkPanicMessageWithDecl(v___x_5194_, v___x_5193_, v___x_5192_, v___x_5191_, v___x_5190_);
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5196_, lean_object* v_fixedArgs_5197_, lean_object* v_varyingArgs_5198_, lean_object* v_i_5199_, lean_object* v_j_5200_, lean_object* v_xs_5201_){
_start:
{
lean_object* v_lower_5203_; lean_object* v_upper_5204_; lean_object* v___x_5208_; uint8_t v___x_5209_; 
v___x_5208_ = lean_array_get_size(v_perm_5196_);
v___x_5209_ = lean_nat_dec_lt(v_i_5199_, v___x_5208_);
if (v___x_5209_ == 0)
{
lean_object* v___x_5210_; lean_object* v___x_5211_; uint8_t v___x_5212_; 
lean_dec(v_i_5199_);
lean_dec_ref(v_perm_5196_);
v___x_5210_ = lean_unsigned_to_nat(0u);
v___x_5211_ = lean_array_get_size(v_varyingArgs_5198_);
v___x_5212_ = lean_nat_dec_le(v_j_5200_, v___x_5210_);
if (v___x_5212_ == 0)
{
v_lower_5203_ = v_j_5200_;
v_upper_5204_ = v___x_5211_;
goto v___jp_5202_;
}
else
{
lean_dec(v_j_5200_);
v_lower_5203_ = v___x_5210_;
v_upper_5204_ = v___x_5211_;
goto v___jp_5202_;
}
}
else
{
lean_object* v___x_5213_; 
v___x_5213_ = lean_array_fget_borrowed(v_perm_5196_, v_i_5199_);
if (lean_obj_tag(v___x_5213_) == 1)
{
lean_object* v_val_5214_; lean_object* v___x_5215_; uint8_t v___x_5216_; 
v_val_5214_ = lean_ctor_get(v___x_5213_, 0);
v___x_5215_ = lean_array_get_size(v_fixedArgs_5197_);
v___x_5216_ = lean_nat_dec_lt(v_val_5214_, v___x_5215_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; lean_object* v___x_5218_; 
lean_dec_ref(v_xs_5201_);
lean_dec(v_j_5200_);
lean_dec(v_i_5199_);
lean_dec_ref(v_varyingArgs_5198_);
lean_dec_ref(v_perm_5196_);
v___x_5217_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5218_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5217_);
return v___x_5218_;
}
else
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; 
v___x_5219_ = lean_unsigned_to_nat(1u);
v___x_5220_ = lean_nat_add(v_i_5199_, v___x_5219_);
lean_dec(v_i_5199_);
v___x_5221_ = lean_array_fget_borrowed(v_fixedArgs_5197_, v_val_5214_);
lean_inc(v___x_5221_);
v___x_5222_ = lean_array_push(v_xs_5201_, v___x_5221_);
v_i_5199_ = v___x_5220_;
v_xs_5201_ = v___x_5222_;
goto _start;
}
}
else
{
lean_object* v___x_5224_; lean_object* v___y_5226_; lean_object* v___y_5227_; lean_object* v___y_5228_; lean_object* v_lower_5236_; lean_object* v_upper_5237_; uint8_t v___x_5245_; 
v___x_5224_ = lean_array_get_size(v_varyingArgs_5198_);
v___x_5245_ = lean_nat_dec_lt(v_j_5200_, v___x_5224_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; uint8_t v___x_5247_; 
lean_dec_ref(v_varyingArgs_5198_);
v___x_5246_ = lean_unsigned_to_nat(0u);
v___x_5247_ = lean_nat_dec_le(v_i_5199_, v___x_5246_);
if (v___x_5247_ == 0)
{
lean_inc(v_i_5199_);
v_lower_5236_ = v_i_5199_;
v_upper_5237_ = v___x_5208_;
goto v___jp_5235_;
}
else
{
v_lower_5236_ = v___x_5246_;
v_upper_5237_ = v___x_5208_;
goto v___jp_5235_;
}
}
else
{
lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; 
v___x_5248_ = lean_unsigned_to_nat(1u);
v___x_5249_ = lean_nat_add(v_i_5199_, v___x_5248_);
lean_dec(v_i_5199_);
v___x_5250_ = lean_nat_add(v_j_5200_, v___x_5248_);
v___x_5251_ = lean_array_fget_borrowed(v_varyingArgs_5198_, v_j_5200_);
lean_dec(v_j_5200_);
lean_inc(v___x_5251_);
v___x_5252_ = lean_array_push(v_xs_5201_, v___x_5251_);
v_i_5199_ = v___x_5249_;
v_j_5200_ = v___x_5250_;
v_xs_5201_ = v___x_5252_;
goto _start;
}
v___jp_5225_:
{
uint8_t v___x_5229_; 
v___x_5229_ = lean_nat_dec_lt(v___y_5227_, v___y_5228_);
if (v___x_5229_ == 0)
{
lean_dec(v___y_5228_);
lean_dec(v___y_5227_);
lean_dec_ref(v___y_5226_);
lean_dec(v_j_5200_);
lean_dec(v_i_5199_);
return v_xs_5201_;
}
else
{
size_t v___x_5230_; size_t v___x_5231_; uint8_t v___x_5232_; 
v___x_5230_ = lean_usize_of_nat(v___y_5227_);
lean_dec(v___y_5227_);
v___x_5231_ = lean_usize_of_nat(v___y_5228_);
lean_dec(v___y_5228_);
v___x_5232_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5200_, v___x_5224_, v_i_5199_, v___x_5208_, v___y_5226_, v___x_5230_, v___x_5231_);
lean_dec_ref(v___y_5226_);
lean_dec(v_i_5199_);
lean_dec(v_j_5200_);
if (v___x_5232_ == 0)
{
return v_xs_5201_;
}
else
{
lean_object* v___x_5233_; lean_object* v___x_5234_; 
lean_dec_ref(v_xs_5201_);
v___x_5233_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5234_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5233_);
return v___x_5234_;
}
}
}
v___jp_5235_:
{
lean_object* v___x_5238_; lean_object* v_array_5239_; lean_object* v_start_5240_; lean_object* v_stop_5241_; uint8_t v___x_5242_; 
v___x_5238_ = l_Array_toSubarray___redArg(v_perm_5196_, v_lower_5236_, v_upper_5237_);
v_array_5239_ = lean_ctor_get(v___x_5238_, 0);
lean_inc_ref(v_array_5239_);
v_start_5240_ = lean_ctor_get(v___x_5238_, 1);
lean_inc(v_start_5240_);
v_stop_5241_ = lean_ctor_get(v___x_5238_, 2);
lean_inc(v_stop_5241_);
lean_dec_ref(v___x_5238_);
v___x_5242_ = lean_nat_dec_lt(v_start_5240_, v_stop_5241_);
if (v___x_5242_ == 0)
{
lean_dec(v_stop_5241_);
lean_dec(v_start_5240_);
lean_dec_ref(v_array_5239_);
lean_dec(v_j_5200_);
lean_dec(v_i_5199_);
return v_xs_5201_;
}
else
{
lean_object* v___x_5243_; uint8_t v___x_5244_; 
v___x_5243_ = lean_array_get_size(v_array_5239_);
v___x_5244_ = lean_nat_dec_le(v_stop_5241_, v___x_5243_);
if (v___x_5244_ == 0)
{
lean_dec(v_stop_5241_);
v___y_5226_ = v_array_5239_;
v___y_5227_ = v_start_5240_;
v___y_5228_ = v___x_5243_;
goto v___jp_5225_;
}
else
{
v___y_5226_ = v_array_5239_;
v___y_5227_ = v_start_5240_;
v___y_5228_ = v_stop_5241_;
goto v___jp_5225_;
}
}
}
}
}
v___jp_5202_:
{
lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
v___x_5205_ = l_Array_toSubarray___redArg(v_varyingArgs_5198_, v_lower_5203_, v_upper_5204_);
v___x_5206_ = l_Subarray_copy___redArg(v___x_5205_);
v___x_5207_ = l_Array_append___redArg(v_xs_5201_, v___x_5206_);
lean_dec_ref(v___x_5206_);
return v___x_5207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5254_, lean_object* v_fixedArgs_5255_, lean_object* v_varyingArgs_5256_, lean_object* v_i_5257_, lean_object* v_j_5258_, lean_object* v_xs_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5254_, v_fixedArgs_5255_, v_varyingArgs_5256_, v_i_5257_, v_j_5258_, v_xs_5259_);
lean_dec_ref(v_fixedArgs_5255_);
return v_res_5260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5261_, lean_object* v_perm_5262_, lean_object* v_fixedArgs_5263_, lean_object* v_varyingArgs_5264_, lean_object* v_i_5265_, lean_object* v_j_5266_, lean_object* v_xs_5267_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5262_, v_fixedArgs_5263_, v_varyingArgs_5264_, v_i_5265_, v_j_5266_, v_xs_5267_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5269_, lean_object* v_perm_5270_, lean_object* v_fixedArgs_5271_, lean_object* v_varyingArgs_5272_, lean_object* v_i_5273_, lean_object* v_j_5274_, lean_object* v_xs_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5269_, v_perm_5270_, v_fixedArgs_5271_, v_varyingArgs_5272_, v_i_5273_, v_j_5274_, v_xs_5275_);
lean_dec_ref(v_fixedArgs_5271_);
return v_res_5276_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5279_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5280_ = lean_unsigned_to_nat(2u);
v___x_5281_ = lean_unsigned_to_nat(416u);
v___x_5282_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5284_ = l_mkPanicMessageWithDecl(v___x_5283_, v___x_5282_, v___x_5281_, v___x_5280_, v___x_5279_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5285_, lean_object* v_fixedArgs_5286_, lean_object* v_varyingArgs_5287_){
_start:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; 
v___x_5288_ = lean_array_get_size(v_fixedArgs_5286_);
v___x_5289_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5285_);
v___x_5290_ = lean_nat_dec_eq(v___x_5288_, v___x_5289_);
lean_dec(v___x_5289_);
if (v___x_5290_ == 0)
{
lean_object* v___x_5291_; lean_object* v___x_5292_; 
lean_dec_ref(v_varyingArgs_5287_);
lean_dec_ref(v_perm_5285_);
v___x_5291_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5292_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5291_);
return v___x_5292_;
}
else
{
lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5293_ = lean_unsigned_to_nat(0u);
v___x_5294_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5295_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5285_, v_fixedArgs_5286_, v_varyingArgs_5287_, v___x_5293_, v___x_5293_, v___x_5294_);
return v___x_5295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5296_, lean_object* v_fixedArgs_5297_, lean_object* v_varyingArgs_5298_){
_start:
{
lean_object* v_res_5299_; 
v_res_5299_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5296_, v_fixedArgs_5297_, v_varyingArgs_5298_);
lean_dec_ref(v_fixedArgs_5297_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5300_, lean_object* v_perm_5301_, lean_object* v_fixedArgs_5302_, lean_object* v_varyingArgs_5303_){
_start:
{
lean_object* v___x_5304_; 
v___x_5304_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5301_, v_fixedArgs_5302_, v_varyingArgs_5303_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5305_, lean_object* v_perm_5306_, lean_object* v_fixedArgs_5307_, lean_object* v_varyingArgs_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5305_, v_perm_5306_, v_fixedArgs_5307_, v_varyingArgs_5308_);
lean_dec_ref(v_fixedArgs_5307_);
return v_res_5309_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5310_, lean_object* v_x_5311_){
_start:
{
if (lean_obj_tag(v_x_5310_) == 0)
{
if (lean_obj_tag(v_x_5311_) == 0)
{
uint8_t v___x_5312_; 
v___x_5312_ = 1;
return v___x_5312_;
}
else
{
uint8_t v___x_5313_; 
v___x_5313_ = 0;
return v___x_5313_;
}
}
else
{
if (lean_obj_tag(v_x_5311_) == 0)
{
uint8_t v___x_5314_; 
v___x_5314_ = 0;
return v___x_5314_;
}
else
{
lean_object* v_val_5315_; lean_object* v_val_5316_; uint8_t v___x_5317_; 
v_val_5315_ = lean_ctor_get(v_x_5310_, 0);
v_val_5316_ = lean_ctor_get(v_x_5311_, 0);
v___x_5317_ = lean_nat_dec_eq(v_val_5315_, v_val_5316_);
return v___x_5317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5318_, lean_object* v_x_5319_){
_start:
{
uint8_t v_res_5320_; lean_object* v_r_5321_; 
v_res_5320_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5318_, v_x_5319_);
lean_dec(v_x_5319_);
lean_dec(v_x_5318_);
v_r_5321_ = lean_box(v_res_5320_);
return v_r_5321_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5322_, lean_object* v_ys_5323_, lean_object* v_x_5324_){
_start:
{
lean_object* v_zero_5325_; uint8_t v_isZero_5326_; 
v_zero_5325_ = lean_unsigned_to_nat(0u);
v_isZero_5326_ = lean_nat_dec_eq(v_x_5324_, v_zero_5325_);
if (v_isZero_5326_ == 1)
{
lean_dec(v_x_5324_);
return v_isZero_5326_;
}
else
{
lean_object* v_one_5327_; lean_object* v_n_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; uint8_t v___x_5331_; 
v_one_5327_ = lean_unsigned_to_nat(1u);
v_n_5328_ = lean_nat_sub(v_x_5324_, v_one_5327_);
lean_dec(v_x_5324_);
v___x_5329_ = lean_array_fget_borrowed(v_xs_5322_, v_n_5328_);
v___x_5330_ = lean_array_fget_borrowed(v_ys_5323_, v_n_5328_);
v___x_5331_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5329_, v___x_5330_);
if (v___x_5331_ == 0)
{
lean_dec(v_n_5328_);
return v___x_5331_;
}
else
{
v_x_5324_ = v_n_5328_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5333_, lean_object* v_ys_5334_, lean_object* v_x_5335_){
_start:
{
uint8_t v_res_5336_; lean_object* v_r_5337_; 
v_res_5336_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5333_, v_ys_5334_, v_x_5335_);
lean_dec_ref(v_ys_5334_);
lean_dec_ref(v_xs_5333_);
v_r_5337_ = lean_box(v_res_5336_);
return v_r_5337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5338_, size_t v_i_5339_, lean_object* v_bs_5340_){
_start:
{
uint8_t v___x_5341_; 
v___x_5341_ = lean_usize_dec_lt(v_i_5339_, v_sz_5338_);
if (v___x_5341_ == 0)
{
return v_bs_5340_;
}
else
{
lean_object* v_v_5342_; lean_object* v___x_5343_; lean_object* v_bs_x27_5344_; lean_object* v___x_5345_; size_t v___x_5346_; size_t v___x_5347_; lean_object* v___x_5348_; 
v_v_5342_ = lean_array_uget(v_bs_5340_, v_i_5339_);
v___x_5343_ = lean_unsigned_to_nat(0u);
v_bs_x27_5344_ = lean_array_uset(v_bs_5340_, v_i_5339_, v___x_5343_);
v___x_5345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5345_, 0, v_v_5342_);
v___x_5346_ = ((size_t)1ULL);
v___x_5347_ = lean_usize_add(v_i_5339_, v___x_5346_);
v___x_5348_ = lean_array_uset(v_bs_x27_5344_, v_i_5339_, v___x_5345_);
v_i_5339_ = v___x_5347_;
v_bs_5340_ = v___x_5348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5350_, lean_object* v_i_5351_, lean_object* v_bs_5352_){
_start:
{
size_t v_sz_boxed_5353_; size_t v_i_boxed_5354_; lean_object* v_res_5355_; 
v_sz_boxed_5353_ = lean_unbox_usize(v_sz_5350_);
lean_dec(v_sz_5350_);
v_i_boxed_5354_ = lean_unbox_usize(v_i_5351_);
lean_dec(v_i_5351_);
v_res_5355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5353_, v_i_boxed_5354_, v_bs_5352_);
return v_res_5355_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5356_, lean_object* v_as_5357_, size_t v_i_5358_, size_t v_stop_5359_){
_start:
{
uint8_t v___x_5360_; 
v___x_5360_ = lean_usize_dec_eq(v_i_5358_, v_stop_5359_);
if (v___x_5360_ == 0)
{
lean_object* v_numFixed_5361_; uint8_t v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; size_t v_sz_5365_; size_t v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; uint8_t v___x_5374_; 
v_numFixed_5361_ = lean_ctor_get(v_fixedParamPerms_5356_, 0);
v___x_5362_ = 1;
v___x_5363_ = lean_array_uget_borrowed(v_as_5357_, v_i_5358_);
lean_inc(v_numFixed_5361_);
v___x_5364_ = l_Array_range(v_numFixed_5361_);
v_sz_5365_ = lean_array_size(v___x_5364_);
v___x_5366_ = ((size_t)0ULL);
v___x_5367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5365_, v___x_5366_, v___x_5364_);
v___x_5368_ = lean_array_get_size(v___x_5363_);
v___x_5369_ = lean_nat_sub(v___x_5368_, v_numFixed_5361_);
v___x_5370_ = lean_box(0);
v___x_5371_ = lean_mk_array(v___x_5369_, v___x_5370_);
v___x_5372_ = l_Array_append___redArg(v___x_5367_, v___x_5371_);
lean_dec_ref(v___x_5371_);
v___x_5373_ = lean_array_get_size(v___x_5372_);
v___x_5374_ = lean_nat_dec_eq(v___x_5368_, v___x_5373_);
if (v___x_5374_ == 0)
{
lean_dec_ref(v___x_5372_);
lean_dec_ref(v_fixedParamPerms_5356_);
return v___x_5362_;
}
else
{
uint8_t v___x_5375_; 
v___x_5375_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5363_, v___x_5372_, v___x_5368_);
lean_dec_ref(v___x_5372_);
if (v___x_5375_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5356_);
return v___x_5362_;
}
else
{
size_t v___x_5376_; size_t v___x_5377_; 
v___x_5376_ = ((size_t)1ULL);
v___x_5377_ = lean_usize_add(v_i_5358_, v___x_5376_);
v_i_5358_ = v___x_5377_;
goto _start;
}
}
}
else
{
uint8_t v___x_5379_; 
lean_dec_ref(v_fixedParamPerms_5356_);
v___x_5379_ = 0;
return v___x_5379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5380_, lean_object* v_as_5381_, lean_object* v_i_5382_, lean_object* v_stop_5383_){
_start:
{
size_t v_i_boxed_5384_; size_t v_stop_boxed_5385_; uint8_t v_res_5386_; lean_object* v_r_5387_; 
v_i_boxed_5384_ = lean_unbox_usize(v_i_5382_);
lean_dec(v_i_5382_);
v_stop_boxed_5385_ = lean_unbox_usize(v_stop_5383_);
lean_dec(v_stop_5383_);
v_res_5386_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5380_, v_as_5381_, v_i_boxed_5384_, v_stop_boxed_5385_);
lean_dec_ref(v_as_5381_);
v_r_5387_ = lean_box(v_res_5386_);
return v_r_5387_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5388_){
_start:
{
lean_object* v_perms_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; uint8_t v___x_5392_; 
v_perms_5389_ = lean_ctor_get(v_fixedParamPerms_5388_, 1);
lean_inc_ref(v_perms_5389_);
v___x_5390_ = lean_unsigned_to_nat(0u);
v___x_5391_ = lean_array_get_size(v_perms_5389_);
v___x_5392_ = lean_nat_dec_lt(v___x_5390_, v___x_5391_);
if (v___x_5392_ == 0)
{
uint8_t v___x_5393_; 
lean_dec_ref(v_perms_5389_);
lean_dec_ref(v_fixedParamPerms_5388_);
v___x_5393_ = 1;
return v___x_5393_;
}
else
{
if (v___x_5392_ == 0)
{
lean_dec_ref(v_perms_5389_);
lean_dec_ref(v_fixedParamPerms_5388_);
return v___x_5392_;
}
else
{
size_t v___x_5394_; size_t v___x_5395_; uint8_t v___x_5396_; 
v___x_5394_ = ((size_t)0ULL);
v___x_5395_ = lean_usize_of_nat(v___x_5391_);
v___x_5396_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5388_, v_perms_5389_, v___x_5394_, v___x_5395_);
lean_dec_ref(v_perms_5389_);
if (v___x_5396_ == 0)
{
return v___x_5392_;
}
else
{
uint8_t v___x_5397_; 
v___x_5397_ = 0;
return v___x_5397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5398_){
_start:
{
uint8_t v_res_5399_; lean_object* v_r_5400_; 
v_res_5399_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5398_);
v_r_5400_ = lean_box(v_res_5399_);
return v_r_5400_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5401_, lean_object* v_ys_5402_, lean_object* v_hsz_5403_, lean_object* v_x_5404_, lean_object* v_x_5405_){
_start:
{
uint8_t v___x_5406_; 
v___x_5406_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5401_, v_ys_5402_, v_x_5404_);
return v___x_5406_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5407_, lean_object* v_ys_5408_, lean_object* v_hsz_5409_, lean_object* v_x_5410_, lean_object* v_x_5411_){
_start:
{
uint8_t v_res_5412_; lean_object* v_r_5413_; 
v_res_5412_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5407_, v_ys_5408_, v_hsz_5409_, v_x_5410_, v_x_5411_);
lean_dec_ref(v_ys_5408_);
lean_dec_ref(v_xs_5407_);
v_r_5413_ = lean_box(v_res_5412_);
return v_r_5413_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5414_; 
v___x_5414_ = l_Array_instInhabited(lean_box(0));
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5415_){
_start:
{
lean_object* v___f_5416_; lean_object* v___f_5417_; lean_object* v___f_5418_; lean_object* v___f_5419_; lean_object* v___f_5420_; lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___f_5416_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5417_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5418_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5419_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5420_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5421_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5422_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5423_, 0, v___f_5416_);
lean_ctor_set(v___x_5423_, 1, v___f_5417_);
v___x_5424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5424_, 0, v___x_5423_);
lean_ctor_set(v___x_5424_, 1, v___f_5418_);
lean_ctor_set(v___x_5424_, 2, v___f_5419_);
lean_ctor_set(v___x_5424_, 3, v___f_5420_);
lean_ctor_set(v___x_5424_, 4, v___f_5421_);
v___x_5425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5425_, 0, v___x_5424_);
lean_ctor_set(v___x_5425_, 1, v___f_5422_);
v___x_5426_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5427_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5427_);
lean_ctor_set(v___x_5428_, 1, v___x_5427_);
v___x_5429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5426_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___x_5430_ = l_instInhabitedOfMonad___redArg(v___x_5425_, v___x_5429_);
v___x_5431_ = lean_panic_fn_borrowed(v___x_5430_, v_msg_5415_);
lean_dec(v___x_5430_);
return v___x_5431_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5432_; 
v___x_5432_ = l_Array_instInhabited(lean_box(0));
return v___x_5432_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5433_){
_start:
{
lean_object* v___f_5434_; lean_object* v___f_5435_; lean_object* v___f_5436_; lean_object* v___f_5437_; lean_object* v___f_5438_; lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___f_5434_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5435_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5436_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5437_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5438_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5439_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5440_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5441_, 0, v___f_5434_);
lean_ctor_set(v___x_5441_, 1, v___f_5435_);
v___x_5442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5442_, 0, v___x_5441_);
lean_ctor_set(v___x_5442_, 1, v___f_5436_);
lean_ctor_set(v___x_5442_, 2, v___f_5437_);
lean_ctor_set(v___x_5442_, 3, v___f_5438_);
lean_ctor_set(v___x_5442_, 4, v___f_5439_);
v___x_5443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5442_);
lean_ctor_set(v___x_5443_, 1, v___f_5440_);
v___x_5444_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5445_, 0, v___x_5444_);
v___x_5446_ = l_instInhabitedOfMonad___redArg(v___x_5443_, v___x_5445_);
v___x_5447_ = lean_panic_fn_borrowed(v___x_5446_, v_msg_5433_);
lean_dec(v___x_5446_);
return v___x_5447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5448_, uint8_t v___x_5449_, lean_object* v___x_5450_, lean_object* v___x_5451_, lean_object* v_as_5452_, size_t v_sz_5453_, size_t v_i_5454_, lean_object* v_b_5455_){
_start:
{
lean_object* v_a_5457_; uint8_t v___x_5461_; 
v___x_5461_ = lean_usize_dec_lt(v_i_5454_, v_sz_5453_);
if (v___x_5461_ == 0)
{
return v_b_5455_;
}
else
{
lean_object* v_fst_5462_; lean_object* v_snd_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5485_; 
v_fst_5462_ = lean_ctor_get(v_b_5455_, 0);
v_snd_5463_ = lean_ctor_get(v_b_5455_, 1);
v_isSharedCheck_5485_ = !lean_is_exclusive(v_b_5455_);
if (v_isSharedCheck_5485_ == 0)
{
v___x_5465_ = v_b_5455_;
v_isShared_5466_ = v_isSharedCheck_5485_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_snd_5463_);
lean_inc(v_fst_5462_);
lean_dec(v_b_5455_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5485_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5471_; lean_object* v_a_5472_; lean_object* v___x_5473_; 
v___x_5471_ = lean_box(0);
v_a_5472_ = lean_array_uget_borrowed(v_as_5452_, v_i_5454_);
v___x_5473_ = lean_array_get_borrowed(v___x_5471_, v___x_5448_, v_a_5472_);
if (lean_obj_tag(v___x_5473_) == 1)
{
lean_object* v_val_5474_; uint8_t v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; uint8_t v___x_5478_; 
v_val_5474_ = lean_ctor_get(v___x_5473_, 0);
v___x_5475_ = 0;
v___x_5476_ = lean_box(v___x_5475_);
v___x_5477_ = lean_array_get(v___x_5476_, v_fst_5462_, v_val_5474_);
lean_dec(v___x_5476_);
v___x_5478_ = lean_unbox(v___x_5477_);
lean_dec(v___x_5477_);
if (v___x_5478_ == 0)
{
if (v___x_5449_ == 0)
{
goto v___jp_5467_;
}
else
{
uint8_t v_changed_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
lean_del_object(v___x_5465_);
lean_dec(v_snd_5463_);
v_changed_5479_ = lean_nat_dec_eq(v___x_5450_, v___x_5451_);
v___x_5480_ = lean_box(v_changed_5479_);
v___x_5481_ = lean_array_set(v_fst_5462_, v_val_5474_, v___x_5480_);
v___x_5482_ = lean_box(v_changed_5479_);
v___x_5483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5483_, 0, v___x_5481_);
lean_ctor_set(v___x_5483_, 1, v___x_5482_);
v_a_5457_ = v___x_5483_;
goto v___jp_5456_;
}
}
else
{
goto v___jp_5467_;
}
}
else
{
lean_object* v___x_5484_; 
lean_del_object(v___x_5465_);
v___x_5484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5484_, 0, v_fst_5462_);
lean_ctor_set(v___x_5484_, 1, v_snd_5463_);
v_a_5457_ = v___x_5484_;
goto v___jp_5456_;
}
v___jp_5467_:
{
lean_object* v___x_5469_; 
if (v_isShared_5466_ == 0)
{
v___x_5469_ = v___x_5465_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_fst_5462_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v_snd_5463_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
v_a_5457_ = v___x_5469_;
goto v___jp_5456_;
}
}
}
}
v___jp_5456_:
{
size_t v___x_5458_; size_t v___x_5459_; 
v___x_5458_ = ((size_t)1ULL);
v___x_5459_ = lean_usize_add(v_i_5454_, v___x_5458_);
v_i_5454_ = v___x_5459_;
v_b_5455_ = v_a_5457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5486_, lean_object* v___x_5487_, lean_object* v___x_5488_, lean_object* v___x_5489_, lean_object* v_as_5490_, lean_object* v_sz_5491_, lean_object* v_i_5492_, lean_object* v_b_5493_){
_start:
{
uint8_t v___x_6987__boxed_5494_; size_t v_sz_boxed_5495_; size_t v_i_boxed_5496_; lean_object* v_res_5497_; 
v___x_6987__boxed_5494_ = lean_unbox(v___x_5487_);
v_sz_boxed_5495_ = lean_unbox_usize(v_sz_5491_);
lean_dec(v_sz_5491_);
v_i_boxed_5496_ = lean_unbox_usize(v_i_5492_);
lean_dec(v_i_5492_);
v_res_5497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5486_, v___x_6987__boxed_5494_, v___x_5488_, v___x_5489_, v_as_5490_, v_sz_boxed_5495_, v_i_boxed_5496_, v_b_5493_);
lean_dec_ref(v_as_5490_);
lean_dec(v___x_5489_);
lean_dec(v___x_5488_);
lean_dec_ref(v___x_5486_);
return v_res_5497_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5498_; 
v___x_5498_ = l_Array_instInhabited(lean_box(0));
return v___x_5498_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object* v_upperBound_5499_, lean_object* v___x_5500_, lean_object* v_fixedParamPerms_5501_, lean_object* v_next_5502_, lean_object* v___x_5503_, lean_object* v___x_5504_, lean_object* v_a_5505_, lean_object* v_b_5506_){
_start:
{
lean_object* v_a_5508_; uint8_t v___x_5512_; 
v___x_5512_ = lean_nat_dec_lt(v_a_5505_, v_upperBound_5499_);
if (v___x_5512_ == 0)
{
lean_dec(v_a_5505_);
return v_b_5506_;
}
else
{
lean_object* v_fst_5513_; lean_object* v_snd_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5550_; 
v_fst_5513_ = lean_ctor_get(v_b_5506_, 0);
v_snd_5514_ = lean_ctor_get(v_b_5506_, 1);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_b_5506_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5516_ = v_b_5506_;
v_isShared_5517_ = v_isSharedCheck_5550_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_snd_5514_);
lean_inc(v_fst_5513_);
lean_dec(v_b_5506_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5550_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5518_; 
v___x_5518_ = lean_array_fget_borrowed(v___x_5500_, v_a_5505_);
if (lean_obj_tag(v___x_5518_) == 1)
{
lean_object* v_val_5519_; uint8_t v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; uint8_t v___x_5523_; 
v_val_5519_ = lean_ctor_get(v___x_5518_, 0);
v___x_5520_ = 0;
v___x_5521_ = lean_box(v___x_5520_);
v___x_5522_ = lean_array_get(v___x_5521_, v_fst_5513_, v_val_5519_);
lean_dec(v___x_5521_);
v___x_5523_ = lean_unbox(v___x_5522_);
if (v___x_5523_ == 0)
{
lean_object* v___x_5525_; 
lean_dec(v___x_5522_);
if (v_isShared_5517_ == 0)
{
v___x_5525_ = v___x_5516_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_fst_5513_);
lean_ctor_set(v_reuseFailAlloc_5526_, 1, v_snd_5514_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
v_a_5508_ = v___x_5525_;
goto v___jp_5507_;
}
}
else
{
lean_object* v_revDeps_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5532_; 
v_revDeps_5527_ = lean_ctor_get(v_fixedParamPerms_5501_, 2);
v___x_5528_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0);
v___x_5529_ = lean_array_get_borrowed(v___x_5528_, v_revDeps_5527_, v_next_5502_);
v___x_5530_ = lean_array_get_borrowed(v___x_5528_, v___x_5529_, v_a_5505_);
if (v_isShared_5517_ == 0)
{
v___x_5532_ = v___x_5516_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_fst_5513_);
lean_ctor_set(v_reuseFailAlloc_5546_, 1, v_snd_5514_);
v___x_5532_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
size_t v_sz_5533_; size_t v___x_5534_; uint8_t v___x_5535_; lean_object* v___x_5536_; lean_object* v_fst_5537_; lean_object* v_snd_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5545_; 
v_sz_5533_ = lean_array_size(v___x_5530_);
v___x_5534_ = ((size_t)0ULL);
v___x_5535_ = lean_unbox(v___x_5522_);
lean_dec(v___x_5522_);
v___x_5536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5500_, v___x_5535_, v___x_5503_, v___x_5504_, v___x_5530_, v_sz_5533_, v___x_5534_, v___x_5532_);
v_fst_5537_ = lean_ctor_get(v___x_5536_, 0);
v_snd_5538_ = lean_ctor_get(v___x_5536_, 1);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5540_ = v___x_5536_;
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_snd_5538_);
lean_inc(v_fst_5537_);
lean_dec(v___x_5536_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5545_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5543_; 
if (v_isShared_5541_ == 0)
{
v___x_5543_ = v___x_5540_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_fst_5537_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v_snd_5538_);
v___x_5543_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
v_a_5508_ = v___x_5543_;
goto v___jp_5507_;
}
}
}
}
}
else
{
lean_object* v___x_5548_; 
if (v_isShared_5517_ == 0)
{
v___x_5548_ = v___x_5516_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_fst_5513_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v_snd_5514_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
v_a_5508_ = v___x_5548_;
goto v___jp_5507_;
}
}
}
}
v___jp_5507_:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; 
v___x_5509_ = lean_unsigned_to_nat(1u);
v___x_5510_ = lean_nat_add(v_a_5505_, v___x_5509_);
lean_dec(v_a_5505_);
v_a_5505_ = v___x_5510_;
v_b_5506_ = v_a_5508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object* v_upperBound_5551_, lean_object* v___x_5552_, lean_object* v_fixedParamPerms_5553_, lean_object* v_next_5554_, lean_object* v___x_5555_, lean_object* v___x_5556_, lean_object* v_a_5557_, lean_object* v_b_5558_){
_start:
{
lean_object* v_res_5559_; 
v_res_5559_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5551_, v___x_5552_, v_fixedParamPerms_5553_, v_next_5554_, v___x_5555_, v___x_5556_, v_a_5557_, v_b_5558_);
lean_dec(v___x_5556_);
lean_dec(v___x_5555_);
lean_dec(v_next_5554_);
lean_dec_ref(v_fixedParamPerms_5553_);
lean_dec_ref(v___x_5552_);
lean_dec(v_upperBound_5551_);
return v_res_5559_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5560_, lean_object* v___x_5561_, lean_object* v___x_5562_, lean_object* v___x_5563_, lean_object* v_fixedParamPerms_5564_, lean_object* v_next_5565_, lean_object* v_a_5566_, lean_object* v_b_5567_){
_start:
{
lean_object* v_a_5569_; uint8_t v___x_5573_; 
v___x_5573_ = lean_nat_dec_lt(v_a_5566_, v_upperBound_5560_);
if (v___x_5573_ == 0)
{
return v_b_5567_;
}
else
{
lean_object* v_fst_5574_; lean_object* v_snd_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5611_; 
v_fst_5574_ = lean_ctor_get(v_b_5567_, 0);
v_snd_5575_ = lean_ctor_get(v_b_5567_, 1);
v_isSharedCheck_5611_ = !lean_is_exclusive(v_b_5567_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5577_ = v_b_5567_;
v_isShared_5578_ = v_isSharedCheck_5611_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_snd_5575_);
lean_inc(v_fst_5574_);
lean_dec(v_b_5567_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5611_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5579_; 
v___x_5579_ = lean_array_fget_borrowed(v___x_5561_, v_a_5566_);
if (lean_obj_tag(v___x_5579_) == 1)
{
lean_object* v_val_5580_; uint8_t v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; uint8_t v___x_5584_; 
v_val_5580_ = lean_ctor_get(v___x_5579_, 0);
v___x_5581_ = 0;
v___x_5582_ = lean_box(v___x_5581_);
v___x_5583_ = lean_array_get(v___x_5582_, v_fst_5574_, v_val_5580_);
lean_dec(v___x_5582_);
v___x_5584_ = lean_unbox(v___x_5583_);
if (v___x_5584_ == 0)
{
lean_object* v___x_5586_; 
lean_dec(v___x_5583_);
if (v_isShared_5578_ == 0)
{
v___x_5586_ = v___x_5577_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_fst_5574_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v_snd_5575_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
v_a_5569_ = v___x_5586_;
goto v___jp_5568_;
}
}
else
{
lean_object* v_revDeps_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5593_; 
v_revDeps_5588_ = lean_ctor_get(v_fixedParamPerms_5564_, 2);
v___x_5589_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0);
v___x_5590_ = lean_array_get_borrowed(v___x_5589_, v_revDeps_5588_, v_next_5565_);
v___x_5591_ = lean_array_get_borrowed(v___x_5589_, v___x_5590_, v_a_5566_);
if (v_isShared_5578_ == 0)
{
v___x_5593_ = v___x_5577_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_fst_5574_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v_snd_5575_);
v___x_5593_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
size_t v_sz_5594_; size_t v___x_5595_; uint8_t v___x_5596_; lean_object* v___x_5597_; lean_object* v_fst_5598_; lean_object* v_snd_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5606_; 
v_sz_5594_ = lean_array_size(v___x_5591_);
v___x_5595_ = ((size_t)0ULL);
v___x_5596_ = lean_unbox(v___x_5583_);
lean_dec(v___x_5583_);
v___x_5597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5561_, v___x_5596_, v___x_5562_, v___x_5563_, v___x_5591_, v_sz_5594_, v___x_5595_, v___x_5593_);
v_fst_5598_ = lean_ctor_get(v___x_5597_, 0);
v_snd_5599_ = lean_ctor_get(v___x_5597_, 1);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5601_ = v___x_5597_;
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_snd_5599_);
lean_inc(v_fst_5598_);
lean_dec(v___x_5597_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_fst_5598_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v_snd_5599_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
v_a_5569_ = v___x_5604_;
goto v___jp_5568_;
}
}
}
}
}
else
{
lean_object* v___x_5609_; 
if (v_isShared_5578_ == 0)
{
v___x_5609_ = v___x_5577_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_fst_5574_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_snd_5575_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
v_a_5569_ = v___x_5609_;
goto v___jp_5568_;
}
}
}
}
v___jp_5568_:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; 
v___x_5570_ = lean_unsigned_to_nat(1u);
v___x_5571_ = lean_nat_add(v_a_5566_, v___x_5570_);
v___x_5572_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5560_, v___x_5561_, v_fixedParamPerms_5564_, v_next_5565_, v___x_5562_, v___x_5563_, v___x_5571_, v_a_5569_);
return v___x_5572_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5612_, lean_object* v___x_5613_, lean_object* v___x_5614_, lean_object* v___x_5615_, lean_object* v_fixedParamPerms_5616_, lean_object* v_next_5617_, lean_object* v_a_5618_, lean_object* v_b_5619_){
_start:
{
lean_object* v_res_5620_; 
v_res_5620_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5612_, v___x_5613_, v___x_5614_, v___x_5615_, v_fixedParamPerms_5616_, v_next_5617_, v_a_5618_, v_b_5619_);
lean_dec(v_a_5618_);
lean_dec(v_next_5617_);
lean_dec_ref(v_fixedParamPerms_5616_);
lean_dec(v___x_5615_);
lean_dec(v___x_5614_);
lean_dec_ref(v___x_5613_);
lean_dec(v_upperBound_5612_);
return v_res_5620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5621_, lean_object* v___x_5622_, lean_object* v___x_5623_, lean_object* v___x_5624_, lean_object* v_fixedParamPerms_5625_, lean_object* v_a_5626_, lean_object* v_b_5627_){
_start:
{
uint8_t v___x_5628_; 
v___x_5628_ = lean_nat_dec_lt(v_a_5626_, v_upperBound_5621_);
if (v___x_5628_ == 0)
{
lean_dec(v_a_5626_);
return v_b_5627_;
}
else
{
lean_object* v_fst_5629_; lean_object* v_snd_5630_; lean_object* v___x_5632_; uint8_t v_isShared_5633_; uint8_t v_isSharedCheck_5653_; 
v_fst_5629_ = lean_ctor_get(v_b_5627_, 0);
v_snd_5630_ = lean_ctor_get(v_b_5627_, 1);
v_isSharedCheck_5653_ = !lean_is_exclusive(v_b_5627_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5632_ = v_b_5627_;
v_isShared_5633_ = v_isSharedCheck_5653_;
goto v_resetjp_5631_;
}
else
{
lean_inc(v_snd_5630_);
lean_inc(v_fst_5629_);
lean_dec(v_b_5627_);
v___x_5632_ = lean_box(0);
v_isShared_5633_ = v_isSharedCheck_5653_;
goto v_resetjp_5631_;
}
v_resetjp_5631_:
{
lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5638_; 
v___x_5634_ = lean_array_fget_borrowed(v___x_5622_, v_a_5626_);
v___x_5635_ = lean_array_get_size(v___x_5634_);
v___x_5636_ = lean_unsigned_to_nat(0u);
if (v_isShared_5633_ == 0)
{
v___x_5638_ = v___x_5632_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_fst_5629_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_snd_5630_);
v___x_5638_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
lean_object* v___x_5639_; lean_object* v_fst_5640_; lean_object* v_snd_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5651_; 
v___x_5639_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5635_, v___x_5634_, v___x_5623_, v___x_5624_, v_fixedParamPerms_5625_, v_a_5626_, v___x_5636_, v___x_5638_);
v_fst_5640_ = lean_ctor_get(v___x_5639_, 0);
v_snd_5641_ = lean_ctor_get(v___x_5639_, 1);
v_isSharedCheck_5651_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5651_ == 0)
{
v___x_5643_ = v___x_5639_;
v_isShared_5644_ = v_isSharedCheck_5651_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_snd_5641_);
lean_inc(v_fst_5640_);
lean_dec(v___x_5639_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5651_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5646_; 
if (v_isShared_5644_ == 0)
{
v___x_5646_ = v___x_5643_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_fst_5640_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v_snd_5641_);
v___x_5646_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5647_ = lean_unsigned_to_nat(1u);
v___x_5648_ = lean_nat_add(v_a_5626_, v___x_5647_);
lean_dec(v_a_5626_);
v_a_5626_ = v___x_5648_;
v_b_5627_ = v___x_5646_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5654_, lean_object* v___x_5655_, lean_object* v___x_5656_, lean_object* v___x_5657_, lean_object* v_fixedParamPerms_5658_, lean_object* v_a_5659_, lean_object* v_b_5660_){
_start:
{
lean_object* v_res_5661_; 
v_res_5661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5654_, v___x_5655_, v___x_5656_, v___x_5657_, v_fixedParamPerms_5658_, v_a_5659_, v_b_5660_);
lean_dec_ref(v_fixedParamPerms_5658_);
lean_dec(v___x_5657_);
lean_dec(v___x_5656_);
lean_dec_ref(v___x_5655_);
lean_dec(v_upperBound_5654_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5662_, lean_object* v___x_5663_, lean_object* v___x_5664_, lean_object* v_fixedParamPerms_5665_, lean_object* v_a_5666_){
_start:
{
lean_object* v_snd_5667_; uint8_t v___x_5668_; 
v_snd_5667_ = lean_ctor_get(v_a_5666_, 1);
v___x_5668_ = lean_unbox(v_snd_5667_);
if (v___x_5668_ == 0)
{
lean_object* v_fst_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5676_; 
lean_inc(v_snd_5667_);
v_fst_5669_ = lean_ctor_get(v_a_5666_, 0);
v_isSharedCheck_5676_ = !lean_is_exclusive(v_a_5666_);
if (v_isSharedCheck_5676_ == 0)
{
lean_object* v_unused_5677_; 
v_unused_5677_ = lean_ctor_get(v_a_5666_, 1);
lean_dec(v_unused_5677_);
v___x_5671_ = v_a_5666_;
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_fst_5669_);
lean_dec(v_a_5666_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5676_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v___x_5674_; 
if (v_isShared_5672_ == 0)
{
v___x_5674_ = v___x_5671_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_fst_5669_);
lean_ctor_set(v_reuseFailAlloc_5675_, 1, v_snd_5667_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
else
{
lean_object* v_fst_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5699_; 
v_fst_5678_ = lean_ctor_get(v_a_5666_, 0);
v_isSharedCheck_5699_ = !lean_is_exclusive(v_a_5666_);
if (v_isSharedCheck_5699_ == 0)
{
lean_object* v_unused_5700_; 
v_unused_5700_ = lean_ctor_get(v_a_5666_, 1);
lean_dec(v_unused_5700_);
v___x_5680_ = v_a_5666_;
v_isShared_5681_ = v_isSharedCheck_5699_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_fst_5678_);
lean_dec(v_a_5666_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5699_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
uint8_t v_changed_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5686_; 
v_changed_5682_ = 0;
v___x_5683_ = lean_unsigned_to_nat(0u);
v___x_5684_ = lean_box(v_changed_5682_);
if (v_isShared_5681_ == 0)
{
lean_ctor_set(v___x_5680_, 1, v___x_5684_);
v___x_5686_ = v___x_5680_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_fst_5678_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v___x_5684_);
v___x_5686_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
lean_object* v___x_5687_; lean_object* v_fst_5688_; lean_object* v_snd_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5697_; 
v___x_5687_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5662_, v___x_5663_, v___x_5664_, v___x_5662_, v_fixedParamPerms_5665_, v___x_5683_, v___x_5686_);
v_fst_5688_ = lean_ctor_get(v___x_5687_, 0);
v_snd_5689_ = lean_ctor_get(v___x_5687_, 1);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5687_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5691_ = v___x_5687_;
v_isShared_5692_ = v_isSharedCheck_5697_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_snd_5689_);
lean_inc(v_fst_5688_);
lean_dec(v___x_5687_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5697_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___x_5694_; 
if (v_isShared_5692_ == 0)
{
v___x_5694_ = v___x_5691_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_fst_5688_);
lean_ctor_set(v_reuseFailAlloc_5696_, 1, v_snd_5689_);
v___x_5694_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
v_a_5666_ = v___x_5694_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5701_, lean_object* v___x_5702_, lean_object* v___x_5703_, lean_object* v_fixedParamPerms_5704_, lean_object* v_a_5705_){
_start:
{
lean_object* v_res_5706_; 
v_res_5706_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5701_, v___x_5702_, v___x_5703_, v_fixedParamPerms_5704_, v_a_5705_);
lean_dec_ref(v_fixedParamPerms_5704_);
lean_dec(v___x_5703_);
lean_dec_ref(v___x_5702_);
lean_dec(v___x_5701_);
return v_res_5706_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5707_, lean_object* v_a_5708_, lean_object* v_b_5709_){
_start:
{
lean_object* v_a_5711_; uint8_t v___x_5715_; 
v___x_5715_ = lean_nat_dec_lt(v_a_5708_, v_upperBound_5707_);
if (v___x_5715_ == 0)
{
lean_dec(v_a_5708_);
return v_b_5709_;
}
else
{
lean_object* v_snd_5716_; lean_object* v_snd_5717_; lean_object* v_snd_5718_; lean_object* v_snd_5719_; lean_object* v_fst_5720_; lean_object* v___x_5722_; uint8_t v_isShared_5723_; uint8_t v_isSharedCheck_5832_; 
v_snd_5716_ = lean_ctor_get(v_b_5709_, 1);
lean_inc(v_snd_5716_);
v_snd_5717_ = lean_ctor_get(v_snd_5716_, 1);
lean_inc(v_snd_5717_);
v_snd_5718_ = lean_ctor_get(v_snd_5717_, 1);
lean_inc(v_snd_5718_);
v_snd_5719_ = lean_ctor_get(v_snd_5718_, 1);
lean_inc(v_snd_5719_);
v_fst_5720_ = lean_ctor_get(v_b_5709_, 0);
v_isSharedCheck_5832_ = !lean_is_exclusive(v_b_5709_);
if (v_isSharedCheck_5832_ == 0)
{
lean_object* v_unused_5833_; 
v_unused_5833_ = lean_ctor_get(v_b_5709_, 1);
lean_dec(v_unused_5833_);
v___x_5722_ = v_b_5709_;
v_isShared_5723_ = v_isSharedCheck_5832_;
goto v_resetjp_5721_;
}
else
{
lean_inc(v_fst_5720_);
lean_dec(v_b_5709_);
v___x_5722_ = lean_box(0);
v_isShared_5723_ = v_isSharedCheck_5832_;
goto v_resetjp_5721_;
}
v_resetjp_5721_:
{
lean_object* v_fst_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5830_; 
v_fst_5724_ = lean_ctor_get(v_snd_5716_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v_snd_5716_);
if (v_isSharedCheck_5830_ == 0)
{
lean_object* v_unused_5831_; 
v_unused_5831_ = lean_ctor_get(v_snd_5716_, 1);
lean_dec(v_unused_5831_);
v___x_5726_ = v_snd_5716_;
v_isShared_5727_ = v_isSharedCheck_5830_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_fst_5724_);
lean_dec(v_snd_5716_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5830_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v_fst_5728_; lean_object* v___x_5730_; uint8_t v_isShared_5731_; uint8_t v_isSharedCheck_5828_; 
v_fst_5728_ = lean_ctor_get(v_snd_5717_, 0);
v_isSharedCheck_5828_ = !lean_is_exclusive(v_snd_5717_);
if (v_isSharedCheck_5828_ == 0)
{
lean_object* v_unused_5829_; 
v_unused_5829_ = lean_ctor_get(v_snd_5717_, 1);
lean_dec(v_unused_5829_);
v___x_5730_ = v_snd_5717_;
v_isShared_5731_ = v_isSharedCheck_5828_;
goto v_resetjp_5729_;
}
else
{
lean_inc(v_fst_5728_);
lean_dec(v_snd_5717_);
v___x_5730_ = lean_box(0);
v_isShared_5731_ = v_isSharedCheck_5828_;
goto v_resetjp_5729_;
}
v_resetjp_5729_:
{
lean_object* v_fst_5732_; lean_object* v___x_5734_; uint8_t v_isShared_5735_; uint8_t v_isSharedCheck_5826_; 
v_fst_5732_ = lean_ctor_get(v_snd_5718_, 0);
v_isSharedCheck_5826_ = !lean_is_exclusive(v_snd_5718_);
if (v_isSharedCheck_5826_ == 0)
{
lean_object* v_unused_5827_; 
v_unused_5827_ = lean_ctor_get(v_snd_5718_, 1);
lean_dec(v_unused_5827_);
v___x_5734_ = v_snd_5718_;
v_isShared_5735_ = v_isSharedCheck_5826_;
goto v_resetjp_5733_;
}
else
{
lean_inc(v_fst_5732_);
lean_dec(v_snd_5718_);
v___x_5734_ = lean_box(0);
v_isShared_5735_ = v_isSharedCheck_5826_;
goto v_resetjp_5733_;
}
v_resetjp_5733_:
{
lean_object* v_array_5736_; lean_object* v_start_5737_; lean_object* v_stop_5738_; uint8_t v___x_5739_; 
v_array_5736_ = lean_ctor_get(v_snd_5719_, 0);
v_start_5737_ = lean_ctor_get(v_snd_5719_, 1);
v_stop_5738_ = lean_ctor_get(v_snd_5719_, 2);
v___x_5739_ = lean_nat_dec_lt(v_start_5737_, v_stop_5738_);
if (v___x_5739_ == 0)
{
lean_object* v___x_5741_; 
lean_dec(v_a_5708_);
if (v_isShared_5735_ == 0)
{
v___x_5741_ = v___x_5734_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_fst_5732_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v_snd_5719_);
v___x_5741_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
lean_object* v___x_5743_; 
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 1, v___x_5741_);
v___x_5743_ = v___x_5730_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_fst_5728_);
lean_ctor_set(v_reuseFailAlloc_5750_, 1, v___x_5741_);
v___x_5743_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
lean_object* v___x_5745_; 
if (v_isShared_5727_ == 0)
{
lean_ctor_set(v___x_5726_, 1, v___x_5743_);
v___x_5745_ = v___x_5726_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_fst_5724_);
lean_ctor_set(v_reuseFailAlloc_5749_, 1, v___x_5743_);
v___x_5745_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
lean_object* v___x_5747_; 
if (v_isShared_5723_ == 0)
{
lean_ctor_set(v___x_5722_, 1, v___x_5745_);
v___x_5747_ = v___x_5722_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5748_; 
v_reuseFailAlloc_5748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5748_, 0, v_fst_5720_);
lean_ctor_set(v_reuseFailAlloc_5748_, 1, v___x_5745_);
v___x_5747_ = v_reuseFailAlloc_5748_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
return v___x_5747_;
}
}
}
}
}
else
{
lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5822_; 
lean_inc(v_stop_5738_);
lean_inc(v_start_5737_);
lean_inc_ref(v_array_5736_);
v_isSharedCheck_5822_ = !lean_is_exclusive(v_snd_5719_);
if (v_isSharedCheck_5822_ == 0)
{
lean_object* v_unused_5823_; lean_object* v_unused_5824_; lean_object* v_unused_5825_; 
v_unused_5823_ = lean_ctor_get(v_snd_5719_, 2);
lean_dec(v_unused_5823_);
v_unused_5824_ = lean_ctor_get(v_snd_5719_, 1);
lean_dec(v_unused_5824_);
v_unused_5825_ = lean_ctor_get(v_snd_5719_, 0);
lean_dec(v_unused_5825_);
v___x_5753_ = v_snd_5719_;
v_isShared_5754_ = v_isSharedCheck_5822_;
goto v_resetjp_5752_;
}
else
{
lean_dec(v_snd_5719_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5822_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v_array_5755_; lean_object* v_start_5756_; lean_object* v_stop_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5762_; 
v_array_5755_ = lean_ctor_get(v_fst_5732_, 0);
v_start_5756_ = lean_ctor_get(v_fst_5732_, 1);
v_stop_5757_ = lean_ctor_get(v_fst_5732_, 2);
v___x_5758_ = lean_array_fget(v_array_5736_, v_start_5737_);
v___x_5759_ = lean_unsigned_to_nat(1u);
v___x_5760_ = lean_nat_add(v_start_5737_, v___x_5759_);
lean_dec(v_start_5737_);
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 1, v___x_5760_);
v___x_5762_ = v___x_5753_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_array_5736_);
lean_ctor_set(v_reuseFailAlloc_5821_, 1, v___x_5760_);
lean_ctor_set(v_reuseFailAlloc_5821_, 2, v_stop_5738_);
v___x_5762_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
uint8_t v___x_5763_; 
v___x_5763_ = lean_nat_dec_lt(v_start_5756_, v_stop_5757_);
if (v___x_5763_ == 0)
{
lean_object* v___x_5765_; 
lean_dec(v___x_5758_);
lean_dec(v_a_5708_);
if (v_isShared_5735_ == 0)
{
lean_ctor_set(v___x_5734_, 1, v___x_5762_);
v___x_5765_ = v___x_5734_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_fst_5732_);
lean_ctor_set(v_reuseFailAlloc_5775_, 1, v___x_5762_);
v___x_5765_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
lean_object* v___x_5767_; 
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 1, v___x_5765_);
v___x_5767_ = v___x_5730_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_fst_5728_);
lean_ctor_set(v_reuseFailAlloc_5774_, 1, v___x_5765_);
v___x_5767_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
lean_object* v___x_5769_; 
if (v_isShared_5727_ == 0)
{
lean_ctor_set(v___x_5726_, 1, v___x_5767_);
v___x_5769_ = v___x_5726_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_fst_5724_);
lean_ctor_set(v_reuseFailAlloc_5773_, 1, v___x_5767_);
v___x_5769_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
lean_object* v___x_5771_; 
if (v_isShared_5723_ == 0)
{
lean_ctor_set(v___x_5722_, 1, v___x_5769_);
v___x_5771_ = v___x_5722_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_fst_5720_);
lean_ctor_set(v_reuseFailAlloc_5772_, 1, v___x_5769_);
v___x_5771_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
return v___x_5771_;
}
}
}
}
}
else
{
lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5817_; 
lean_inc(v_stop_5757_);
lean_inc(v_start_5756_);
lean_inc_ref(v_array_5755_);
v_isSharedCheck_5817_ = !lean_is_exclusive(v_fst_5732_);
if (v_isSharedCheck_5817_ == 0)
{
lean_object* v_unused_5818_; lean_object* v_unused_5819_; lean_object* v_unused_5820_; 
v_unused_5818_ = lean_ctor_get(v_fst_5732_, 2);
lean_dec(v_unused_5818_);
v_unused_5819_ = lean_ctor_get(v_fst_5732_, 1);
lean_dec(v_unused_5819_);
v_unused_5820_ = lean_ctor_get(v_fst_5732_, 0);
lean_dec(v_unused_5820_);
v___x_5777_ = v_fst_5732_;
v_isShared_5778_ = v_isSharedCheck_5817_;
goto v_resetjp_5776_;
}
else
{
lean_dec(v_fst_5732_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5817_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5782_; 
v___x_5779_ = lean_array_fget(v_array_5755_, v_start_5756_);
v___x_5780_ = lean_nat_add(v_start_5756_, v___x_5759_);
lean_dec(v_start_5756_);
if (v_isShared_5778_ == 0)
{
lean_ctor_set(v___x_5777_, 1, v___x_5780_);
v___x_5782_ = v___x_5777_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_array_5755_);
lean_ctor_set(v_reuseFailAlloc_5816_, 1, v___x_5780_);
lean_ctor_set(v_reuseFailAlloc_5816_, 2, v_stop_5757_);
v___x_5782_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
uint8_t v___x_5783_; 
v___x_5783_ = lean_unbox(v___x_5779_);
lean_dec(v___x_5779_);
if (v___x_5783_ == 0)
{
lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5789_; 
v___x_5784_ = lean_array_get_size(v_fst_5728_);
v___x_5785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5785_, 0, v___x_5784_);
v___x_5786_ = lean_array_push(v_fst_5720_, v___x_5785_);
v___x_5787_ = lean_array_push(v_fst_5728_, v___x_5758_);
if (v_isShared_5735_ == 0)
{
lean_ctor_set(v___x_5734_, 1, v___x_5762_);
lean_ctor_set(v___x_5734_, 0, v___x_5782_);
v___x_5789_ = v___x_5734_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v___x_5782_);
lean_ctor_set(v_reuseFailAlloc_5799_, 1, v___x_5762_);
v___x_5789_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
lean_object* v___x_5791_; 
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 1, v___x_5789_);
lean_ctor_set(v___x_5730_, 0, v___x_5787_);
v___x_5791_ = v___x_5730_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v___x_5787_);
lean_ctor_set(v_reuseFailAlloc_5798_, 1, v___x_5789_);
v___x_5791_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
lean_object* v___x_5793_; 
if (v_isShared_5727_ == 0)
{
lean_ctor_set(v___x_5726_, 1, v___x_5791_);
v___x_5793_ = v___x_5726_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_fst_5724_);
lean_ctor_set(v_reuseFailAlloc_5797_, 1, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
lean_object* v___x_5795_; 
if (v_isShared_5723_ == 0)
{
lean_ctor_set(v___x_5722_, 1, v___x_5793_);
lean_ctor_set(v___x_5722_, 0, v___x_5786_);
v___x_5795_ = v___x_5722_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5786_);
lean_ctor_set(v_reuseFailAlloc_5796_, 1, v___x_5793_);
v___x_5795_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
v_a_5711_ = v___x_5795_;
goto v___jp_5710_;
}
}
}
}
}
else
{
lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5805_; 
v___x_5800_ = lean_box(0);
v___x_5801_ = lean_array_push(v_fst_5720_, v___x_5800_);
v___x_5802_ = l_Lean_Expr_fvarId_x21(v___x_5758_);
lean_dec(v___x_5758_);
v___x_5803_ = lean_array_push(v_fst_5724_, v___x_5802_);
if (v_isShared_5735_ == 0)
{
lean_ctor_set(v___x_5734_, 1, v___x_5762_);
lean_ctor_set(v___x_5734_, 0, v___x_5782_);
v___x_5805_ = v___x_5734_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v___x_5782_);
lean_ctor_set(v_reuseFailAlloc_5815_, 1, v___x_5762_);
v___x_5805_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
lean_object* v___x_5807_; 
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 1, v___x_5805_);
v___x_5807_ = v___x_5730_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_fst_5728_);
lean_ctor_set(v_reuseFailAlloc_5814_, 1, v___x_5805_);
v___x_5807_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
lean_object* v___x_5809_; 
if (v_isShared_5727_ == 0)
{
lean_ctor_set(v___x_5726_, 1, v___x_5807_);
lean_ctor_set(v___x_5726_, 0, v___x_5803_);
v___x_5809_ = v___x_5726_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5803_);
lean_ctor_set(v_reuseFailAlloc_5813_, 1, v___x_5807_);
v___x_5809_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
lean_object* v___x_5811_; 
if (v_isShared_5723_ == 0)
{
lean_ctor_set(v___x_5722_, 1, v___x_5809_);
lean_ctor_set(v___x_5722_, 0, v___x_5801_);
v___x_5811_ = v___x_5722_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5801_);
lean_ctor_set(v_reuseFailAlloc_5812_, 1, v___x_5809_);
v___x_5811_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
v_a_5711_ = v___x_5811_;
goto v___jp_5710_;
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
v___jp_5710_:
{
lean_object* v___x_5712_; lean_object* v___x_5713_; 
v___x_5712_ = lean_unsigned_to_nat(1u);
v___x_5713_ = lean_nat_add(v_a_5708_, v___x_5712_);
lean_dec(v_a_5708_);
v_a_5708_ = v___x_5713_;
v_b_5709_ = v_a_5711_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5834_, lean_object* v_a_5835_, lean_object* v_b_5836_){
_start:
{
lean_object* v_res_5837_; 
v_res_5837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5834_, v_a_5835_, v_b_5836_);
lean_dec(v_upperBound_5834_);
return v_res_5837_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5838_, size_t v_i_5839_, size_t v_stop_5840_){
_start:
{
uint8_t v___x_5841_; 
v___x_5841_ = lean_usize_dec_eq(v_i_5839_, v_stop_5840_);
if (v___x_5841_ == 0)
{
lean_object* v___x_5842_; uint8_t v___x_5843_; 
v___x_5842_ = lean_array_uget_borrowed(v_as_5838_, v_i_5839_);
v___x_5843_ = l_Lean_Expr_isFVar(v___x_5842_);
if (v___x_5843_ == 0)
{
uint8_t v___x_5844_; 
v___x_5844_ = 1;
return v___x_5844_;
}
else
{
size_t v___x_5845_; size_t v___x_5846_; 
v___x_5845_ = ((size_t)1ULL);
v___x_5846_ = lean_usize_add(v_i_5839_, v___x_5845_);
v_i_5839_ = v___x_5846_;
goto _start;
}
}
else
{
uint8_t v___x_5848_; 
v___x_5848_ = 0;
return v___x_5848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5849_, lean_object* v_i_5850_, lean_object* v_stop_5851_){
_start:
{
size_t v_i_boxed_5852_; size_t v_stop_boxed_5853_; uint8_t v_res_5854_; lean_object* v_r_5855_; 
v_i_boxed_5852_ = lean_unbox_usize(v_i_5850_);
lean_dec(v_i_5850_);
v_stop_boxed_5853_ = lean_unbox_usize(v_stop_5851_);
lean_dec(v_stop_5851_);
v_res_5854_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5849_, v_i_boxed_5852_, v_stop_boxed_5853_);
lean_dec_ref(v_as_5849_);
v_r_5855_ = lean_box(v_res_5854_);
return v_r_5855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5856_, size_t v_sz_5857_, size_t v_i_5858_, lean_object* v_bs_5859_){
_start:
{
uint8_t v___x_5860_; 
v___x_5860_ = lean_usize_dec_lt(v_i_5858_, v_sz_5857_);
if (v___x_5860_ == 0)
{
return v_bs_5859_;
}
else
{
lean_object* v_v_5861_; lean_object* v___x_5862_; lean_object* v_bs_x27_5863_; lean_object* v___y_5865_; 
v_v_5861_ = lean_array_uget(v_bs_5859_, v_i_5858_);
v___x_5862_ = lean_unsigned_to_nat(0u);
v_bs_x27_5863_ = lean_array_uset(v_bs_5859_, v_i_5858_, v___x_5862_);
if (lean_obj_tag(v_v_5861_) == 0)
{
v___y_5865_ = v_v_5861_;
goto v___jp_5864_;
}
else
{
lean_object* v_val_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; 
v_val_5870_ = lean_ctor_get(v_v_5861_, 0);
lean_inc(v_val_5870_);
lean_dec_ref_known(v_v_5861_, 1);
v___x_5871_ = lean_box(0);
v___x_5872_ = lean_array_get_borrowed(v___x_5871_, v___x_5856_, v_val_5870_);
lean_dec(v_val_5870_);
lean_inc(v___x_5872_);
v___y_5865_ = v___x_5872_;
goto v___jp_5864_;
}
v___jp_5864_:
{
size_t v___x_5866_; size_t v___x_5867_; lean_object* v___x_5868_; 
v___x_5866_ = ((size_t)1ULL);
v___x_5867_ = lean_usize_add(v_i_5858_, v___x_5866_);
v___x_5868_ = lean_array_uset(v_bs_x27_5863_, v_i_5858_, v___y_5865_);
v_i_5858_ = v___x_5867_;
v_bs_5859_ = v___x_5868_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5873_, lean_object* v_sz_5874_, lean_object* v_i_5875_, lean_object* v_bs_5876_){
_start:
{
size_t v_sz_boxed_5877_; size_t v_i_boxed_5878_; lean_object* v_res_5879_; 
v_sz_boxed_5877_ = lean_unbox_usize(v_sz_5874_);
lean_dec(v_sz_5874_);
v_i_boxed_5878_ = lean_unbox_usize(v_i_5875_);
lean_dec(v_i_5875_);
v_res_5879_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5873_, v_sz_boxed_5877_, v_i_boxed_5878_, v_bs_5876_);
lean_dec_ref(v___x_5873_);
return v_res_5879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5880_, size_t v_sz_5881_, size_t v_i_5882_, lean_object* v_bs_5883_){
_start:
{
uint8_t v___x_5884_; 
v___x_5884_ = lean_usize_dec_lt(v_i_5882_, v_sz_5881_);
if (v___x_5884_ == 0)
{
return v_bs_5883_;
}
else
{
lean_object* v_v_5885_; lean_object* v___x_5886_; lean_object* v_bs_x27_5887_; size_t v_sz_5888_; size_t v___x_5889_; lean_object* v___x_5890_; size_t v___x_5891_; size_t v___x_5892_; lean_object* v___x_5893_; 
v_v_5885_ = lean_array_uget(v_bs_5883_, v_i_5882_);
v___x_5886_ = lean_unsigned_to_nat(0u);
v_bs_x27_5887_ = lean_array_uset(v_bs_5883_, v_i_5882_, v___x_5886_);
v_sz_5888_ = lean_array_size(v_v_5885_);
v___x_5889_ = ((size_t)0ULL);
v___x_5890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5880_, v_sz_5888_, v___x_5889_, v_v_5885_);
v___x_5891_ = ((size_t)1ULL);
v___x_5892_ = lean_usize_add(v_i_5882_, v___x_5891_);
v___x_5893_ = lean_array_uset(v_bs_x27_5887_, v_i_5882_, v___x_5890_);
v_i_5882_ = v___x_5892_;
v_bs_5883_ = v___x_5893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5895_, lean_object* v_sz_5896_, lean_object* v_i_5897_, lean_object* v_bs_5898_){
_start:
{
size_t v_sz_boxed_5899_; size_t v_i_boxed_5900_; lean_object* v_res_5901_; 
v_sz_boxed_5899_ = lean_unbox_usize(v_sz_5896_);
lean_dec(v_sz_5896_);
v_i_boxed_5900_ = lean_unbox_usize(v_i_5897_);
lean_dec(v_i_5897_);
v_res_5901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5895_, v_sz_boxed_5899_, v_i_boxed_5900_, v_bs_5898_);
lean_dec_ref(v___x_5895_);
return v_res_5901_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; 
v___x_5904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5905_ = lean_unsigned_to_nat(6u);
v___x_5906_ = lean_unsigned_to_nat(463u);
v___x_5907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5909_ = l_mkPanicMessageWithDecl(v___x_5908_, v___x_5907_, v___x_5906_, v___x_5905_, v___x_5904_);
return v___x_5909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5910_, lean_object* v___x_5911_, lean_object* v___x_5912_, lean_object* v_as_5913_, size_t v_sz_5914_, size_t v_i_5915_, lean_object* v_b_5916_){
_start:
{
lean_object* v_a_5918_; uint8_t v___x_5922_; 
v___x_5922_ = lean_usize_dec_lt(v_i_5915_, v_sz_5914_);
if (v___x_5922_ == 0)
{
return v_b_5916_;
}
else
{
lean_object* v_a_5923_; lean_object* v___x_5924_; uint8_t v___x_5925_; 
v_a_5923_ = lean_array_uget_borrowed(v_as_5913_, v_i_5915_);
v___x_5924_ = lean_array_get_size(v___x_5910_);
v___x_5925_ = lean_nat_dec_lt(v_a_5923_, v___x_5924_);
if (v___x_5925_ == 0)
{
lean_object* v___x_5926_; lean_object* v___x_5927_; 
lean_dec_ref(v_b_5916_);
v___x_5926_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5927_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5926_);
if (lean_obj_tag(v___x_5927_) == 0)
{
lean_object* v_a_5928_; 
v_a_5928_ = lean_ctor_get(v___x_5927_, 0);
lean_inc(v_a_5928_);
lean_dec_ref_known(v___x_5927_, 1);
return v_a_5928_;
}
else
{
lean_object* v_a_5929_; 
v_a_5929_ = lean_ctor_get(v___x_5927_, 0);
lean_inc(v_a_5929_);
lean_dec_ref_known(v___x_5927_, 1);
v_a_5918_ = v_a_5929_;
goto v___jp_5917_;
}
}
else
{
lean_object* v___x_5930_; lean_object* v___x_5931_; 
v___x_5930_ = lean_box(0);
v___x_5931_ = lean_array_get_borrowed(v___x_5930_, v___x_5910_, v_a_5923_);
if (lean_obj_tag(v___x_5931_) == 1)
{
lean_object* v_val_5932_; uint8_t v_changed_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; 
v_val_5932_ = lean_ctor_get(v___x_5931_, 0);
v_changed_5933_ = lean_nat_dec_eq(v___x_5911_, v___x_5912_);
v___x_5934_ = lean_box(v_changed_5933_);
v___x_5935_ = lean_array_set(v_b_5916_, v_val_5932_, v___x_5934_);
v_a_5918_ = v___x_5935_;
goto v___jp_5917_;
}
else
{
v_a_5918_ = v_b_5916_;
goto v___jp_5917_;
}
}
}
v___jp_5917_:
{
size_t v___x_5919_; size_t v___x_5920_; 
v___x_5919_ = ((size_t)1ULL);
v___x_5920_ = lean_usize_add(v_i_5915_, v___x_5919_);
v_i_5915_ = v___x_5920_;
v_b_5916_ = v_a_5918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5936_, lean_object* v___x_5937_, lean_object* v___x_5938_, lean_object* v_as_5939_, lean_object* v_sz_5940_, lean_object* v_i_5941_, lean_object* v_b_5942_){
_start:
{
size_t v_sz_boxed_5943_; size_t v_i_boxed_5944_; lean_object* v_res_5945_; 
v_sz_boxed_5943_ = lean_unbox_usize(v_sz_5940_);
lean_dec(v_sz_5940_);
v_i_boxed_5944_ = lean_unbox_usize(v_i_5941_);
lean_dec(v_i_5941_);
v_res_5945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5936_, v___x_5937_, v___x_5938_, v_as_5939_, v_sz_boxed_5943_, v_i_boxed_5944_, v_b_5942_);
lean_dec_ref(v_as_5939_);
lean_dec(v___x_5938_);
lean_dec(v___x_5937_);
lean_dec_ref(v___x_5936_);
return v_res_5945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5946_, lean_object* v___x_5947_, lean_object* v___x_5948_, lean_object* v_a_5949_, lean_object* v_b_5950_){
_start:
{
uint8_t v___x_5951_; 
v___x_5951_ = lean_nat_dec_lt(v_a_5949_, v_upperBound_5946_);
if (v___x_5951_ == 0)
{
lean_dec(v_a_5949_);
return v_b_5950_;
}
else
{
lean_object* v_snd_5952_; lean_object* v_snd_5953_; lean_object* v_fst_5954_; lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_6020_; 
v_snd_5952_ = lean_ctor_get(v_b_5950_, 1);
lean_inc(v_snd_5952_);
v_snd_5953_ = lean_ctor_get(v_snd_5952_, 1);
lean_inc(v_snd_5953_);
v_fst_5954_ = lean_ctor_get(v_b_5950_, 0);
v_isSharedCheck_6020_ = !lean_is_exclusive(v_b_5950_);
if (v_isSharedCheck_6020_ == 0)
{
lean_object* v_unused_6021_; 
v_unused_6021_ = lean_ctor_get(v_b_5950_, 1);
lean_dec(v_unused_6021_);
v___x_5956_ = v_b_5950_;
v_isShared_5957_ = v_isSharedCheck_6020_;
goto v_resetjp_5955_;
}
else
{
lean_inc(v_fst_5954_);
lean_dec(v_b_5950_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_6020_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
lean_object* v_fst_5958_; lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_6018_; 
v_fst_5958_ = lean_ctor_get(v_snd_5952_, 0);
v_isSharedCheck_6018_ = !lean_is_exclusive(v_snd_5952_);
if (v_isSharedCheck_6018_ == 0)
{
lean_object* v_unused_6019_; 
v_unused_6019_ = lean_ctor_get(v_snd_5952_, 1);
lean_dec(v_unused_6019_);
v___x_5960_ = v_snd_5952_;
v_isShared_5961_ = v_isSharedCheck_6018_;
goto v_resetjp_5959_;
}
else
{
lean_inc(v_fst_5958_);
lean_dec(v_snd_5952_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_6018_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v_array_5962_; lean_object* v_start_5963_; lean_object* v_stop_5964_; uint8_t v___x_5965_; 
v_array_5962_ = lean_ctor_get(v_snd_5953_, 0);
v_start_5963_ = lean_ctor_get(v_snd_5953_, 1);
v_stop_5964_ = lean_ctor_get(v_snd_5953_, 2);
v___x_5965_ = lean_nat_dec_lt(v_start_5963_, v_stop_5964_);
if (v___x_5965_ == 0)
{
lean_object* v___x_5967_; 
lean_dec(v_a_5949_);
if (v_isShared_5961_ == 0)
{
v___x_5967_ = v___x_5960_;
goto v_reusejp_5966_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_fst_5958_);
lean_ctor_set(v_reuseFailAlloc_5971_, 1, v_snd_5953_);
v___x_5967_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5966_;
}
v_reusejp_5966_:
{
lean_object* v___x_5969_; 
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 1, v___x_5967_);
v___x_5969_ = v___x_5956_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_fst_5954_);
lean_ctor_set(v_reuseFailAlloc_5970_, 1, v___x_5967_);
v___x_5969_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
return v___x_5969_;
}
}
}
else
{
lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_6014_; 
lean_inc(v_stop_5964_);
lean_inc(v_start_5963_);
lean_inc_ref(v_array_5962_);
v_isSharedCheck_6014_ = !lean_is_exclusive(v_snd_5953_);
if (v_isSharedCheck_6014_ == 0)
{
lean_object* v_unused_6015_; lean_object* v_unused_6016_; lean_object* v_unused_6017_; 
v_unused_6015_ = lean_ctor_get(v_snd_5953_, 2);
lean_dec(v_unused_6015_);
v_unused_6016_ = lean_ctor_get(v_snd_5953_, 1);
lean_dec(v_unused_6016_);
v_unused_6017_ = lean_ctor_get(v_snd_5953_, 0);
lean_dec(v_unused_6017_);
v___x_5973_ = v_snd_5953_;
v_isShared_5974_ = v_isSharedCheck_6014_;
goto v_resetjp_5972_;
}
else
{
lean_dec(v_snd_5953_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_6014_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v_array_5975_; lean_object* v_start_5976_; lean_object* v_stop_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5982_; 
v_array_5975_ = lean_ctor_get(v_fst_5958_, 0);
v_start_5976_ = lean_ctor_get(v_fst_5958_, 1);
v_stop_5977_ = lean_ctor_get(v_fst_5958_, 2);
v___x_5978_ = lean_array_fget(v_array_5962_, v_start_5963_);
v___x_5979_ = lean_unsigned_to_nat(1u);
v___x_5980_ = lean_nat_add(v_start_5963_, v___x_5979_);
lean_dec(v_start_5963_);
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 1, v___x_5980_);
v___x_5982_ = v___x_5973_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_array_5962_);
lean_ctor_set(v_reuseFailAlloc_6013_, 1, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_6013_, 2, v_stop_5964_);
v___x_5982_ = v_reuseFailAlloc_6013_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
uint8_t v___x_5983_; 
v___x_5983_ = lean_nat_dec_lt(v_start_5976_, v_stop_5977_);
if (v___x_5983_ == 0)
{
lean_object* v___x_5985_; 
lean_dec(v___x_5978_);
lean_dec(v_a_5949_);
if (v_isShared_5961_ == 0)
{
lean_ctor_set(v___x_5960_, 1, v___x_5982_);
v___x_5985_ = v___x_5960_;
goto v_reusejp_5984_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_fst_5958_);
lean_ctor_set(v_reuseFailAlloc_5989_, 1, v___x_5982_);
v___x_5985_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5984_;
}
v_reusejp_5984_:
{
lean_object* v___x_5987_; 
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 1, v___x_5985_);
v___x_5987_ = v___x_5956_;
goto v_reusejp_5986_;
}
else
{
lean_object* v_reuseFailAlloc_5988_; 
v_reuseFailAlloc_5988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5988_, 0, v_fst_5954_);
lean_ctor_set(v_reuseFailAlloc_5988_, 1, v___x_5985_);
v___x_5987_ = v_reuseFailAlloc_5988_;
goto v_reusejp_5986_;
}
v_reusejp_5986_:
{
return v___x_5987_;
}
}
}
else
{
lean_object* v___x_5991_; uint8_t v_isShared_5992_; uint8_t v_isSharedCheck_6009_; 
lean_inc(v_stop_5977_);
lean_inc(v_start_5976_);
lean_inc_ref(v_array_5975_);
v_isSharedCheck_6009_ = !lean_is_exclusive(v_fst_5958_);
if (v_isSharedCheck_6009_ == 0)
{
lean_object* v_unused_6010_; lean_object* v_unused_6011_; lean_object* v_unused_6012_; 
v_unused_6010_ = lean_ctor_get(v_fst_5958_, 2);
lean_dec(v_unused_6010_);
v_unused_6011_ = lean_ctor_get(v_fst_5958_, 1);
lean_dec(v_unused_6011_);
v_unused_6012_ = lean_ctor_get(v_fst_5958_, 0);
lean_dec(v_unused_6012_);
v___x_5991_ = v_fst_5958_;
v_isShared_5992_ = v_isSharedCheck_6009_;
goto v_resetjp_5990_;
}
else
{
lean_dec(v_fst_5958_);
v___x_5991_ = lean_box(0);
v_isShared_5992_ = v_isSharedCheck_6009_;
goto v_resetjp_5990_;
}
v_resetjp_5990_:
{
lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5996_; 
v___x_5993_ = lean_array_fget(v_array_5975_, v_start_5976_);
v___x_5994_ = lean_nat_add(v_start_5976_, v___x_5979_);
lean_dec(v_start_5976_);
if (v_isShared_5992_ == 0)
{
lean_ctor_set(v___x_5991_, 1, v___x_5994_);
v___x_5996_ = v___x_5991_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v_array_5975_);
lean_ctor_set(v_reuseFailAlloc_6008_, 1, v___x_5994_);
lean_ctor_set(v_reuseFailAlloc_6008_, 2, v_stop_5977_);
v___x_5996_ = v_reuseFailAlloc_6008_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
size_t v_sz_5997_; size_t v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6001_; 
v_sz_5997_ = lean_array_size(v___x_5993_);
v___x_5998_ = ((size_t)0ULL);
v___x_5999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5978_, v___x_5947_, v___x_5948_, v___x_5993_, v_sz_5997_, v___x_5998_, v_fst_5954_);
lean_dec(v___x_5993_);
lean_dec(v___x_5978_);
if (v_isShared_5961_ == 0)
{
lean_ctor_set(v___x_5960_, 1, v___x_5982_);
lean_ctor_set(v___x_5960_, 0, v___x_5996_);
v___x_6001_ = v___x_5960_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v___x_5996_);
lean_ctor_set(v_reuseFailAlloc_6007_, 1, v___x_5982_);
v___x_6001_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
lean_object* v___x_6003_; 
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 1, v___x_6001_);
lean_ctor_set(v___x_5956_, 0, v___x_5999_);
v___x_6003_ = v___x_5956_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6006_; 
v_reuseFailAlloc_6006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6006_, 0, v___x_5999_);
lean_ctor_set(v_reuseFailAlloc_6006_, 1, v___x_6001_);
v___x_6003_ = v_reuseFailAlloc_6006_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
lean_object* v___x_6004_; 
v___x_6004_ = lean_nat_add(v_a_5949_, v___x_5979_);
lean_dec(v_a_5949_);
v_a_5949_ = v___x_6004_;
v_b_5950_ = v___x_6003_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6022_, lean_object* v___x_6023_, lean_object* v___x_6024_, lean_object* v_a_6025_, lean_object* v_b_6026_){
_start:
{
lean_object* v_res_6027_; 
v_res_6027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6022_, v___x_6023_, v___x_6024_, v_a_6025_, v_b_6026_);
lean_dec(v___x_6024_);
lean_dec(v___x_6023_);
lean_dec(v_upperBound_6022_);
return v_res_6027_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6029_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6030_ = lean_unsigned_to_nat(2u);
v___x_6031_ = lean_unsigned_to_nat(457u);
v___x_6032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6033_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6034_ = l_mkPanicMessageWithDecl(v___x_6033_, v___x_6032_, v___x_6031_, v___x_6030_, v___x_6029_);
return v___x_6034_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; 
v___x_6036_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6037_ = lean_unsigned_to_nat(2u);
v___x_6038_ = lean_unsigned_to_nat(458u);
v___x_6039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6040_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6041_ = l_mkPanicMessageWithDecl(v___x_6040_, v___x_6039_, v___x_6038_, v___x_6037_, v___x_6036_);
return v___x_6041_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; 
v___x_6043_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6044_ = lean_unsigned_to_nat(2u);
v___x_6045_ = lean_unsigned_to_nat(456u);
v___x_6046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6047_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6048_ = l_mkPanicMessageWithDecl(v___x_6047_, v___x_6046_, v___x_6045_, v___x_6044_, v___x_6043_);
return v___x_6048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6049_, lean_object* v_xs_6050_, lean_object* v_toErase_6051_){
_start:
{
lean_object* v___x_6052_; lean_object* v___x_6053_; uint8_t v___x_6137_; 
v___x_6052_ = lean_unsigned_to_nat(0u);
v___x_6053_ = lean_array_get_size(v_xs_6050_);
v___x_6137_ = lean_nat_dec_lt(v___x_6052_, v___x_6053_);
if (v___x_6137_ == 0)
{
goto v___jp_6054_;
}
else
{
if (v___x_6137_ == 0)
{
goto v___jp_6054_;
}
else
{
size_t v___x_6138_; size_t v___x_6139_; uint8_t v___x_6140_; 
v___x_6138_ = ((size_t)0ULL);
v___x_6139_ = lean_usize_of_nat(v___x_6053_);
v___x_6140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6050_, v___x_6138_, v___x_6139_);
if (v___x_6140_ == 0)
{
goto v___jp_6054_;
}
else
{
lean_object* v___x_6141_; lean_object* v___x_6142_; 
lean_dec_ref(v_toErase_6051_);
lean_dec_ref(v_xs_6050_);
lean_dec_ref(v_fixedParamPerms_6049_);
v___x_6141_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6142_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6141_);
return v___x_6142_;
}
}
}
v___jp_6054_:
{
lean_object* v_numFixed_6055_; lean_object* v_perms_6056_; lean_object* v_revDeps_6057_; uint8_t v___x_6058_; 
v_numFixed_6055_ = lean_ctor_get(v_fixedParamPerms_6049_, 0);
v_perms_6056_ = lean_ctor_get(v_fixedParamPerms_6049_, 1);
lean_inc_ref(v_perms_6056_);
v_revDeps_6057_ = lean_ctor_get(v_fixedParamPerms_6049_, 2);
lean_inc_ref(v_revDeps_6057_);
v___x_6058_ = lean_nat_dec_eq(v_numFixed_6055_, v___x_6053_);
if (v___x_6058_ == 0)
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
lean_dec_ref(v_revDeps_6057_);
lean_dec_ref(v_perms_6056_);
lean_dec_ref(v_toErase_6051_);
lean_dec_ref(v_xs_6050_);
lean_dec_ref(v_fixedParamPerms_6049_);
v___x_6059_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6060_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6059_);
return v___x_6060_;
}
else
{
lean_object* v___x_6061_; lean_object* v___x_6062_; uint8_t v_changed_6063_; 
v___x_6061_ = lean_array_get_size(v_toErase_6051_);
v___x_6062_ = lean_array_get_size(v_perms_6056_);
v_changed_6063_ = lean_nat_dec_eq(v___x_6061_, v___x_6062_);
if (v_changed_6063_ == 0)
{
lean_object* v___x_6064_; lean_object* v___x_6065_; 
lean_dec_ref(v_revDeps_6057_);
lean_dec_ref(v_perms_6056_);
lean_dec_ref(v_toErase_6051_);
lean_dec_ref(v_xs_6050_);
lean_dec_ref(v_fixedParamPerms_6049_);
v___x_6064_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6065_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6064_);
return v___x_6065_;
}
else
{
uint8_t v_changed_6066_; lean_object* v___x_6067_; lean_object* v_mask_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v_fst_6074_; lean_object* v___x_6076_; uint8_t v_isShared_6077_; uint8_t v_isSharedCheck_6135_; 
v_changed_6066_ = 0;
v___x_6067_ = lean_box(v_changed_6066_);
lean_inc(v_numFixed_6055_);
v_mask_6068_ = lean_mk_array(v_numFixed_6055_, v___x_6067_);
v___x_6069_ = l_Array_toSubarray___redArg(v_toErase_6051_, v___x_6052_, v___x_6061_);
lean_inc_ref(v_perms_6056_);
v___x_6070_ = l_Array_toSubarray___redArg(v_perms_6056_, v___x_6052_, v___x_6062_);
v___x_6071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6069_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6072_, 0, v_mask_6068_);
lean_ctor_set(v___x_6072_, 1, v___x_6071_);
v___x_6073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6061_, v___x_6061_, v___x_6062_, v___x_6052_, v___x_6072_);
v_fst_6074_ = lean_ctor_get(v___x_6073_, 0);
v_isSharedCheck_6135_ = !lean_is_exclusive(v___x_6073_);
if (v_isSharedCheck_6135_ == 0)
{
lean_object* v_unused_6136_; 
v_unused_6136_ = lean_ctor_get(v___x_6073_, 1);
lean_dec(v_unused_6136_);
v___x_6076_ = v___x_6073_;
v_isShared_6077_ = v_isSharedCheck_6135_;
goto v_resetjp_6075_;
}
else
{
lean_inc(v_fst_6074_);
lean_dec(v___x_6073_);
v___x_6076_ = lean_box(0);
v_isShared_6077_ = v_isSharedCheck_6135_;
goto v_resetjp_6075_;
}
v_resetjp_6075_:
{
lean_object* v___x_6078_; lean_object* v___x_6080_; 
v___x_6078_ = lean_box(v_changed_6063_);
if (v_isShared_6077_ == 0)
{
lean_ctor_set(v___x_6076_, 1, v___x_6078_);
v___x_6080_ = v___x_6076_;
goto v_reusejp_6079_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_fst_6074_);
lean_ctor_set(v_reuseFailAlloc_6134_, 1, v___x_6078_);
v___x_6080_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6079_;
}
v_reusejp_6079_:
{
lean_object* v___x_6081_; lean_object* v___x_6083_; uint8_t v_isShared_6084_; uint8_t v_isSharedCheck_6130_; 
v___x_6081_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6062_, v_perms_6056_, v___x_6061_, v_fixedParamPerms_6049_, v___x_6080_);
v_isSharedCheck_6130_ = !lean_is_exclusive(v_fixedParamPerms_6049_);
if (v_isSharedCheck_6130_ == 0)
{
lean_object* v_unused_6131_; lean_object* v_unused_6132_; lean_object* v_unused_6133_; 
v_unused_6131_ = lean_ctor_get(v_fixedParamPerms_6049_, 2);
lean_dec(v_unused_6131_);
v_unused_6132_ = lean_ctor_get(v_fixedParamPerms_6049_, 1);
lean_dec(v_unused_6132_);
v_unused_6133_ = lean_ctor_get(v_fixedParamPerms_6049_, 0);
lean_dec(v_unused_6133_);
v___x_6083_ = v_fixedParamPerms_6049_;
v_isShared_6084_ = v_isSharedCheck_6130_;
goto v_resetjp_6082_;
}
else
{
lean_dec(v_fixedParamPerms_6049_);
v___x_6083_ = lean_box(0);
v_isShared_6084_ = v_isSharedCheck_6130_;
goto v_resetjp_6082_;
}
v_resetjp_6082_:
{
lean_object* v_fst_6085_; lean_object* v___x_6087_; uint8_t v_isShared_6088_; uint8_t v_isSharedCheck_6128_; 
v_fst_6085_ = lean_ctor_get(v___x_6081_, 0);
v_isSharedCheck_6128_ = !lean_is_exclusive(v___x_6081_);
if (v_isSharedCheck_6128_ == 0)
{
lean_object* v_unused_6129_; 
v_unused_6129_ = lean_ctor_get(v___x_6081_, 1);
lean_dec(v_unused_6129_);
v___x_6087_ = v___x_6081_;
v_isShared_6088_ = v_isSharedCheck_6128_;
goto v_resetjp_6086_;
}
else
{
lean_inc(v_fst_6085_);
lean_dec(v___x_6081_);
v___x_6087_ = lean_box(0);
v_isShared_6088_ = v_isSharedCheck_6128_;
goto v_resetjp_6086_;
}
v_resetjp_6086_:
{
lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6094_; 
v___x_6089_ = lean_array_get_size(v_fst_6085_);
v___x_6090_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6091_ = l_Array_toSubarray___redArg(v_fst_6085_, v___x_6052_, v___x_6089_);
v___x_6092_ = l_Array_toSubarray___redArg(v_xs_6050_, v___x_6052_, v___x_6053_);
if (v_isShared_6088_ == 0)
{
lean_ctor_set(v___x_6087_, 1, v___x_6092_);
lean_ctor_set(v___x_6087_, 0, v___x_6091_);
v___x_6094_ = v___x_6087_;
goto v_reusejp_6093_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v___x_6091_);
lean_ctor_set(v_reuseFailAlloc_6127_, 1, v___x_6092_);
v___x_6094_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6093_;
}
v_reusejp_6093_:
{
lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v_snd_6099_; lean_object* v_snd_6100_; lean_object* v_fst_6101_; lean_object* v_fst_6102_; lean_object* v___x_6104_; uint8_t v_isShared_6105_; uint8_t v_isSharedCheck_6125_; 
v___x_6095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6090_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v___x_6096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6090_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
v___x_6097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6090_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6089_, v___x_6052_, v___x_6097_);
v_snd_6099_ = lean_ctor_get(v___x_6098_, 1);
lean_inc(v_snd_6099_);
v_snd_6100_ = lean_ctor_get(v_snd_6099_, 1);
lean_inc(v_snd_6100_);
v_fst_6101_ = lean_ctor_get(v___x_6098_, 0);
lean_inc(v_fst_6101_);
lean_dec_ref(v___x_6098_);
v_fst_6102_ = lean_ctor_get(v_snd_6099_, 0);
v_isSharedCheck_6125_ = !lean_is_exclusive(v_snd_6099_);
if (v_isSharedCheck_6125_ == 0)
{
lean_object* v_unused_6126_; 
v_unused_6126_ = lean_ctor_get(v_snd_6099_, 1);
lean_dec(v_unused_6126_);
v___x_6104_ = v_snd_6099_;
v_isShared_6105_ = v_isSharedCheck_6125_;
goto v_resetjp_6103_;
}
else
{
lean_inc(v_fst_6102_);
lean_dec(v_snd_6099_);
v___x_6104_ = lean_box(0);
v_isShared_6105_ = v_isSharedCheck_6125_;
goto v_resetjp_6103_;
}
v_resetjp_6103_:
{
lean_object* v_fst_6106_; lean_object* v___x_6108_; uint8_t v_isShared_6109_; uint8_t v_isSharedCheck_6123_; 
v_fst_6106_ = lean_ctor_get(v_snd_6100_, 0);
v_isSharedCheck_6123_ = !lean_is_exclusive(v_snd_6100_);
if (v_isSharedCheck_6123_ == 0)
{
lean_object* v_unused_6124_; 
v_unused_6124_ = lean_ctor_get(v_snd_6100_, 1);
lean_dec(v_unused_6124_);
v___x_6108_ = v_snd_6100_;
v_isShared_6109_ = v_isSharedCheck_6123_;
goto v_resetjp_6107_;
}
else
{
lean_inc(v_fst_6106_);
lean_dec(v_snd_6100_);
v___x_6108_ = lean_box(0);
v_isShared_6109_ = v_isSharedCheck_6123_;
goto v_resetjp_6107_;
}
v_resetjp_6107_:
{
lean_object* v___x_6110_; size_t v_sz_6111_; size_t v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6115_; 
v___x_6110_ = lean_array_get_size(v_fst_6106_);
v_sz_6111_ = lean_array_size(v_perms_6056_);
v___x_6112_ = ((size_t)0ULL);
v___x_6113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6101_, v_sz_6111_, v___x_6112_, v_perms_6056_);
lean_dec(v_fst_6101_);
if (v_isShared_6084_ == 0)
{
lean_ctor_set(v___x_6083_, 1, v___x_6113_);
lean_ctor_set(v___x_6083_, 0, v___x_6110_);
v___x_6115_ = v___x_6083_;
goto v_reusejp_6114_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v___x_6110_);
lean_ctor_set(v_reuseFailAlloc_6122_, 1, v___x_6113_);
lean_ctor_set(v_reuseFailAlloc_6122_, 2, v_revDeps_6057_);
v___x_6115_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6114_;
}
v_reusejp_6114_:
{
lean_object* v___x_6117_; 
if (v_isShared_6109_ == 0)
{
lean_ctor_set(v___x_6108_, 1, v_fst_6102_);
v___x_6117_ = v___x_6108_;
goto v_reusejp_6116_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v_fst_6106_);
lean_ctor_set(v_reuseFailAlloc_6121_, 1, v_fst_6102_);
v___x_6117_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6116_;
}
v_reusejp_6116_:
{
lean_object* v___x_6119_; 
if (v_isShared_6105_ == 0)
{
lean_ctor_set(v___x_6104_, 1, v___x_6117_);
lean_ctor_set(v___x_6104_, 0, v___x_6115_);
v___x_6119_ = v___x_6104_;
goto v_reusejp_6118_;
}
else
{
lean_object* v_reuseFailAlloc_6120_; 
v_reuseFailAlloc_6120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6120_, 0, v___x_6115_);
lean_ctor_set(v_reuseFailAlloc_6120_, 1, v___x_6117_);
v___x_6119_ = v_reuseFailAlloc_6120_;
goto v_reusejp_6118_;
}
v_reusejp_6118_:
{
return v___x_6119_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6143_, lean_object* v___x_6144_, lean_object* v___x_6145_, lean_object* v___x_6146_, lean_object* v_fixedParamPerms_6147_, lean_object* v_next_6148_, lean_object* v_inst_6149_, lean_object* v_R_6150_, lean_object* v_a_6151_, lean_object* v_b_6152_, lean_object* v_c_6153_){
_start:
{
lean_object* v___x_6154_; 
v___x_6154_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6143_, v___x_6144_, v___x_6145_, v___x_6146_, v_fixedParamPerms_6147_, v_next_6148_, v_a_6151_, v_b_6152_);
return v___x_6154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6155_, lean_object* v___x_6156_, lean_object* v___x_6157_, lean_object* v___x_6158_, lean_object* v_fixedParamPerms_6159_, lean_object* v_next_6160_, lean_object* v_inst_6161_, lean_object* v_R_6162_, lean_object* v_a_6163_, lean_object* v_b_6164_, lean_object* v_c_6165_){
_start:
{
lean_object* v_res_6166_; 
v_res_6166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6155_, v___x_6156_, v___x_6157_, v___x_6158_, v_fixedParamPerms_6159_, v_next_6160_, v_inst_6161_, v_R_6162_, v_a_6163_, v_b_6164_, v_c_6165_);
lean_dec(v_a_6163_);
lean_dec(v_next_6160_);
lean_dec_ref(v_fixedParamPerms_6159_);
lean_dec(v___x_6158_);
lean_dec(v___x_6157_);
lean_dec_ref(v___x_6156_);
lean_dec(v_upperBound_6155_);
return v_res_6166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6167_, lean_object* v___x_6168_, lean_object* v___x_6169_, lean_object* v___x_6170_, lean_object* v_fixedParamPerms_6171_, lean_object* v_inst_6172_, lean_object* v_R_6173_, lean_object* v_a_6174_, lean_object* v_b_6175_, lean_object* v_c_6176_){
_start:
{
lean_object* v___x_6177_; 
v___x_6177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6167_, v___x_6168_, v___x_6169_, v___x_6170_, v_fixedParamPerms_6171_, v_a_6174_, v_b_6175_);
return v___x_6177_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6178_, lean_object* v___x_6179_, lean_object* v___x_6180_, lean_object* v___x_6181_, lean_object* v_fixedParamPerms_6182_, lean_object* v_inst_6183_, lean_object* v_R_6184_, lean_object* v_a_6185_, lean_object* v_b_6186_, lean_object* v_c_6187_){
_start:
{
lean_object* v_res_6188_; 
v_res_6188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6178_, v___x_6179_, v___x_6180_, v___x_6181_, v_fixedParamPerms_6182_, v_inst_6183_, v_R_6184_, v_a_6185_, v_b_6186_, v_c_6187_);
lean_dec_ref(v_fixedParamPerms_6182_);
lean_dec(v___x_6181_);
lean_dec(v___x_6180_);
lean_dec_ref(v___x_6179_);
lean_dec(v_upperBound_6178_);
return v_res_6188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6189_, lean_object* v___x_6190_, lean_object* v___x_6191_, lean_object* v_fixedParamPerms_6192_, lean_object* v_inst_6193_, lean_object* v_a_6194_){
_start:
{
lean_object* v___x_6195_; 
v___x_6195_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6189_, v___x_6190_, v___x_6191_, v_fixedParamPerms_6192_, v_a_6194_);
return v___x_6195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6196_, lean_object* v___x_6197_, lean_object* v___x_6198_, lean_object* v_fixedParamPerms_6199_, lean_object* v_inst_6200_, lean_object* v_a_6201_){
_start:
{
lean_object* v_res_6202_; 
v_res_6202_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6196_, v___x_6197_, v___x_6198_, v_fixedParamPerms_6199_, v_inst_6200_, v_a_6201_);
lean_dec_ref(v_fixedParamPerms_6199_);
lean_dec(v___x_6198_);
lean_dec_ref(v___x_6197_);
lean_dec(v___x_6196_);
return v_res_6202_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6203_, lean_object* v_inst_6204_, lean_object* v_R_6205_, lean_object* v_a_6206_, lean_object* v_b_6207_, lean_object* v_c_6208_){
_start:
{
lean_object* v___x_6209_; 
v___x_6209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6203_, v_a_6206_, v_b_6207_);
return v___x_6209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6210_, lean_object* v_inst_6211_, lean_object* v_R_6212_, lean_object* v_a_6213_, lean_object* v_b_6214_, lean_object* v_c_6215_){
_start:
{
lean_object* v_res_6216_; 
v_res_6216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6210_, v_inst_6211_, v_R_6212_, v_a_6213_, v_b_6214_, v_c_6215_);
lean_dec(v_upperBound_6210_);
return v_res_6216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6217_, lean_object* v___x_6218_, lean_object* v___x_6219_, lean_object* v_inst_6220_, lean_object* v_R_6221_, lean_object* v_a_6222_, lean_object* v_b_6223_, lean_object* v_c_6224_){
_start:
{
lean_object* v___x_6225_; 
v___x_6225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6217_, v___x_6218_, v___x_6219_, v_a_6222_, v_b_6223_);
return v___x_6225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6226_, lean_object* v___x_6227_, lean_object* v___x_6228_, lean_object* v_inst_6229_, lean_object* v_R_6230_, lean_object* v_a_6231_, lean_object* v_b_6232_, lean_object* v_c_6233_){
_start:
{
lean_object* v_res_6234_; 
v_res_6234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6226_, v___x_6227_, v___x_6228_, v_inst_6229_, v_R_6230_, v_a_6231_, v_b_6232_, v_c_6233_);
lean_dec(v___x_6228_);
lean_dec(v___x_6227_);
lean_dec(v_upperBound_6226_);
return v_res_6234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object* v_upperBound_6235_, lean_object* v___x_6236_, lean_object* v_fixedParamPerms_6237_, lean_object* v_next_6238_, lean_object* v___x_6239_, lean_object* v___x_6240_, lean_object* v_inst_6241_, lean_object* v_R_6242_, lean_object* v_a_6243_, lean_object* v_b_6244_, lean_object* v_c_6245_){
_start:
{
lean_object* v___x_6246_; 
v___x_6246_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_6235_, v___x_6236_, v_fixedParamPerms_6237_, v_next_6238_, v___x_6239_, v___x_6240_, v_a_6243_, v_b_6244_);
return v___x_6246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object* v_upperBound_6247_, lean_object* v___x_6248_, lean_object* v_fixedParamPerms_6249_, lean_object* v_next_6250_, lean_object* v___x_6251_, lean_object* v___x_6252_, lean_object* v_inst_6253_, lean_object* v_R_6254_, lean_object* v_a_6255_, lean_object* v_b_6256_, lean_object* v_c_6257_){
_start:
{
lean_object* v_res_6258_; 
v_res_6258_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(v_upperBound_6247_, v___x_6248_, v_fixedParamPerms_6249_, v_next_6250_, v___x_6251_, v___x_6252_, v_inst_6253_, v_R_6254_, v_a_6255_, v_b_6256_, v_c_6257_);
lean_dec(v___x_6252_);
lean_dec(v___x_6251_);
lean_dec(v_next_6250_);
lean_dec_ref(v_fixedParamPerms_6249_);
lean_dec_ref(v___x_6248_);
lean_dec(v_upperBound_6247_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6316_; uint8_t v___x_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; 
v___x_6316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6317_ = 0;
v___x_6318_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6319_ = l_Lean_registerTraceClass(v___x_6316_, v___x_6317_, v___x_6318_);
return v___x_6319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6320_){
_start:
{
lean_object* v_res_6321_; 
v_res_6321_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6321_;
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
