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
lean_object* v___f_1009_; lean_object* v___x_27048__overap_1010_; lean_object* v___x_1011_; 
v___f_1009_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_27048__overap_1010_ = lean_panic_fn_borrowed(v___f_1009_, v_msg_1003_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
v___x_1011_ = lean_apply_5(v___x_27048__overap_1010_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, lean_box(0));
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
v_options_1087_ = lean_ctor_get(v___y_1079_, 1);
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
v_ref_1110_ = lean_ctor_get(v___y_1107_, 4);
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
lean_object* v___y_1469_; lean_object* v_toCold_1478_; lean_object* v_options_1479_; lean_object* v_currRecDepth_1480_; lean_object* v_maxRecDepth_1481_; lean_object* v_ref_1482_; lean_object* v_currNamespace_1483_; lean_object* v_openDecls_1484_; lean_object* v_initHeartbeats_1485_; lean_object* v_maxHeartbeats_1486_; lean_object* v_currMacroScope_1487_; uint8_t v_diag_1488_; uint8_t v_suppressElabErrors_1489_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_toCold_1478_ = lean_ctor_get(v___y_1465_, 0);
v_options_1479_ = lean_ctor_get(v___y_1465_, 1);
v_currRecDepth_1480_ = lean_ctor_get(v___y_1465_, 2);
v_maxRecDepth_1481_ = lean_ctor_get(v___y_1465_, 3);
v_ref_1482_ = lean_ctor_get(v___y_1465_, 4);
v_currNamespace_1483_ = lean_ctor_get(v___y_1465_, 5);
v_openDecls_1484_ = lean_ctor_get(v___y_1465_, 6);
v_initHeartbeats_1485_ = lean_ctor_get(v___y_1465_, 7);
v_maxHeartbeats_1486_ = lean_ctor_get(v___y_1465_, 8);
v_currMacroScope_1487_ = lean_ctor_get(v___y_1465_, 9);
v_diag_1488_ = lean_ctor_get_uint8(v___y_1465_, sizeof(void*)*10);
v_suppressElabErrors_1489_ = lean_ctor_get_uint8(v___y_1465_, sizeof(void*)*10 + 1);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_nat_dec_eq(v_maxRecDepth_1481_, v___x_1495_);
if (v___x_1496_ == 0)
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_nat_dec_eq(v_currRecDepth_1480_, v_maxRecDepth_1481_);
if (v___x_1497_ == 0)
{
goto v___jp_1490_;
}
else
{
lean_object* v___x_1498_; 
lean_dec_ref(v_x_1461_);
lean_inc(v_ref_1482_);
v___x_1498_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1482_);
v___y_1469_ = v___x_1498_;
goto v___jp_1468_;
}
}
else
{
goto v___jp_1490_;
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
v___jp_1490_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1491_ = lean_unsigned_to_nat(1u);
v___x_1492_ = lean_nat_add(v_currRecDepth_1480_, v___x_1491_);
lean_inc(v_currMacroScope_1487_);
lean_inc(v_maxHeartbeats_1486_);
lean_inc(v_initHeartbeats_1485_);
lean_inc(v_openDecls_1484_);
lean_inc(v_currNamespace_1483_);
lean_inc(v_ref_1482_);
lean_inc(v_maxRecDepth_1481_);
lean_inc_ref(v_options_1479_);
lean_inc_ref(v_toCold_1478_);
v___x_1493_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1493_, 0, v_toCold_1478_);
lean_ctor_set(v___x_1493_, 1, v_options_1479_);
lean_ctor_set(v___x_1493_, 2, v___x_1492_);
lean_ctor_set(v___x_1493_, 3, v_maxRecDepth_1481_);
lean_ctor_set(v___x_1493_, 4, v_ref_1482_);
lean_ctor_set(v___x_1493_, 5, v_currNamespace_1483_);
lean_ctor_set(v___x_1493_, 6, v_openDecls_1484_);
lean_ctor_set(v___x_1493_, 7, v_initHeartbeats_1485_);
lean_ctor_set(v___x_1493_, 8, v_maxHeartbeats_1486_);
lean_ctor_set(v___x_1493_, 9, v_currMacroScope_1487_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*10, v_diag_1488_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*10 + 1, v_suppressElabErrors_1489_);
lean_inc(v___y_1466_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc(v___y_1462_);
v___x_1494_ = lean_apply_6(v_x_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___x_1493_, v___y_1466_, lean_box(0));
v___y_1469_ = v___x_1494_;
goto v___jp_1468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1507_, lean_object* v_x_1508_){
_start:
{
if (lean_obj_tag(v_x_1508_) == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_box(0);
return v___x_1509_;
}
else
{
lean_object* v_key_1510_; lean_object* v_value_1511_; lean_object* v_tail_1512_; uint8_t v___x_1513_; 
v_key_1510_ = lean_ctor_get(v_x_1508_, 0);
v_value_1511_ = lean_ctor_get(v_x_1508_, 1);
v_tail_1512_ = lean_ctor_get(v_x_1508_, 2);
v___x_1513_ = l_Lean_ExprStructEq_beq(v_key_1510_, v_a_1507_);
if (v___x_1513_ == 0)
{
v_x_1508_ = v_tail_1512_;
goto _start;
}
else
{
lean_object* v___x_1515_; 
lean_inc(v_value_1511_);
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_value_1511_);
return v___x_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1516_, v_x_1517_);
lean_dec(v_x_1517_);
lean_dec_ref(v_a_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_buckets_1521_; lean_object* v___x_1522_; uint64_t v___x_1523_; uint64_t v___x_1524_; uint64_t v___x_1525_; uint64_t v_fold_1526_; uint64_t v___x_1527_; uint64_t v___x_1528_; uint64_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; size_t v___x_1533_; size_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_buckets_1521_ = lean_ctor_get(v_m_1519_, 1);
v___x_1522_ = lean_array_get_size(v_buckets_1521_);
v___x_1523_ = l_Lean_ExprStructEq_hash(v_a_1520_);
v___x_1524_ = 32ULL;
v___x_1525_ = lean_uint64_shift_right(v___x_1523_, v___x_1524_);
v_fold_1526_ = lean_uint64_xor(v___x_1523_, v___x_1525_);
v___x_1527_ = 16ULL;
v___x_1528_ = lean_uint64_shift_right(v_fold_1526_, v___x_1527_);
v___x_1529_ = lean_uint64_xor(v_fold_1526_, v___x_1528_);
v___x_1530_ = lean_uint64_to_usize(v___x_1529_);
v___x_1531_ = lean_usize_of_nat(v___x_1522_);
v___x_1532_ = ((size_t)1ULL);
v___x_1533_ = lean_usize_sub(v___x_1531_, v___x_1532_);
v___x_1534_ = lean_usize_land(v___x_1530_, v___x_1533_);
v___x_1535_ = lean_array_uget_borrowed(v_buckets_1521_, v___x_1534_);
v___x_1536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1520_, v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1537_, v_a_1538_);
lean_dec_ref(v_a_1538_);
lean_dec_ref(v_m_1537_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1543_, lean_object* v_pre_1544_, lean_object* v_post_1545_, uint8_t v_usedLetOnly_1546_, uint8_t v_skipConstInApp_1547_, uint8_t v_skipInstances_1548_, lean_object* v_body_1549_, lean_object* v_x_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = lean_array_push(v_fvars_1543_, v_x_1550_);
v___x_1558_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1544_, v_post_1545_, v_usedLetOnly_1546_, v_skipConstInApp_1547_, v_skipInstances_1548_, v___x_1557_, v_body_1549_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1559_, lean_object* v_pre_1560_, lean_object* v_post_1561_, lean_object* v_usedLetOnly_1562_, lean_object* v_skipConstInApp_1563_, lean_object* v_skipInstances_1564_, lean_object* v_body_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
uint8_t v_usedLetOnly_boxed_1573_; uint8_t v_skipConstInApp_boxed_1574_; uint8_t v_skipInstances_boxed_1575_; lean_object* v_res_1576_; 
v_usedLetOnly_boxed_1573_ = lean_unbox(v_usedLetOnly_1562_);
v_skipConstInApp_boxed_1574_ = lean_unbox(v_skipConstInApp_1563_);
v_skipInstances_boxed_1575_ = lean_unbox(v_skipInstances_1564_);
v_res_1576_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1559_, v_pre_1560_, v_post_1561_, v_usedLetOnly_boxed_1573_, v_skipConstInApp_boxed_1574_, v_skipInstances_boxed_1575_, v_body_1565_, v_x_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1577_, lean_object* v_post_1578_, uint8_t v_usedLetOnly_1579_, uint8_t v_skipConstInApp_1580_, uint8_t v_skipInstances_1581_, lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
lean_inc_ref(v_post_1578_);
lean_inc(v___y_1587_);
lean_inc_ref(v___y_1586_);
lean_inc(v___y_1585_);
lean_inc_ref(v___y_1584_);
lean_inc_ref(v_e_1582_);
v___x_1589_ = lean_apply_6(v_post_1578_, v_e_1582_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, lean_box(0));
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1608_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1608_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1608_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
switch(lean_obj_tag(v_a_1590_))
{
case 0:
{
lean_object* v_e_1594_; lean_object* v___x_1596_; 
lean_dec_ref(v_e_1582_);
lean_dec_ref(v_post_1578_);
lean_dec_ref(v_pre_1577_);
v_e_1594_ = lean_ctor_get(v_a_1590_, 0);
lean_inc_ref(v_e_1594_);
lean_dec_ref_known(v_a_1590_, 1);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_e_1594_);
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_e_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
case 1:
{
lean_object* v_e_1598_; lean_object* v___x_1599_; 
lean_del_object(v___x_1592_);
lean_dec_ref(v_e_1582_);
v_e_1598_ = lean_ctor_get(v_a_1590_, 0);
lean_inc_ref(v_e_1598_);
lean_dec_ref_known(v_a_1590_, 1);
v___x_1599_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1577_, v_post_1578_, v_usedLetOnly_1579_, v_skipConstInApp_1580_, v_skipInstances_1581_, v_e_1598_, v_a_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1599_;
}
default: 
{
lean_object* v_e_x3f_1600_; 
lean_dec_ref(v_post_1578_);
lean_dec_ref(v_pre_1577_);
v_e_x3f_1600_ = lean_ctor_get(v_a_1590_, 0);
lean_inc(v_e_x3f_1600_);
lean_dec_ref_known(v_a_1590_, 1);
if (lean_obj_tag(v_e_x3f_1600_) == 0)
{
lean_object* v___x_1602_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_e_1582_);
v___x_1602_ = v___x_1592_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_e_1582_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1606_; 
lean_dec_ref(v_e_1582_);
v_val_1604_ = lean_ctor_get(v_e_x3f_1600_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v_e_x3f_1600_, 1);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_val_1604_);
v___x_1606_ = v___x_1592_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_val_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec_ref(v_e_1582_);
lean_dec_ref(v_post_1578_);
lean_dec_ref(v_pre_1577_);
v_a_1609_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1589_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1589_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1617_, lean_object* v_post_1618_, uint8_t v_usedLetOnly_1619_, uint8_t v_skipConstInApp_1620_, uint8_t v_skipInstances_1621_, lean_object* v_fvars_1622_, lean_object* v_e_1623_, lean_object* v_a_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
if (lean_obj_tag(v_e_1623_) == 6)
{
lean_object* v_binderName_1630_; lean_object* v_binderType_1631_; lean_object* v_body_1632_; uint8_t v_binderInfo_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_binderName_1630_ = lean_ctor_get(v_e_1623_, 0);
lean_inc(v_binderName_1630_);
v_binderType_1631_ = lean_ctor_get(v_e_1623_, 1);
lean_inc_ref(v_binderType_1631_);
v_body_1632_ = lean_ctor_get(v_e_1623_, 2);
lean_inc_ref(v_body_1632_);
v_binderInfo_1633_ = lean_ctor_get_uint8(v_e_1623_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1623_, 3);
v___x_1634_ = lean_expr_instantiate_rev(v_binderType_1631_, v_fvars_1622_);
lean_dec_ref(v_binderType_1631_);
lean_inc_ref(v_post_1618_);
lean_inc_ref(v_pre_1617_);
v___x_1635_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_skipInstances_1621_, v___x_1634_, v_a_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___f_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = lean_box(v_usedLetOnly_1619_);
v___x_1638_ = lean_box(v_skipConstInApp_1620_);
v___x_1639_ = lean_box(v_skipInstances_1621_);
v___f_1640_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1640_, 0, v_fvars_1622_);
lean_closure_set(v___f_1640_, 1, v_pre_1617_);
lean_closure_set(v___f_1640_, 2, v_post_1618_);
lean_closure_set(v___f_1640_, 3, v___x_1637_);
lean_closure_set(v___f_1640_, 4, v___x_1638_);
lean_closure_set(v___f_1640_, 5, v___x_1639_);
lean_closure_set(v___f_1640_, 6, v_body_1632_);
v___x_1641_ = 0;
v___x_1642_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1630_, v_binderInfo_1633_, v_a_1636_, v___f_1640_, v___x_1641_, v_a_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1642_;
}
else
{
lean_dec_ref(v_body_1632_);
lean_dec(v_binderName_1630_);
lean_dec_ref(v_fvars_1622_);
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
return v___x_1635_;
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_expr_instantiate_rev(v_e_1623_, v_fvars_1622_);
lean_dec_ref(v_e_1623_);
lean_inc_ref(v_post_1618_);
lean_inc_ref(v_pre_1617_);
v___x_1644_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_skipInstances_1621_, v___x_1643_, v_a_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; uint8_t v___x_1646_; uint8_t v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = 0;
v___x_1647_ = 1;
v___x_1648_ = 1;
v___x_1649_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1622_, v_a_1645_, v___x_1646_, v_usedLetOnly_1619_, v___x_1646_, v___x_1647_, v___x_1648_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec_ref(v_fvars_1622_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1617_, v_post_1618_, v_usedLetOnly_1619_, v_skipConstInApp_1620_, v_skipInstances_1621_, v_a_1650_, v_a_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
return v___x_1651_;
}
else
{
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
return v___x_1649_;
}
}
else
{
lean_dec_ref(v_fvars_1622_);
lean_dec_ref(v_post_1618_);
lean_dec_ref(v_pre_1617_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1652_, lean_object* v_pre_1653_, lean_object* v_post_1654_, uint8_t v_usedLetOnly_1655_, uint8_t v_skipConstInApp_1656_, uint8_t v_skipInstances_1657_, lean_object* v_body_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_array_push(v_fvars_1652_, v_x_1659_);
v___x_1667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1653_, v_post_1654_, v_usedLetOnly_1655_, v_skipConstInApp_1656_, v_skipInstances_1657_, v___x_1666_, v_body_1658_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1668_, lean_object* v_pre_1669_, lean_object* v_post_1670_, lean_object* v_usedLetOnly_1671_, lean_object* v_skipConstInApp_1672_, lean_object* v_skipInstances_1673_, lean_object* v_body_1674_, lean_object* v_x_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_usedLetOnly_boxed_1682_; uint8_t v_skipConstInApp_boxed_1683_; uint8_t v_skipInstances_boxed_1684_; lean_object* v_res_1685_; 
v_usedLetOnly_boxed_1682_ = lean_unbox(v_usedLetOnly_1671_);
v_skipConstInApp_boxed_1683_ = lean_unbox(v_skipConstInApp_1672_);
v_skipInstances_boxed_1684_ = lean_unbox(v_skipInstances_1673_);
v_res_1685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1668_, v_pre_1669_, v_post_1670_, v_usedLetOnly_boxed_1682_, v_skipConstInApp_boxed_1683_, v_skipInstances_boxed_1684_, v_body_1674_, v_x_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1686_, lean_object* v_post_1687_, uint8_t v_usedLetOnly_1688_, uint8_t v_skipConstInApp_1689_, uint8_t v_skipInstances_1690_, lean_object* v_fvars_1691_, lean_object* v_e_1692_, lean_object* v_a_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
if (lean_obj_tag(v_e_1692_) == 8)
{
lean_object* v_declName_1699_; lean_object* v_type_1700_; lean_object* v_value_1701_; lean_object* v_body_1702_; uint8_t v_nondep_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_declName_1699_ = lean_ctor_get(v_e_1692_, 0);
lean_inc(v_declName_1699_);
v_type_1700_ = lean_ctor_get(v_e_1692_, 1);
lean_inc_ref(v_type_1700_);
v_value_1701_ = lean_ctor_get(v_e_1692_, 2);
lean_inc_ref(v_value_1701_);
v_body_1702_ = lean_ctor_get(v_e_1692_, 3);
lean_inc_ref(v_body_1702_);
v_nondep_1703_ = lean_ctor_get_uint8(v_e_1692_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1692_, 4);
v___x_1704_ = lean_expr_instantiate_rev(v_type_1700_, v_fvars_1691_);
lean_dec_ref(v_type_1700_);
lean_inc_ref(v_post_1687_);
lean_inc_ref(v_pre_1686_);
v___x_1705_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1686_, v_post_1687_, v_usedLetOnly_1688_, v_skipConstInApp_1689_, v_skipInstances_1690_, v___x_1704_, v_a_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1707_ = lean_expr_instantiate_rev(v_value_1701_, v_fvars_1691_);
lean_dec_ref(v_value_1701_);
lean_inc_ref(v_post_1687_);
lean_inc_ref(v_pre_1686_);
v___x_1708_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1686_, v_post_1687_, v_usedLetOnly_1688_, v_skipConstInApp_1689_, v_skipInstances_1690_, v___x_1707_, v_a_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___f_1713_; uint8_t v___x_1714_; lean_object* v___x_1715_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = lean_box(v_usedLetOnly_1688_);
v___x_1711_ = lean_box(v_skipConstInApp_1689_);
v___x_1712_ = lean_box(v_skipInstances_1690_);
v___f_1713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1713_, 0, v_fvars_1691_);
lean_closure_set(v___f_1713_, 1, v_pre_1686_);
lean_closure_set(v___f_1713_, 2, v_post_1687_);
lean_closure_set(v___f_1713_, 3, v___x_1710_);
lean_closure_set(v___f_1713_, 4, v___x_1711_);
lean_closure_set(v___f_1713_, 5, v___x_1712_);
lean_closure_set(v___f_1713_, 6, v_body_1702_);
v___x_1714_ = 0;
v___x_1715_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1699_, v_a_1706_, v_a_1709_, v___f_1713_, v_nondep_1703_, v___x_1714_, v_a_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1715_;
}
else
{
lean_dec(v_a_1706_);
lean_dec_ref(v_body_1702_);
lean_dec(v_declName_1699_);
lean_dec_ref(v_fvars_1691_);
lean_dec_ref(v_post_1687_);
lean_dec_ref(v_pre_1686_);
return v___x_1708_;
}
}
else
{
lean_dec_ref(v_body_1702_);
lean_dec_ref(v_value_1701_);
lean_dec(v_declName_1699_);
lean_dec_ref(v_fvars_1691_);
lean_dec_ref(v_post_1687_);
lean_dec_ref(v_pre_1686_);
return v___x_1705_;
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_expr_instantiate_rev(v_e_1692_, v_fvars_1691_);
lean_dec_ref(v_e_1692_);
lean_inc_ref(v_post_1687_);
lean_inc_ref(v_pre_1686_);
v___x_1717_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1686_, v_post_1687_, v_usedLetOnly_1688_, v_skipConstInApp_1689_, v_skipInstances_1690_, v___x_1716_, v_a_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; uint8_t v___x_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = 0;
v___x_1720_ = 1;
v___x_1721_ = l_Lean_Meta_mkLetFVars(v_fvars_1691_, v_a_1718_, v_usedLetOnly_1688_, v___x_1719_, v___x_1720_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec_ref(v_fvars_1691_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1686_, v_post_1687_, v_usedLetOnly_1688_, v_skipConstInApp_1689_, v_skipInstances_1690_, v_a_1722_, v_a_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1723_;
}
else
{
lean_dec_ref(v_post_1687_);
lean_dec_ref(v_pre_1686_);
return v___x_1721_;
}
}
else
{
lean_dec_ref(v_fvars_1691_);
lean_dec_ref(v_post_1687_);
lean_dec_ref(v_pre_1686_);
return v___x_1717_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1724_; lean_object* v_dummy_1725_; 
v___x_1724_ = lean_box(0);
v_dummy_1725_ = l_Lean_Expr_sort___override(v___x_1724_);
return v_dummy_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1726_, lean_object* v_post_1727_, uint8_t v_usedLetOnly_1728_, uint8_t v_skipConstInApp_1729_, uint8_t v_skipInstances_1730_, size_t v_sz_1731_, size_t v_i_1732_, lean_object* v_bs_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_lt(v_i_1732_, v_sz_1731_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref(v_post_1727_);
lean_dec_ref(v_pre_1726_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_bs_1733_);
return v___x_1741_;
}
else
{
lean_object* v_v_1742_; lean_object* v___x_1743_; 
v_v_1742_ = lean_array_uget_borrowed(v_bs_1733_, v_i_1732_);
lean_inc(v_v_1742_);
lean_inc_ref(v_post_1727_);
lean_inc_ref(v_pre_1726_);
v___x_1743_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1726_, v_post_1727_, v_usedLetOnly_1728_, v_skipConstInApp_1729_, v_skipInstances_1730_, v_v_1742_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1745_; lean_object* v_bs_x27_1746_; size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1745_ = lean_unsigned_to_nat(0u);
v_bs_x27_1746_ = lean_array_uset(v_bs_1733_, v_i_1732_, v___x_1745_);
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1732_, v___x_1747_);
v___x_1749_ = lean_array_uset(v_bs_x27_1746_, v_i_1732_, v_a_1744_);
v_i_1732_ = v___x_1748_;
v_bs_1733_ = v___x_1749_;
goto _start;
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec_ref(v_bs_1733_);
lean_dec_ref(v_post_1727_);
lean_dec_ref(v_pre_1726_);
v_a_1751_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1743_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1743_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1759_, lean_object* v_post_1760_, uint8_t v_usedLetOnly_1761_, uint8_t v_skipConstInApp_1762_, uint8_t v_skipInstances_1763_, lean_object* v___x_1764_, lean_object* v___y_1765_, lean_object* v_b_1766_, lean_object* v_a_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1759_, v_post_1760_, v_usedLetOnly_1761_, v_skipConstInApp_1762_, v_skipInstances_1763_, v___x_1764_, v___y_1765_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1783_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1783_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_array_fset(v_b_1766_, v_a_1767_, v_a_1774_);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1779_);
v___x_1781_ = v___x_1776_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v_b_1766_);
v_a_1784_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1773_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1773_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1792_, lean_object* v_post_1793_, lean_object* v_usedLetOnly_1794_, lean_object* v_skipConstInApp_1795_, lean_object* v_skipInstances_1796_, lean_object* v___x_1797_, lean_object* v___y_1798_, lean_object* v_b_1799_, lean_object* v_a_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
uint8_t v_usedLetOnly_boxed_1806_; uint8_t v_skipConstInApp_boxed_1807_; uint8_t v_skipInstances_boxed_1808_; lean_object* v_res_1809_; 
v_usedLetOnly_boxed_1806_ = lean_unbox(v_usedLetOnly_1794_);
v_skipConstInApp_boxed_1807_ = lean_unbox(v_skipConstInApp_1795_);
v_skipInstances_boxed_1808_ = lean_unbox(v_skipInstances_1796_);
v_res_1809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1792_, v_post_1793_, v_usedLetOnly_boxed_1806_, v_skipConstInApp_boxed_1807_, v_skipInstances_boxed_1808_, v___x_1797_, v___y_1798_, v_b_1799_, v_a_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v_a_1800_);
lean_dec(v___y_1798_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1810_, lean_object* v___x_1811_, lean_object* v_pre_1812_, lean_object* v_post_1813_, uint8_t v_usedLetOnly_1814_, uint8_t v_skipConstInApp_1815_, uint8_t v_skipInstances_1816_, lean_object* v_a_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___y_1826_; uint8_t v___x_1849_; 
v___x_1849_ = lean_nat_dec_lt(v_a_1817_, v_upperBound_1810_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_dec(v_a_1817_);
lean_dec_ref(v_post_1813_);
lean_dec_ref(v_pre_1812_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_b_1818_);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1851_ = lean_array_fget_borrowed(v_b_1818_, v_a_1817_);
v___x_1852_ = lean_array_get_size(v___x_1811_);
v___x_1853_ = lean_nat_dec_lt(v_a_1817_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___f_1857_; 
lean_inc(v___x_1851_);
v___x_1854_ = lean_box(v_usedLetOnly_1814_);
v___x_1855_ = lean_box(v_skipConstInApp_1815_);
v___x_1856_ = lean_box(v_skipInstances_1816_);
lean_inc(v_a_1817_);
lean_inc(v___y_1819_);
lean_inc_ref(v_post_1813_);
lean_inc_ref(v_pre_1812_);
v___f_1857_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1857_, 0, v_pre_1812_);
lean_closure_set(v___f_1857_, 1, v_post_1813_);
lean_closure_set(v___f_1857_, 2, v___x_1854_);
lean_closure_set(v___f_1857_, 3, v___x_1855_);
lean_closure_set(v___f_1857_, 4, v___x_1856_);
lean_closure_set(v___f_1857_, 5, v___x_1851_);
lean_closure_set(v___f_1857_, 6, v___y_1819_);
lean_closure_set(v___f_1857_, 7, v_b_1818_);
lean_closure_set(v___f_1857_, 8, v_a_1817_);
v___y_1826_ = v___f_1857_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1858_; uint8_t v_isInstance_1859_; 
v___x_1858_ = lean_array_fget_borrowed(v___x_1811_, v_a_1817_);
v_isInstance_1859_ = lean_ctor_get_uint8(v___x_1858_, sizeof(void*)*1 + 4);
if (v_isInstance_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___f_1863_; 
lean_inc(v___x_1851_);
v___x_1860_ = lean_box(v_usedLetOnly_1814_);
v___x_1861_ = lean_box(v_skipConstInApp_1815_);
v___x_1862_ = lean_box(v_skipInstances_1816_);
lean_inc(v_a_1817_);
lean_inc(v___y_1819_);
lean_inc_ref(v_post_1813_);
lean_inc_ref(v_pre_1812_);
v___f_1863_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1863_, 0, v_pre_1812_);
lean_closure_set(v___f_1863_, 1, v_post_1813_);
lean_closure_set(v___f_1863_, 2, v___x_1860_);
lean_closure_set(v___f_1863_, 3, v___x_1861_);
lean_closure_set(v___f_1863_, 4, v___x_1862_);
lean_closure_set(v___f_1863_, 5, v___x_1851_);
lean_closure_set(v___f_1863_, 6, v___y_1819_);
lean_closure_set(v___f_1863_, 7, v_b_1818_);
lean_closure_set(v___f_1863_, 8, v_a_1817_);
v___y_1826_ = v___f_1863_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1864_; lean_object* v___f_1865_; 
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_b_1818_);
v___f_1865_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1865_, 0, v___x_1864_);
v___y_1826_ = v___f_1865_;
goto v___jp_1825_;
}
}
}
v___jp_1825_:
{
lean_object* v___x_1827_; 
lean_inc(v___y_1823_);
lean_inc_ref(v___y_1822_);
lean_inc(v___y_1821_);
lean_inc_ref(v___y_1820_);
v___x_1827_ = lean_apply_5(v___y_1826_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, lean_box(0));
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1840_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1840_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
if (lean_obj_tag(v_a_1828_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; 
lean_dec(v_a_1817_);
lean_dec_ref(v_post_1813_);
lean_dec_ref(v_pre_1812_);
v_a_1832_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v_a_1828_, 1);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v_a_1832_);
v___x_1834_ = v___x_1830_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_del_object(v___x_1830_);
v_a_1836_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v_a_1828_, 1);
v___x_1837_ = lean_unsigned_to_nat(1u);
v___x_1838_ = lean_nat_add(v_a_1817_, v___x_1837_);
lean_dec(v_a_1817_);
v_a_1817_ = v___x_1838_;
v_b_1818_ = v_a_1836_;
goto _start;
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1817_);
lean_dec_ref(v_post_1813_);
lean_dec_ref(v_pre_1812_);
v_a_1841_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1827_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1827_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1866_, lean_object* v_pre_1867_, lean_object* v_post_1868_, uint8_t v_usedLetOnly_1869_, uint8_t v_skipConstInApp_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_f_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; 
if (lean_obj_tag(v_x_1871_) == 5)
{
lean_object* v_fn_1929_; lean_object* v_arg_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_fn_1929_ = lean_ctor_get(v_x_1871_, 0);
lean_inc_ref(v_fn_1929_);
v_arg_1930_ = lean_ctor_get(v_x_1871_, 1);
lean_inc_ref(v_arg_1930_);
lean_dec_ref_known(v_x_1871_, 2);
v___x_1931_ = lean_array_set(v_x_1872_, v_x_1873_, v_arg_1930_);
v___x_1932_ = lean_unsigned_to_nat(1u);
v___x_1933_ = lean_nat_sub(v_x_1873_, v___x_1932_);
lean_dec(v_x_1873_);
v_x_1871_ = v_fn_1929_;
v_x_1872_ = v___x_1931_;
v_x_1873_ = v___x_1933_;
goto _start;
}
else
{
lean_dec(v_x_1873_);
if (v_skipConstInApp_1870_ == 0)
{
goto v___jp_1926_;
}
else
{
uint8_t v___x_1935_; 
v___x_1935_ = l_Lean_Expr_isConst(v_x_1871_);
if (v___x_1935_ == 0)
{
goto v___jp_1926_;
}
else
{
v_f_1881_ = v_x_1871_;
v___y_1882_ = v___y_1874_;
v___y_1883_ = v___y_1875_;
v___y_1884_ = v___y_1876_;
v___y_1885_ = v___y_1877_;
v___y_1886_ = v___y_1878_;
goto v___jp_1880_;
}
}
}
v___jp_1880_:
{
if (v_skipInstances_1866_ == 0)
{
size_t v_sz_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v_sz_1887_ = lean_array_size(v_x_1872_);
v___x_1888_ = ((size_t)0ULL);
lean_inc_ref(v_post_1868_);
lean_inc_ref(v_pre_1867_);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1867_, v_post_1868_, v_usedLetOnly_1869_, v_skipConstInApp_1870_, v_skipInstances_1866_, v_sz_1887_, v___x_1888_, v_x_1872_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
v___x_1891_ = l_Lean_mkAppN(v_f_1881_, v_a_1890_);
lean_dec(v_a_1890_);
v___x_1892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1867_, v_post_1868_, v_usedLetOnly_1869_, v_skipConstInApp_1870_, v_skipInstances_1866_, v___x_1891_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
return v___x_1892_;
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_post_1868_);
lean_dec_ref(v_pre_1867_);
v_a_1893_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1889_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1889_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_array_get_size(v_x_1872_);
lean_inc_ref(v_f_1881_);
v___x_1902_ = l_Lean_Meta_getFunInfoNArgs(v_f_1881_, v___x_1901_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v_paramInfo_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v_paramInfo_1904_ = lean_ctor_get(v_a_1903_, 0);
lean_inc_ref(v_paramInfo_1904_);
lean_dec(v_a_1903_);
v___x_1905_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1868_);
lean_inc_ref(v_pre_1867_);
v___x_1906_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1901_, v_paramInfo_1904_, v_pre_1867_, v_post_1868_, v_usedLetOnly_1869_, v_skipConstInApp_1870_, v_skipInstances_1866_, v___x_1905_, v_x_1872_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec_ref(v_paramInfo_1904_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = l_Lean_mkAppN(v_f_1881_, v_a_1907_);
lean_dec(v_a_1907_);
v___x_1909_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1867_, v_post_1868_, v_usedLetOnly_1869_, v_skipConstInApp_1870_, v_skipInstances_1866_, v___x_1908_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
return v___x_1909_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_post_1868_);
lean_dec_ref(v_pre_1867_);
v_a_1910_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1906_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1906_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref(v_f_1881_);
lean_dec_ref(v_x_1872_);
lean_dec_ref(v_post_1868_);
lean_dec_ref(v_pre_1867_);
v_a_1918_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1902_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1902_);
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
}
v___jp_1926_:
{
lean_object* v___x_1927_; 
lean_inc_ref(v_post_1868_);
lean_inc_ref(v_pre_1867_);
v___x_1927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1867_, v_post_1868_, v_usedLetOnly_1869_, v_skipConstInApp_1870_, v_skipInstances_1866_, v_x_1871_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v_f_1881_ = v_a_1928_;
v___y_1882_ = v___y_1874_;
v___y_1883_ = v___y_1875_;
v___y_1884_ = v___y_1876_;
v___y_1885_ = v___y_1877_;
v___y_1886_ = v___y_1878_;
goto v___jp_1880_;
}
else
{
lean_dec_ref(v_x_1872_);
lean_dec_ref(v_post_1868_);
lean_dec_ref(v_pre_1867_);
return v___x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1936_, lean_object* v_pre_1937_, lean_object* v_e_1938_, lean_object* v_post_1939_, uint8_t v_usedLetOnly_1940_, uint8_t v_skipConstInApp_1941_, uint8_t v_skipInstances_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_Core_checkSystem(v___x_1936_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1950_; 
lean_dec_ref_known(v___x_1949_, 1);
lean_inc_ref(v_pre_1937_);
lean_inc(v___y_1947_);
lean_inc_ref(v___y_1946_);
lean_inc(v___y_1945_);
lean_inc_ref(v___y_1944_);
lean_inc_ref(v_e_1938_);
v___x_1950_ = lean_apply_6(v_pre_1937_, v_e_1938_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, lean_box(0));
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1999_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1999_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1999_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___y_1956_; 
switch(lean_obj_tag(v_a_1951_))
{
case 0:
{
lean_object* v_e_1991_; lean_object* v___x_1993_; 
lean_dec_ref(v_post_1939_);
lean_dec_ref(v_e_1938_);
lean_dec_ref(v_pre_1937_);
v_e_1991_ = lean_ctor_get(v_a_1951_, 0);
lean_inc_ref(v_e_1991_);
lean_dec_ref_known(v_a_1951_, 1);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v_e_1991_);
v___x_1993_ = v___x_1953_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_e_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
case 1:
{
lean_object* v_e_1995_; lean_object* v___x_1996_; 
lean_del_object(v___x_1953_);
lean_dec_ref(v_e_1938_);
v_e_1995_ = lean_ctor_get(v_a_1951_, 0);
lean_inc_ref(v_e_1995_);
lean_dec_ref_known(v_a_1951_, 1);
v___x_1996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v_e_1995_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1996_;
}
default: 
{
lean_object* v_e_x3f_1997_; 
lean_del_object(v___x_1953_);
v_e_x3f_1997_ = lean_ctor_get(v_a_1951_, 0);
lean_inc(v_e_x3f_1997_);
lean_dec_ref_known(v_a_1951_, 1);
if (lean_obj_tag(v_e_x3f_1997_) == 0)
{
v___y_1956_ = v_e_1938_;
goto v___jp_1955_;
}
else
{
lean_object* v_val_1998_; 
lean_dec_ref(v_e_1938_);
v_val_1998_ = lean_ctor_get(v_e_x3f_1997_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_e_x3f_1997_, 1);
v___y_1956_ = v_val_1998_;
goto v___jp_1955_;
}
}
}
v___jp_1955_:
{
switch(lean_obj_tag(v___y_1956_))
{
case 7:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v___x_1957_, v___y_1956_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1958_;
}
case 6:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v___x_1959_, v___y_1956_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1960_;
}
case 8:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v___x_1961_, v___y_1956_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1962_;
}
case 5:
{
lean_object* v_dummy_1963_; lean_object* v_nargs_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_dummy_1963_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1964_ = l_Lean_Expr_getAppNumArgs(v___y_1956_);
lean_inc(v_nargs_1964_);
v___x_1965_ = lean_mk_array(v_nargs_1964_, v_dummy_1963_);
v___x_1966_ = lean_unsigned_to_nat(1u);
v___x_1967_ = lean_nat_sub(v_nargs_1964_, v___x_1966_);
lean_dec(v_nargs_1964_);
v___x_1968_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1942_, v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v___y_1956_, v___x_1965_, v___x_1967_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1968_;
}
case 10:
{
lean_object* v_data_1969_; lean_object* v_expr_1970_; lean_object* v___x_1971_; 
v_data_1969_ = lean_ctor_get(v___y_1956_, 0);
v_expr_1970_ = lean_ctor_get(v___y_1956_, 1);
lean_inc_ref(v_expr_1970_);
lean_inc_ref(v_post_1939_);
lean_inc_ref(v_pre_1937_);
v___x_1971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v_expr_1970_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; size_t v___x_1973_; size_t v___x_1974_; uint8_t v___x_1975_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = lean_ptr_addr(v_expr_1970_);
v___x_1974_ = lean_ptr_addr(v_a_1972_);
v___x_1975_ = lean_usize_dec_eq(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_inc(v_data_1969_);
lean_dec_ref_known(v___y_1956_, 2);
v___x_1976_ = l_Lean_Expr_mdata___override(v_data_1969_, v_a_1972_);
v___x_1977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v___x_1976_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; 
lean_dec(v_a_1972_);
v___x_1978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v___y_1956_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1978_;
}
}
else
{
lean_dec_ref_known(v___y_1956_, 2);
lean_dec_ref(v_post_1939_);
lean_dec_ref(v_pre_1937_);
return v___x_1971_;
}
}
case 11:
{
lean_object* v_typeName_1979_; lean_object* v_idx_1980_; lean_object* v_struct_1981_; lean_object* v___x_1982_; 
v_typeName_1979_ = lean_ctor_get(v___y_1956_, 0);
v_idx_1980_ = lean_ctor_get(v___y_1956_, 1);
v_struct_1981_ = lean_ctor_get(v___y_1956_, 2);
lean_inc_ref(v_struct_1981_);
lean_inc_ref(v_post_1939_);
lean_inc_ref(v_pre_1937_);
v___x_1982_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v_struct_1981_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; size_t v___x_1984_; size_t v___x_1985_; uint8_t v___x_1986_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v___x_1984_ = lean_ptr_addr(v_struct_1981_);
v___x_1985_ = lean_ptr_addr(v_a_1983_);
v___x_1986_ = lean_usize_dec_eq(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_inc(v_idx_1980_);
lean_inc(v_typeName_1979_);
lean_dec_ref_known(v___y_1956_, 3);
v___x_1987_ = l_Lean_Expr_proj___override(v_typeName_1979_, v_idx_1980_, v_a_1983_);
v___x_1988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v___x_1987_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; 
lean_dec(v_a_1983_);
v___x_1989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v___y_1956_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1989_;
}
}
else
{
lean_dec_ref_known(v___y_1956_, 3);
lean_dec_ref(v_post_1939_);
lean_dec_ref(v_pre_1937_);
return v___x_1982_;
}
}
default: 
{
lean_object* v___x_1990_; 
v___x_1990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1937_, v_post_1939_, v_usedLetOnly_1940_, v_skipConstInApp_1941_, v_skipInstances_1942_, v___y_1956_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
return v___x_1990_;
}
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v_post_1939_);
lean_dec_ref(v_e_1938_);
lean_dec_ref(v_pre_1937_);
v_a_2000_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1950_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1950_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_post_1939_);
lean_dec_ref(v_e_1938_);
lean_dec_ref(v_pre_1937_);
v_a_2008_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1949_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1949_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2016_, lean_object* v_pre_2017_, lean_object* v_e_2018_, lean_object* v_post_2019_, lean_object* v_usedLetOnly_2020_, lean_object* v_skipConstInApp_2021_, lean_object* v_skipInstances_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v_usedLetOnly_boxed_2029_; uint8_t v_skipConstInApp_boxed_2030_; uint8_t v_skipInstances_boxed_2031_; lean_object* v_res_2032_; 
v_usedLetOnly_boxed_2029_ = lean_unbox(v_usedLetOnly_2020_);
v_skipConstInApp_boxed_2030_ = lean_unbox(v_skipConstInApp_2021_);
v_skipInstances_boxed_2031_ = lean_unbox(v_skipInstances_2022_);
v_res_2032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2016_, v_pre_2017_, v_e_2018_, v_post_2019_, v_usedLetOnly_boxed_2029_, v_skipConstInApp_boxed_2030_, v_skipInstances_boxed_2031_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2033_, lean_object* v_post_2034_, uint8_t v_usedLetOnly_2035_, uint8_t v_skipConstInApp_2036_, uint8_t v_skipInstances_2037_, lean_object* v_e_2038_, lean_object* v_a_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_inc(v_a_2039_);
v___x_2045_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2045_, 0, lean_box(0));
lean_closure_set(v___x_2045_, 1, lean_box(0));
lean_closure_set(v___x_2045_, 2, v_a_2039_);
v___x_2046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2045_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2081_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2081_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2081_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2047_, v_e_2038_);
lean_dec(v_a_2047_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___f_2056_; lean_object* v___x_2057_; 
lean_del_object(v___x_2049_);
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2053_ = lean_box(v_usedLetOnly_2035_);
v___x_2054_ = lean_box(v_skipConstInApp_2036_);
v___x_2055_ = lean_box(v_skipInstances_2037_);
lean_inc_ref(v_e_2038_);
v___f_2056_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2056_, 0, v___x_2052_);
lean_closure_set(v___f_2056_, 1, v_pre_2033_);
lean_closure_set(v___f_2056_, 2, v_e_2038_);
lean_closure_set(v___f_2056_, 3, v_post_2034_);
lean_closure_set(v___f_2056_, 4, v___x_2053_);
lean_closure_set(v___f_2056_, 5, v___x_2054_);
lean_closure_set(v___f_2056_, 6, v___x_2055_);
v___x_2057_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2056_, v_a_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc_n(v_a_2058_, 2);
lean_dec_ref_known(v___x_2057_, 1);
lean_inc(v_a_2039_);
v___f_2059_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2059_, 0, v_a_2039_);
lean_closure_set(v___f_2059_, 1, v_e_2038_);
lean_closure_set(v___f_2059_, 2, v_a_2058_);
v___x_2060_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2059_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; 
v_unused_2068_ = lean_ctor_get(v___x_2060_, 0);
lean_dec(v_unused_2068_);
v___x_2062_ = v___x_2060_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_dec(v___x_2060_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v_a_2058_);
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2058_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec(v_a_2058_);
v_a_2069_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2060_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2060_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
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
lean_dec_ref(v_e_2038_);
return v___x_2057_;
}
}
else
{
lean_object* v_val_2077_; lean_object* v___x_2079_; 
lean_dec_ref(v_e_2038_);
lean_dec_ref(v_post_2034_);
lean_dec_ref(v_pre_2033_);
v_val_2077_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_val_2077_);
lean_dec_ref_known(v___x_2051_, 1);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v_val_2077_);
v___x_2079_ = v___x_2049_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_val_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v_e_2038_);
lean_dec_ref(v_post_2034_);
lean_dec_ref(v_pre_2033_);
v_a_2082_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2046_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2046_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2090_, lean_object* v_pre_2091_, lean_object* v_post_2092_, lean_object* v_usedLetOnly_2093_, lean_object* v_skipConstInApp_2094_, lean_object* v_skipInstances_2095_, lean_object* v_body_2096_, lean_object* v_x_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v_usedLetOnly_boxed_2104_; uint8_t v_skipConstInApp_boxed_2105_; uint8_t v_skipInstances_boxed_2106_; lean_object* v_res_2107_; 
v_usedLetOnly_boxed_2104_ = lean_unbox(v_usedLetOnly_2093_);
v_skipConstInApp_boxed_2105_ = lean_unbox(v_skipConstInApp_2094_);
v_skipInstances_boxed_2106_ = lean_unbox(v_skipInstances_2095_);
v_res_2107_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2090_, v_pre_2091_, v_post_2092_, v_usedLetOnly_boxed_2104_, v_skipConstInApp_boxed_2105_, v_skipInstances_boxed_2106_, v_body_2096_, v_x_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2108_, lean_object* v_post_2109_, uint8_t v_usedLetOnly_2110_, uint8_t v_skipConstInApp_2111_, uint8_t v_skipInstances_2112_, lean_object* v_fvars_2113_, lean_object* v_e_2114_, lean_object* v_a_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
if (lean_obj_tag(v_e_2114_) == 7)
{
lean_object* v_binderName_2121_; lean_object* v_binderType_2122_; lean_object* v_body_2123_; uint8_t v_binderInfo_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_binderName_2121_ = lean_ctor_get(v_e_2114_, 0);
lean_inc(v_binderName_2121_);
v_binderType_2122_ = lean_ctor_get(v_e_2114_, 1);
lean_inc_ref(v_binderType_2122_);
v_body_2123_ = lean_ctor_get(v_e_2114_, 2);
lean_inc_ref(v_body_2123_);
v_binderInfo_2124_ = lean_ctor_get_uint8(v_e_2114_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2114_, 3);
v___x_2125_ = lean_expr_instantiate_rev(v_binderType_2122_, v_fvars_2113_);
lean_dec_ref(v_binderType_2122_);
lean_inc_ref(v_post_2109_);
lean_inc_ref(v_pre_2108_);
v___x_2126_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2108_, v_post_2109_, v_usedLetOnly_2110_, v_skipConstInApp_2111_, v_skipInstances_2112_, v___x_2125_, v_a_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___f_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = lean_box(v_usedLetOnly_2110_);
v___x_2129_ = lean_box(v_skipConstInApp_2111_);
v___x_2130_ = lean_box(v_skipInstances_2112_);
v___f_2131_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2131_, 0, v_fvars_2113_);
lean_closure_set(v___f_2131_, 1, v_pre_2108_);
lean_closure_set(v___f_2131_, 2, v_post_2109_);
lean_closure_set(v___f_2131_, 3, v___x_2128_);
lean_closure_set(v___f_2131_, 4, v___x_2129_);
lean_closure_set(v___f_2131_, 5, v___x_2130_);
lean_closure_set(v___f_2131_, 6, v_body_2123_);
v___x_2132_ = 0;
v___x_2133_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2121_, v_binderInfo_2124_, v_a_2127_, v___f_2131_, v___x_2132_, v_a_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2133_;
}
else
{
lean_dec_ref(v_body_2123_);
lean_dec(v_binderName_2121_);
lean_dec_ref(v_fvars_2113_);
lean_dec_ref(v_post_2109_);
lean_dec_ref(v_pre_2108_);
return v___x_2126_;
}
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_expr_instantiate_rev(v_e_2114_, v_fvars_2113_);
lean_dec_ref(v_e_2114_);
lean_inc_ref(v_post_2109_);
lean_inc_ref(v_pre_2108_);
v___x_2135_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2108_, v_post_2109_, v_usedLetOnly_2110_, v_skipConstInApp_2111_, v_skipInstances_2112_, v___x_2134_, v_a_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; uint8_t v___x_2137_; uint8_t v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = 0;
v___x_2138_ = 1;
v___x_2139_ = 1;
v___x_2140_ = l_Lean_Meta_mkForallFVars(v_fvars_2113_, v_a_2136_, v___x_2137_, v_usedLetOnly_2110_, v___x_2138_, v___x_2139_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec_ref(v_fvars_2113_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2108_, v_post_2109_, v_usedLetOnly_2110_, v_skipConstInApp_2111_, v_skipInstances_2112_, v_a_2141_, v_a_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2142_;
}
else
{
lean_dec_ref(v_post_2109_);
lean_dec_ref(v_pre_2108_);
return v___x_2140_;
}
}
else
{
lean_dec_ref(v_fvars_2113_);
lean_dec_ref(v_post_2109_);
lean_dec_ref(v_pre_2108_);
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2143_, lean_object* v_pre_2144_, lean_object* v_post_2145_, uint8_t v_usedLetOnly_2146_, uint8_t v_skipConstInApp_2147_, uint8_t v_skipInstances_2148_, lean_object* v_body_2149_, lean_object* v_x_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_array_push(v_fvars_2143_, v_x_2150_);
v___x_2158_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2144_, v_post_2145_, v_usedLetOnly_2146_, v_skipConstInApp_2147_, v_skipInstances_2148_, v___x_2157_, v_body_2149_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2159_, lean_object* v_post_2160_, lean_object* v_usedLetOnly_2161_, lean_object* v_skipConstInApp_2162_, lean_object* v_skipInstances_2163_, lean_object* v_e_2164_, lean_object* v_a_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v_usedLetOnly_boxed_2171_; uint8_t v_skipConstInApp_boxed_2172_; uint8_t v_skipInstances_boxed_2173_; lean_object* v_res_2174_; 
v_usedLetOnly_boxed_2171_ = lean_unbox(v_usedLetOnly_2161_);
v_skipConstInApp_boxed_2172_ = lean_unbox(v_skipConstInApp_2162_);
v_skipInstances_boxed_2173_ = lean_unbox(v_skipInstances_2163_);
v_res_2174_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2159_, v_post_2160_, v_usedLetOnly_boxed_2171_, v_skipConstInApp_boxed_2172_, v_skipInstances_boxed_2173_, v_e_2164_, v_a_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v_a_2165_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2175_, lean_object* v_post_2176_, lean_object* v_usedLetOnly_2177_, lean_object* v_skipConstInApp_2178_, lean_object* v_skipInstances_2179_, lean_object* v_sz_2180_, lean_object* v_i_2181_, lean_object* v_bs_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
uint8_t v_usedLetOnly_boxed_2189_; uint8_t v_skipConstInApp_boxed_2190_; uint8_t v_skipInstances_boxed_2191_; size_t v_sz_boxed_2192_; size_t v_i_boxed_2193_; lean_object* v_res_2194_; 
v_usedLetOnly_boxed_2189_ = lean_unbox(v_usedLetOnly_2177_);
v_skipConstInApp_boxed_2190_ = lean_unbox(v_skipConstInApp_2178_);
v_skipInstances_boxed_2191_ = lean_unbox(v_skipInstances_2179_);
v_sz_boxed_2192_ = lean_unbox_usize(v_sz_2180_);
lean_dec(v_sz_2180_);
v_i_boxed_2193_ = lean_unbox_usize(v_i_2181_);
lean_dec(v_i_2181_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2175_, v_post_2176_, v_usedLetOnly_boxed_2189_, v_skipConstInApp_boxed_2190_, v_skipInstances_boxed_2191_, v_sz_boxed_2192_, v_i_boxed_2193_, v_bs_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2195_, lean_object* v_post_2196_, lean_object* v_usedLetOnly_2197_, lean_object* v_skipConstInApp_2198_, lean_object* v_skipInstances_2199_, lean_object* v_e_2200_, lean_object* v_a_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v_usedLetOnly_boxed_2207_; uint8_t v_skipConstInApp_boxed_2208_; uint8_t v_skipInstances_boxed_2209_; lean_object* v_res_2210_; 
v_usedLetOnly_boxed_2207_ = lean_unbox(v_usedLetOnly_2197_);
v_skipConstInApp_boxed_2208_ = lean_unbox(v_skipConstInApp_2198_);
v_skipInstances_boxed_2209_ = lean_unbox(v_skipInstances_2199_);
v_res_2210_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2195_, v_post_2196_, v_usedLetOnly_boxed_2207_, v_skipConstInApp_boxed_2208_, v_skipInstances_boxed_2209_, v_e_2200_, v_a_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v_a_2201_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2211_, lean_object* v_post_2212_, lean_object* v_usedLetOnly_2213_, lean_object* v_skipConstInApp_2214_, lean_object* v_skipInstances_2215_, lean_object* v_fvars_2216_, lean_object* v_e_2217_, lean_object* v_a_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
uint8_t v_usedLetOnly_boxed_2224_; uint8_t v_skipConstInApp_boxed_2225_; uint8_t v_skipInstances_boxed_2226_; lean_object* v_res_2227_; 
v_usedLetOnly_boxed_2224_ = lean_unbox(v_usedLetOnly_2213_);
v_skipConstInApp_boxed_2225_ = lean_unbox(v_skipConstInApp_2214_);
v_skipInstances_boxed_2226_ = lean_unbox(v_skipInstances_2215_);
v_res_2227_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2211_, v_post_2212_, v_usedLetOnly_boxed_2224_, v_skipConstInApp_boxed_2225_, v_skipInstances_boxed_2226_, v_fvars_2216_, v_e_2217_, v_a_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v_a_2218_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2228_, lean_object* v_post_2229_, lean_object* v_usedLetOnly_2230_, lean_object* v_skipConstInApp_2231_, lean_object* v_skipInstances_2232_, lean_object* v_fvars_2233_, lean_object* v_e_2234_, lean_object* v_a_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
uint8_t v_usedLetOnly_boxed_2241_; uint8_t v_skipConstInApp_boxed_2242_; uint8_t v_skipInstances_boxed_2243_; lean_object* v_res_2244_; 
v_usedLetOnly_boxed_2241_ = lean_unbox(v_usedLetOnly_2230_);
v_skipConstInApp_boxed_2242_ = lean_unbox(v_skipConstInApp_2231_);
v_skipInstances_boxed_2243_ = lean_unbox(v_skipInstances_2232_);
v_res_2244_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2228_, v_post_2229_, v_usedLetOnly_boxed_2241_, v_skipConstInApp_boxed_2242_, v_skipInstances_boxed_2243_, v_fvars_2233_, v_e_2234_, v_a_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v_a_2235_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2245_, lean_object* v_post_2246_, lean_object* v_usedLetOnly_2247_, lean_object* v_skipConstInApp_2248_, lean_object* v_skipInstances_2249_, lean_object* v_fvars_2250_, lean_object* v_e_2251_, lean_object* v_a_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v_usedLetOnly_boxed_2258_; uint8_t v_skipConstInApp_boxed_2259_; uint8_t v_skipInstances_boxed_2260_; lean_object* v_res_2261_; 
v_usedLetOnly_boxed_2258_ = lean_unbox(v_usedLetOnly_2247_);
v_skipConstInApp_boxed_2259_ = lean_unbox(v_skipConstInApp_2248_);
v_skipInstances_boxed_2260_ = lean_unbox(v_skipInstances_2249_);
v_res_2261_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2245_, v_post_2246_, v_usedLetOnly_boxed_2258_, v_skipConstInApp_boxed_2259_, v_skipInstances_boxed_2260_, v_fvars_2250_, v_e_2251_, v_a_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v_a_2252_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2262_, lean_object* v___x_2263_, lean_object* v_pre_2264_, lean_object* v_post_2265_, lean_object* v_usedLetOnly_2266_, lean_object* v_skipConstInApp_2267_, lean_object* v_skipInstances_2268_, lean_object* v_a_2269_, lean_object* v_b_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v_usedLetOnly_boxed_2277_; uint8_t v_skipConstInApp_boxed_2278_; uint8_t v_skipInstances_boxed_2279_; lean_object* v_res_2280_; 
v_usedLetOnly_boxed_2277_ = lean_unbox(v_usedLetOnly_2266_);
v_skipConstInApp_boxed_2278_ = lean_unbox(v_skipConstInApp_2267_);
v_skipInstances_boxed_2279_ = lean_unbox(v_skipInstances_2268_);
v_res_2280_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2262_, v___x_2263_, v_pre_2264_, v_post_2265_, v_usedLetOnly_boxed_2277_, v_skipConstInApp_boxed_2278_, v_skipInstances_boxed_2279_, v_a_2269_, v_b_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___x_2263_);
lean_dec(v_upperBound_2262_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2281_, lean_object* v_pre_2282_, lean_object* v_post_2283_, lean_object* v_usedLetOnly_2284_, lean_object* v_skipConstInApp_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
uint8_t v_skipInstances_boxed_2295_; uint8_t v_usedLetOnly_boxed_2296_; uint8_t v_skipConstInApp_boxed_2297_; lean_object* v_res_2298_; 
v_skipInstances_boxed_2295_ = lean_unbox(v_skipInstances_2281_);
v_usedLetOnly_boxed_2296_ = lean_unbox(v_usedLetOnly_2284_);
v_skipConstInApp_boxed_2297_ = lean_unbox(v_skipConstInApp_2285_);
v_res_2298_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2295_, v_pre_2282_, v_post_2283_, v_usedLetOnly_boxed_2296_, v_skipConstInApp_boxed_2297_, v_x_2286_, v_x_2287_, v_x_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2300_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2300_, 0, lean_box(0));
lean_closure_set(v___x_2300_, 1, lean_box(0));
lean_closure_set(v___x_2300_, 2, v___x_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2301_, lean_object* v_pre_2302_, lean_object* v_post_2303_, uint8_t v_usedLetOnly_2304_, uint8_t v_skipConstInApp_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; 
v___x_2311_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2312_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2311_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = 0;
v___x_2315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2302_, v_post_2303_, v_usedLetOnly_2304_, v_skipConstInApp_2305_, v___x_2314_, v_input_2301_, v_a_2313_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2317_, 0, lean_box(0));
lean_closure_set(v___x_2317_, 1, lean_box(0));
lean_closure_set(v___x_2317_, 2, v_a_2313_);
v___x_2318_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2317_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; 
v_unused_2326_ = lean_ctor_get(v___x_2318_, 0);
lean_dec(v_unused_2326_);
v___x_2320_ = v___x_2318_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_dec(v___x_2318_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v_a_2316_);
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2316_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
else
{
lean_dec(v_a_2313_);
return v___x_2315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2327_, lean_object* v_pre_2328_, lean_object* v_post_2329_, lean_object* v_usedLetOnly_2330_, lean_object* v_skipConstInApp_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_usedLetOnly_boxed_2337_; uint8_t v_skipConstInApp_boxed_2338_; lean_object* v_res_2339_; 
v_usedLetOnly_boxed_2337_ = lean_unbox(v_usedLetOnly_2330_);
v_skipConstInApp_boxed_2338_ = lean_unbox(v_skipConstInApp_2331_);
v_res_2339_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2327_, v_pre_2328_, v_post_2329_, v_usedLetOnly_boxed_2337_, v_skipConstInApp_boxed_2338_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2340_, lean_object* v_as_2341_, lean_object* v_j_2342_){
_start:
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = lean_array_get_size(v_as_2341_);
v___x_2344_ = lean_nat_dec_lt(v_j_2342_, v___x_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec(v_j_2342_);
v___x_2345_ = lean_box(0);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; lean_object* v_declName_2347_; uint8_t v___x_2348_; 
v___x_2346_ = lean_array_fget_borrowed(v_as_2341_, v_j_2342_);
v_declName_2347_ = lean_ctor_get(v___x_2346_, 3);
v___x_2348_ = lean_name_eq(v_declName_2347_, v___x_2340_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_add(v_j_2342_, v___x_2349_);
lean_dec(v_j_2342_);
v_j_2342_ = v___x_2350_;
goto _start;
}
else
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_j_2342_);
return v___x_2352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2353_, lean_object* v_as_2354_, lean_object* v_j_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2353_, v_as_2354_, v_j_2355_);
lean_dec_ref(v_as_2354_);
lean_dec(v___x_2353_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_st_ref_get(v_val_2357_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v_val_2365_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2372_, lean_object* v_val_2373_, lean_object* v_a_2374_, lean_object* v___x_2375_, lean_object* v_____r_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2382_ = lean_st_ref_take(v_val_2372_);
v___x_2383_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2373_, v_a_2374_, v___x_2382_);
v___x_2384_ = lean_st_ref_put(v_val_2372_, v___x_2383_);
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2375_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2387_, lean_object* v_val_2388_, lean_object* v_a_2389_, lean_object* v___x_2390_, lean_object* v_____r_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2387_, v_val_2388_, v_a_2389_, v___x_2390_, v_____r_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v_val_2388_);
lean_dec(v_val_2387_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2398_, lean_object* v_val_2399_, lean_object* v_next_2400_, lean_object* v_next_2401_, lean_object* v___x_2402_, lean_object* v___x_2403_, lean_object* v_upperBound_2404_, lean_object* v_params_2405_, lean_object* v___x_2406_, lean_object* v_a_2407_, uint8_t v_b_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
uint8_t v_a_2415_; uint8_t v___x_2419_; 
v___x_2419_ = lean_nat_dec_lt(v_a_2407_, v_upperBound_2404_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
lean_dec(v_a_2407_);
lean_dec_ref(v___x_2406_);
lean_dec(v_next_2400_);
v___x_2420_ = lean_box(v_b_2408_);
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
return v___x_2421_;
}
else
{
lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = lean_st_ref_get(v_val_2398_);
v___x_2423_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2401_, v_a_2407_, v___x_2422_);
lean_dec(v___x_2422_);
if (v___x_2423_ == 0)
{
v_a_2415_ = v_b_2408_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2424_; uint8_t v_foApprox_2425_; uint8_t v_ctxApprox_2426_; uint8_t v_quasiPatternApprox_2427_; uint8_t v_constApprox_2428_; uint8_t v_isDefEqStuckEx_2429_; uint8_t v_unificationHints_2430_; uint8_t v_assignSyntheticOpaque_2431_; uint8_t v_offsetCnstrs_2432_; uint8_t v_transparency_2433_; uint8_t v_etaStruct_2434_; uint8_t v_univApprox_2435_; uint8_t v_iota_2436_; uint8_t v_beta_2437_; uint8_t v_proj_2438_; uint8_t v_zeta_2439_; uint8_t v_zetaDelta_2440_; uint8_t v_zetaUnused_2441_; uint8_t v_zetaHave_2442_; uint8_t v_canUnfoldPredicateConfig_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2489_; 
v___x_2424_ = l_Lean_Meta_Context_config(v___y_2409_);
v_foApprox_2425_ = lean_ctor_get_uint8(v___x_2424_, 0);
v_ctxApprox_2426_ = lean_ctor_get_uint8(v___x_2424_, 1);
v_quasiPatternApprox_2427_ = lean_ctor_get_uint8(v___x_2424_, 2);
v_constApprox_2428_ = lean_ctor_get_uint8(v___x_2424_, 3);
v_isDefEqStuckEx_2429_ = lean_ctor_get_uint8(v___x_2424_, 4);
v_unificationHints_2430_ = lean_ctor_get_uint8(v___x_2424_, 5);
v_assignSyntheticOpaque_2431_ = lean_ctor_get_uint8(v___x_2424_, 7);
v_offsetCnstrs_2432_ = lean_ctor_get_uint8(v___x_2424_, 8);
v_transparency_2433_ = lean_ctor_get_uint8(v___x_2424_, 9);
v_etaStruct_2434_ = lean_ctor_get_uint8(v___x_2424_, 10);
v_univApprox_2435_ = lean_ctor_get_uint8(v___x_2424_, 11);
v_iota_2436_ = lean_ctor_get_uint8(v___x_2424_, 12);
v_beta_2437_ = lean_ctor_get_uint8(v___x_2424_, 13);
v_proj_2438_ = lean_ctor_get_uint8(v___x_2424_, 14);
v_zeta_2439_ = lean_ctor_get_uint8(v___x_2424_, 15);
v_zetaDelta_2440_ = lean_ctor_get_uint8(v___x_2424_, 16);
v_zetaUnused_2441_ = lean_ctor_get_uint8(v___x_2424_, 17);
v_zetaHave_2442_ = lean_ctor_get_uint8(v___x_2424_, 18);
v_canUnfoldPredicateConfig_2443_ = lean_ctor_get_uint8(v___x_2424_, 19);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2445_ = v___x_2424_;
v_isShared_2446_ = v_isSharedCheck_2489_;
goto v_resetjp_2444_;
}
else
{
lean_dec(v___x_2424_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2489_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
uint8_t v_trackZetaDelta_2447_; lean_object* v_zetaDeltaSet_2448_; lean_object* v_lctx_2449_; lean_object* v_localInstances_2450_; lean_object* v_defEqCtx_x3f_2451_; lean_object* v_synthPendingDepth_2452_; lean_object* v_customCanUnfoldPredicate_x3f_2453_; uint8_t v_univApprox_2454_; uint8_t v_inTypeClassResolution_2455_; uint8_t v_cacheInferType_2456_; uint8_t v___x_2457_; lean_object* v___x_2459_; 
v_trackZetaDelta_2447_ = lean_ctor_get_uint8(v___y_2409_, sizeof(void*)*7);
v_zetaDeltaSet_2448_ = lean_ctor_get(v___y_2409_, 1);
v_lctx_2449_ = lean_ctor_get(v___y_2409_, 2);
v_localInstances_2450_ = lean_ctor_get(v___y_2409_, 3);
v_defEqCtx_x3f_2451_ = lean_ctor_get(v___y_2409_, 4);
v_synthPendingDepth_2452_ = lean_ctor_get(v___y_2409_, 5);
v_customCanUnfoldPredicate_x3f_2453_ = lean_ctor_get(v___y_2409_, 6);
v_univApprox_2454_ = lean_ctor_get_uint8(v___y_2409_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2455_ = lean_ctor_get_uint8(v___y_2409_, sizeof(void*)*7 + 2);
v_cacheInferType_2456_ = lean_ctor_get_uint8(v___y_2409_, sizeof(void*)*7 + 3);
v___x_2457_ = 0;
if (v_isShared_2446_ == 0)
{
v___x_2459_ = v___x_2445_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 0, v_foApprox_2425_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 1, v_ctxApprox_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 2, v_quasiPatternApprox_2427_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 3, v_constApprox_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 4, v_isDefEqStuckEx_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 5, v_unificationHints_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 7, v_assignSyntheticOpaque_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 8, v_offsetCnstrs_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 9, v_transparency_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 10, v_etaStruct_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 11, v_univApprox_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 12, v_iota_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 13, v_beta_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 14, v_proj_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 15, v_zeta_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 16, v_zetaDelta_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 17, v_zetaUnused_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 18, v_zetaHave_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 19, v_canUnfoldPredicateConfig_2443_);
v___x_2459_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
uint64_t v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v_transparency_2464_; uint8_t v___x_2465_; lean_object* v___y_2467_; lean_object* v___x_2481_; uint8_t v___x_2482_; uint8_t v___x_2483_; 
lean_ctor_set_uint8(v___x_2459_, 6, v___x_2457_);
v___x_2460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2459_);
v___x_2461_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set_uint64(v___x_2461_, sizeof(void*)*1, v___x_2460_);
lean_inc(v_customCanUnfoldPredicate_x3f_2453_);
lean_inc(v_synthPendingDepth_2452_);
lean_inc(v_defEqCtx_x3f_2451_);
lean_inc_ref(v_localInstances_2450_);
lean_inc_ref(v_lctx_2449_);
lean_inc(v_zetaDeltaSet_2448_);
lean_inc_ref(v___x_2461_);
v___x_2462_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v_zetaDeltaSet_2448_);
lean_ctor_set(v___x_2462_, 2, v_lctx_2449_);
lean_ctor_set(v___x_2462_, 3, v_localInstances_2450_);
lean_ctor_set(v___x_2462_, 4, v_defEqCtx_x3f_2451_);
lean_ctor_set(v___x_2462_, 5, v_synthPendingDepth_2452_);
lean_ctor_set(v___x_2462_, 6, v_customCanUnfoldPredicate_x3f_2453_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*7, v_trackZetaDelta_2447_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*7 + 1, v_univApprox_2454_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2455_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*7 + 3, v_cacheInferType_2456_);
v___x_2463_ = l_Lean_Meta_Context_config(v___x_2462_);
v_transparency_2464_ = lean_ctor_get_uint8(v___x_2463_, 9);
lean_dec_ref(v___x_2463_);
v___x_2465_ = lean_nat_dec_eq(v___x_2402_, v___x_2403_);
v___x_2481_ = lean_array_fget_borrowed(v_params_2405_, v_a_2407_);
v___x_2482_ = 2;
v___x_2483_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2464_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2462_, 7);
v___x_2484_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2482_, v___x_2461_);
lean_inc(v_customCanUnfoldPredicate_x3f_2453_);
lean_inc(v_synthPendingDepth_2452_);
lean_inc(v_defEqCtx_x3f_2451_);
lean_inc_ref(v_localInstances_2450_);
lean_inc_ref(v_lctx_2449_);
lean_inc(v_zetaDeltaSet_2448_);
v___x_2485_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v_zetaDeltaSet_2448_);
lean_ctor_set(v___x_2485_, 2, v_lctx_2449_);
lean_ctor_set(v___x_2485_, 3, v_localInstances_2450_);
lean_ctor_set(v___x_2485_, 4, v_defEqCtx_x3f_2451_);
lean_ctor_set(v___x_2485_, 5, v_synthPendingDepth_2452_);
lean_ctor_set(v___x_2485_, 6, v_customCanUnfoldPredicate_x3f_2453_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*7, v_trackZetaDelta_2447_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*7 + 1, v_univApprox_2454_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2455_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*7 + 3, v_cacheInferType_2456_);
lean_inc_ref(v___x_2406_);
lean_inc(v___x_2481_);
v___x_2486_ = l_Lean_Meta_isExprDefEq(v___x_2481_, v___x_2406_, v___x_2485_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec_ref_known(v___x_2485_, 7);
v___y_2467_ = v___x_2486_;
goto v___jp_2466_;
}
else
{
lean_object* v___x_2487_; 
lean_dec_ref_known(v___x_2461_, 1);
lean_inc_ref(v___x_2406_);
lean_inc(v___x_2481_);
v___x_2487_ = l_Lean_Meta_isExprDefEq(v___x_2481_, v___x_2406_, v___x_2462_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec_ref_known(v___x_2462_, 7);
v___y_2467_ = v___x_2487_;
goto v___jp_2466_;
}
v___jp_2466_:
{
if (lean_obj_tag(v___y_2467_) == 0)
{
lean_object* v_a_2468_; uint8_t v___x_2469_; 
v_a_2468_ = lean_ctor_get(v___y_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___y_2467_, 1);
v___x_2469_ = lean_unbox(v_a_2468_);
lean_dec(v_a_2468_);
if (v___x_2469_ == 0)
{
v_a_2415_ = v_b_2408_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_st_ref_take(v_val_2398_);
lean_inc(v_a_2407_);
lean_inc(v_next_2400_);
v___x_2471_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2399_, v_next_2400_, v_next_2401_, v_a_2407_, v___x_2470_);
v___x_2472_ = lean_st_ref_put(v_val_2398_, v___x_2471_);
v_a_2415_ = v___x_2465_;
goto v___jp_2414_;
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v_a_2407_);
lean_dec_ref(v___x_2406_);
lean_dec(v_next_2400_);
v_a_2473_ = lean_ctor_get(v___y_2467_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___y_2467_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___y_2467_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___y_2467_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
}
}
}
v___jp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_nat_add(v_a_2407_, v___x_2416_);
lean_dec(v_a_2407_);
v_a_2407_ = v___x_2417_;
v_b_2408_ = v_a_2415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2490_, lean_object* v_val_2491_, lean_object* v_next_2492_, lean_object* v_next_2493_, lean_object* v___x_2494_, lean_object* v___x_2495_, lean_object* v_upperBound_2496_, lean_object* v_params_2497_, lean_object* v___x_2498_, lean_object* v_a_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
uint8_t v_b_boxed_2506_; lean_object* v_res_2507_; 
v_b_boxed_2506_ = lean_unbox(v_b_2500_);
v_res_2507_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2490_, v_val_2491_, v_next_2492_, v_next_2493_, v___x_2494_, v___x_2495_, v_upperBound_2496_, v_params_2497_, v___x_2498_, v_a_2499_, v_b_boxed_2506_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_params_2497_);
lean_dec(v_upperBound_2496_);
lean_dec(v___x_2495_);
lean_dec(v___x_2494_);
lean_dec(v_next_2493_);
lean_dec(v_val_2491_);
lean_dec(v_val_2490_);
return v_res_2507_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2520_ = l_Lean_Name_append(v___x_2519_, v___x_2518_);
return v___x_2520_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2523_ = l_Lean_stringToMessageData(v___x_2522_);
return v___x_2523_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2525_ = l_Lean_stringToMessageData(v___x_2524_);
return v___x_2525_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2528_ = l_Lean_stringToMessageData(v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2534_ = l_Lean_stringToMessageData(v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2537_ = l_Lean_stringToMessageData(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2541_, lean_object* v_val_2542_, lean_object* v_upperBound_2543_, lean_object* v_args_2544_, lean_object* v_e_2545_, lean_object* v_next_2546_, lean_object* v_params_2547_, lean_object* v___x_2548_, lean_object* v___x_2549_, lean_object* v_a_2550_, lean_object* v_b_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_a_2558_; lean_object* v___y_2563_; uint8_t v___x_2582_; 
v___x_2582_ = lean_nat_dec_lt(v_a_2550_, v_upperBound_2543_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v___x_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_b_2551_);
return v___x_2583_;
}
else
{
lean_object* v___x_2584_; 
v___x_2584_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2541_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___x_2586_ = lean_box(0);
v___x_2587_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2542_, v_a_2550_, v_a_2585_);
lean_dec(v_a_2585_);
if (v___x_2587_ == 0)
{
v_a_2558_ = v___x_2586_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = lean_array_get_size(v_args_2544_);
v___x_2589_ = lean_nat_dec_lt(v_a_2550_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v_options_2590_; lean_object* v_toCold_2591_; uint8_t v_hasTrace_2592_; 
v_options_2590_ = lean_ctor_get(v___y_2554_, 1);
v_toCold_2591_ = lean_ctor_get(v___y_2554_, 0);
v_hasTrace_2592_ = lean_ctor_get_uint8(v_options_2590_, sizeof(void*)*1);
if (v_hasTrace_2592_ == 0)
{
goto v___jp_2593_;
}
else
{
lean_object* v_inheritedTraceOptions_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v_inheritedTraceOptions_2595_ = lean_ctor_get(v_toCold_2591_, 4);
v___x_2596_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2597_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2598_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2595_, v_options_2590_, v___x_2597_);
if (v___x_2598_ == 0)
{
goto v___jp_2593_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2599_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2542_);
v___x_2600_ = l_Nat_reprFast(v_val_2542_);
v___x_2601_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
v___x_2602_ = l_Lean_MessageData_ofFormat(v___x_2601_);
v___x_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2599_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
lean_inc(v_a_2550_);
v___x_2606_ = l_Nat_reprFast(v_a_2550_);
v___x_2607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
v___x_2608_ = l_Lean_MessageData_ofFormat(v___x_2607_);
lean_inc_ref(v___x_2608_);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2605_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
lean_inc_ref(v_e_2545_);
v___x_2612_ = l_Lean_MessageData_ofExpr(v_e_2545_);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2608_);
v___x_2617_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2596_, v___x_2616_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2617_, 1);
lean_inc(v_a_2550_);
v___x_2619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2586_, v_a_2618_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2619_;
goto v___jp_2562_;
}
else
{
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
return v___x_2617_;
}
}
}
v___jp_2593_:
{
lean_object* v___x_2594_; 
lean_inc(v_a_2550_);
v___x_2594_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2586_, v___x_2586_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2594_;
goto v___jp_2562_;
}
}
else
{
lean_object* v___x_2620_; 
v___x_2620_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2541_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = lean_array_fget_borrowed(v_args_2544_, v_a_2550_);
v___x_2623_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2542_, v_a_2550_, v_next_2546_, v_a_2621_);
lean_dec(v_a_2621_);
if (lean_obj_tag(v___x_2623_) == 1)
{
lean_object* v_val_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2728_; 
v_val_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2728_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_val_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2728_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; uint8_t v_foApprox_2629_; uint8_t v_ctxApprox_2630_; uint8_t v_quasiPatternApprox_2631_; uint8_t v_constApprox_2632_; uint8_t v_isDefEqStuckEx_2633_; uint8_t v_unificationHints_2634_; uint8_t v_assignSyntheticOpaque_2635_; uint8_t v_offsetCnstrs_2636_; uint8_t v_transparency_2637_; uint8_t v_etaStruct_2638_; uint8_t v_univApprox_2639_; uint8_t v_iota_2640_; uint8_t v_beta_2641_; uint8_t v_proj_2642_; uint8_t v_zeta_2643_; uint8_t v_zetaDelta_2644_; uint8_t v_zetaUnused_2645_; uint8_t v_zetaHave_2646_; uint8_t v_canUnfoldPredicateConfig_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2727_; 
v___x_2628_ = l_Lean_Meta_Context_config(v___y_2552_);
v_foApprox_2629_ = lean_ctor_get_uint8(v___x_2628_, 0);
v_ctxApprox_2630_ = lean_ctor_get_uint8(v___x_2628_, 1);
v_quasiPatternApprox_2631_ = lean_ctor_get_uint8(v___x_2628_, 2);
v_constApprox_2632_ = lean_ctor_get_uint8(v___x_2628_, 3);
v_isDefEqStuckEx_2633_ = lean_ctor_get_uint8(v___x_2628_, 4);
v_unificationHints_2634_ = lean_ctor_get_uint8(v___x_2628_, 5);
v_assignSyntheticOpaque_2635_ = lean_ctor_get_uint8(v___x_2628_, 7);
v_offsetCnstrs_2636_ = lean_ctor_get_uint8(v___x_2628_, 8);
v_transparency_2637_ = lean_ctor_get_uint8(v___x_2628_, 9);
v_etaStruct_2638_ = lean_ctor_get_uint8(v___x_2628_, 10);
v_univApprox_2639_ = lean_ctor_get_uint8(v___x_2628_, 11);
v_iota_2640_ = lean_ctor_get_uint8(v___x_2628_, 12);
v_beta_2641_ = lean_ctor_get_uint8(v___x_2628_, 13);
v_proj_2642_ = lean_ctor_get_uint8(v___x_2628_, 14);
v_zeta_2643_ = lean_ctor_get_uint8(v___x_2628_, 15);
v_zetaDelta_2644_ = lean_ctor_get_uint8(v___x_2628_, 16);
v_zetaUnused_2645_ = lean_ctor_get_uint8(v___x_2628_, 17);
v_zetaHave_2646_ = lean_ctor_get_uint8(v___x_2628_, 18);
v_canUnfoldPredicateConfig_2647_ = lean_ctor_get_uint8(v___x_2628_, 19);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2649_ = v___x_2628_;
v_isShared_2650_ = v_isSharedCheck_2727_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v___x_2628_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2727_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
uint8_t v_trackZetaDelta_2651_; lean_object* v_zetaDeltaSet_2652_; lean_object* v_lctx_2653_; lean_object* v_localInstances_2654_; lean_object* v_defEqCtx_x3f_2655_; lean_object* v_synthPendingDepth_2656_; lean_object* v_customCanUnfoldPredicate_x3f_2657_; uint8_t v_univApprox_2658_; uint8_t v_inTypeClassResolution_2659_; uint8_t v_cacheInferType_2660_; uint8_t v___x_2661_; lean_object* v___x_2663_; 
v_trackZetaDelta_2651_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*7);
v_zetaDeltaSet_2652_ = lean_ctor_get(v___y_2552_, 1);
v_lctx_2653_ = lean_ctor_get(v___y_2552_, 2);
v_localInstances_2654_ = lean_ctor_get(v___y_2552_, 3);
v_defEqCtx_x3f_2655_ = lean_ctor_get(v___y_2552_, 4);
v_synthPendingDepth_2656_ = lean_ctor_get(v___y_2552_, 5);
v_customCanUnfoldPredicate_x3f_2657_ = lean_ctor_get(v___y_2552_, 6);
v_univApprox_2658_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2659_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*7 + 2);
v_cacheInferType_2660_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*7 + 3);
v___x_2661_ = 0;
if (v_isShared_2650_ == 0)
{
v___x_2663_ = v___x_2649_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 0, v_foApprox_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 1, v_ctxApprox_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 2, v_quasiPatternApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 3, v_constApprox_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 4, v_isDefEqStuckEx_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 5, v_unificationHints_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 7, v_assignSyntheticOpaque_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 8, v_offsetCnstrs_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 9, v_transparency_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 10, v_etaStruct_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 11, v_univApprox_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 12, v_iota_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 13, v_beta_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 14, v_proj_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 15, v_zeta_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 16, v_zetaDelta_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 17, v_zetaUnused_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 18, v_zetaHave_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2726_, 19, v_canUnfoldPredicateConfig_2647_);
v___x_2663_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
uint64_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v_transparency_2668_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___y_2674_; uint8_t v___x_2720_; uint8_t v___x_2721_; 
lean_ctor_set_uint8(v___x_2663_, 6, v___x_2661_);
v___x_2664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2663_);
v___x_2665_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set_uint64(v___x_2665_, sizeof(void*)*1, v___x_2664_);
lean_inc(v_customCanUnfoldPredicate_x3f_2657_);
lean_inc(v_synthPendingDepth_2656_);
lean_inc(v_defEqCtx_x3f_2655_);
lean_inc_ref(v_localInstances_2654_);
lean_inc_ref(v_lctx_2653_);
lean_inc(v_zetaDeltaSet_2652_);
lean_inc_ref(v___x_2665_);
v___x_2666_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v_zetaDeltaSet_2652_);
lean_ctor_set(v___x_2666_, 2, v_lctx_2653_);
lean_ctor_set(v___x_2666_, 3, v_localInstances_2654_);
lean_ctor_set(v___x_2666_, 4, v_defEqCtx_x3f_2655_);
lean_ctor_set(v___x_2666_, 5, v_synthPendingDepth_2656_);
lean_ctor_set(v___x_2666_, 6, v_customCanUnfoldPredicate_x3f_2657_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*7, v_trackZetaDelta_2651_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*7 + 1, v_univApprox_2658_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2659_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*7 + 3, v_cacheInferType_2660_);
v___x_2667_ = l_Lean_Meta_Context_config(v___x_2666_);
v_transparency_2668_ = lean_ctor_get_uint8(v___x_2667_, 9);
lean_dec_ref(v___x_2667_);
v___x_2671_ = l_Lean_instInhabitedExpr;
v___x_2672_ = lean_array_get_borrowed(v___x_2671_, v_params_2547_, v_val_2624_);
lean_dec(v_val_2624_);
v___x_2720_ = 2;
v___x_2721_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2668_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
lean_dec_ref_known(v___x_2666_, 7);
v___x_2722_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2720_, v___x_2665_);
lean_inc(v_customCanUnfoldPredicate_x3f_2657_);
lean_inc(v_synthPendingDepth_2656_);
lean_inc(v_defEqCtx_x3f_2655_);
lean_inc_ref(v_localInstances_2654_);
lean_inc_ref(v_lctx_2653_);
lean_inc(v_zetaDeltaSet_2652_);
v___x_2723_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v_zetaDeltaSet_2652_);
lean_ctor_set(v___x_2723_, 2, v_lctx_2653_);
lean_ctor_set(v___x_2723_, 3, v_localInstances_2654_);
lean_ctor_set(v___x_2723_, 4, v_defEqCtx_x3f_2655_);
lean_ctor_set(v___x_2723_, 5, v_synthPendingDepth_2656_);
lean_ctor_set(v___x_2723_, 6, v_customCanUnfoldPredicate_x3f_2657_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7, v_trackZetaDelta_2651_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 1, v_univApprox_2658_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2659_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*7 + 3, v_cacheInferType_2660_);
lean_inc(v___x_2622_);
lean_inc(v___x_2672_);
v___x_2724_ = l_Lean_Meta_isExprDefEq(v___x_2672_, v___x_2622_, v___x_2723_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec_ref_known(v___x_2723_, 7);
v___y_2674_ = v___x_2724_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2725_; 
lean_dec_ref_known(v___x_2665_, 1);
lean_inc(v___x_2622_);
lean_inc(v___x_2672_);
v___x_2725_ = l_Lean_Meta_isExprDefEq(v___x_2672_, v___x_2622_, v___x_2666_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec_ref_known(v___x_2666_, 7);
v___y_2674_ = v___x_2725_;
goto v___jp_2673_;
}
v___jp_2669_:
{
lean_object* v___x_2670_; 
lean_inc(v_a_2550_);
v___x_2670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2586_, v___x_2586_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2670_;
goto v___jp_2562_;
}
v___jp_2673_:
{
if (lean_obj_tag(v___y_2674_) == 0)
{
lean_object* v_a_2675_; uint8_t v___x_2676_; 
v_a_2675_ = lean_ctor_get(v___y_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___y_2674_, 1);
v___x_2676_ = lean_unbox(v_a_2675_);
lean_dec(v_a_2675_);
if (v___x_2676_ == 0)
{
lean_object* v_options_2677_; uint8_t v_hasTrace_2678_; 
v_options_2677_ = lean_ctor_get(v___y_2554_, 1);
v_hasTrace_2678_ = lean_ctor_get_uint8(v_options_2677_, sizeof(void*)*1);
if (v_hasTrace_2678_ == 0)
{
lean_del_object(v___x_2626_);
goto v___jp_2669_;
}
else
{
lean_object* v_toCold_2679_; lean_object* v_inheritedTraceOptions_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_toCold_2679_ = lean_ctor_get(v___y_2554_, 0);
v_inheritedTraceOptions_2680_ = lean_ctor_get(v_toCold_2679_, 4);
v___x_2681_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2682_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2683_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2680_, v_options_2677_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_del_object(v___x_2626_);
goto v___jp_2669_;
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2684_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2542_);
v___x_2685_ = l_Nat_reprFast(v_val_2542_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set_tag(v___x_2626_, 3);
lean_ctor_set(v___x_2626_, 0, v___x_2685_);
v___x_2687_ = v___x_2626_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2688_ = l_Lean_MessageData_ofFormat(v___x_2687_);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2684_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2689_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
lean_inc(v_a_2550_);
v___x_2692_ = l_Nat_reprFast(v_a_2550_);
v___x_2693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
v___x_2694_ = l_Lean_MessageData_ofFormat(v___x_2693_);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2691_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
lean_inc_ref(v_e_2545_);
v___x_2698_ = l_Lean_MessageData_ofExpr(v_e_2545_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
lean_inc(v___x_2672_);
v___x_2702_ = l_Lean_MessageData_ofExpr(v___x_2672_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
lean_inc(v___x_2622_);
v___x_2706_ = l_Lean_MessageData_ofExpr(v___x_2622_);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2681_, v___x_2707_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2710_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
lean_inc(v_a_2550_);
v___x_2710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2586_, v_a_2709_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2710_;
goto v___jp_2562_;
}
else
{
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
return v___x_2708_;
}
}
}
}
}
else
{
lean_del_object(v___x_2626_);
v_a_2558_ = v___x_2586_;
goto v___jp_2557_;
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_del_object(v___x_2626_);
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v_a_2712_ = lean_ctor_get(v___y_2674_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___y_2674_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___y_2674_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___y_2674_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
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
lean_object* v___x_2729_; uint8_t v___x_2730_; lean_object* v___x_2731_; 
lean_dec(v___x_2623_);
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = 0;
lean_inc(v___x_2622_);
lean_inc(v_a_2550_);
v___x_2731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2541_, v_val_2542_, v_a_2550_, v_next_2546_, v___x_2548_, v___x_2549_, v___x_2548_, v_params_2547_, v___x_2622_, v___x_2729_, v___x_2730_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; uint8_t v___x_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = lean_unbox(v_a_2732_);
lean_dec(v_a_2732_);
if (v___x_2733_ == 0)
{
lean_object* v_options_2734_; lean_object* v_toCold_2735_; uint8_t v_hasTrace_2736_; 
v_options_2734_ = lean_ctor_get(v___y_2554_, 1);
v_toCold_2735_ = lean_ctor_get(v___y_2554_, 0);
v_hasTrace_2736_ = lean_ctor_get_uint8(v_options_2734_, sizeof(void*)*1);
if (v_hasTrace_2736_ == 0)
{
goto v___jp_2737_;
}
else
{
lean_object* v_inheritedTraceOptions_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v_inheritedTraceOptions_2739_ = lean_ctor_get(v_toCold_2735_, 4);
v___x_2740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2741_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2739_, v_options_2734_, v___x_2741_);
if (v___x_2742_ == 0)
{
goto v___jp_2737_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2743_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2542_);
v___x_2744_ = l_Nat_reprFast(v_val_2542_);
v___x_2745_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
v___x_2746_ = l_Lean_MessageData_ofFormat(v___x_2745_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2743_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
lean_inc(v_a_2550_);
v___x_2750_ = l_Nat_reprFast(v_a_2550_);
v___x_2751_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
v___x_2752_ = l_Lean_MessageData_ofFormat(v___x_2751_);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2749_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
lean_inc_ref(v_e_2545_);
v___x_2756_ = l_Lean_MessageData_ofExpr(v_e_2545_);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
lean_inc(v___x_2622_);
v___x_2760_ = l_Lean_MessageData_ofExpr(v___x_2622_);
v___x_2761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2740_, v___x_2763_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
lean_inc(v_a_2550_);
v___x_2766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2586_, v_a_2765_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2766_;
goto v___jp_2562_;
}
else
{
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
return v___x_2764_;
}
}
}
v___jp_2737_:
{
lean_object* v___x_2738_; 
lean_inc(v_a_2550_);
v___x_2738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2586_, v___x_2586_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2738_;
goto v___jp_2562_;
}
}
else
{
v_a_2558_ = v___x_2586_;
goto v___jp_2557_;
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v_a_2767_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2731_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2731_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v_a_2775_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2620_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2620_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v_a_2783_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2584_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2584_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
v___jp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_unsigned_to_nat(1u);
v___x_2560_ = lean_nat_add(v_a_2550_, v___x_2559_);
lean_dec(v_a_2550_);
v_a_2550_ = v___x_2560_;
v_b_2551_ = v_a_2558_;
goto _start;
}
v___jp_2562_:
{
if (lean_obj_tag(v___y_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2573_; 
v_a_2564_ = lean_ctor_get(v___y_2563_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___y_2563_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2566_ = v___y_2563_;
v_isShared_2567_ = v_isSharedCheck_2573_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___y_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2573_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
if (lean_obj_tag(v_a_2564_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v_a_2568_ = lean_ctor_get(v_a_2564_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v_a_2564_, 1);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v_a_2568_);
v___x_2570_ = v___x_2566_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
else
{
lean_object* v_a_2572_; 
lean_del_object(v___x_2566_);
v_a_2572_ = lean_ctor_get(v_a_2564_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v_a_2564_, 1);
v_a_2558_ = v_a_2572_;
goto v___jp_2557_;
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v_a_2574_ = lean_ctor_get(v___y_2563_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___y_2563_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___y_2563_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___y_2563_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2791_, lean_object* v_val_2792_, lean_object* v_upperBound_2793_, lean_object* v_args_2794_, lean_object* v_e_2795_, lean_object* v_next_2796_, lean_object* v_params_2797_, lean_object* v___x_2798_, lean_object* v___x_2799_, lean_object* v_a_2800_, lean_object* v_b_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2791_, v_val_2792_, v_upperBound_2793_, v_args_2794_, v_e_2795_, v_next_2796_, v_params_2797_, v___x_2798_, v___x_2799_, v_a_2800_, v_b_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___x_2799_);
lean_dec(v___x_2798_);
lean_dec_ref(v_params_2797_);
lean_dec(v_next_2796_);
lean_dec_ref(v_args_2794_);
lean_dec(v_upperBound_2793_);
lean_dec(v_val_2791_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2810_, lean_object* v___x_2811_, lean_object* v_val_2812_, lean_object* v_e_2813_, lean_object* v_next_2814_, lean_object* v_params_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
if (lean_obj_tag(v_x_2818_) == 5)
{
lean_object* v_fn_2826_; lean_object* v_arg_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_fn_2826_ = lean_ctor_get(v_x_2818_, 0);
lean_inc_ref(v_fn_2826_);
v_arg_2827_ = lean_ctor_get(v_x_2818_, 1);
lean_inc_ref(v_arg_2827_);
lean_dec_ref_known(v_x_2818_, 2);
v___x_2828_ = lean_array_set(v_x_2819_, v_x_2820_, v_arg_2827_);
v___x_2829_ = lean_unsigned_to_nat(1u);
v___x_2830_ = lean_nat_sub(v_x_2820_, v___x_2829_);
lean_dec(v_x_2820_);
v_x_2818_ = v_fn_2826_;
v_x_2819_ = v___x_2828_;
v_x_2820_ = v___x_2830_;
goto _start;
}
else
{
uint8_t v___x_2832_; 
lean_dec(v_x_2820_);
v___x_2832_ = l_Lean_Expr_isConst(v_x_2818_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_x_2819_);
lean_dec_ref(v_x_2818_);
lean_dec_ref(v_e_2813_);
v___x_2833_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2835_ = l_Lean_Expr_constName_x21(v_x_2818_);
lean_dec_ref(v_x_2818_);
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2835_, v_preDefs_2810_, v___x_2836_);
lean_dec(v___x_2835_);
if (lean_obj_tag(v___x_2837_) == 1)
{
lean_object* v_val_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_val_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_val_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_array_get_borrowed(v___x_2836_, v___x_2811_, v_val_2838_);
v___x_2841_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2812_, v_val_2838_, v___x_2840_, v_x_2819_, v_e_2813_, v_next_2814_, v_params_2815_, v___x_2816_, v___x_2817_, v___x_2836_, v___x_2839_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v_x_2819_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2849_; 
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2841_, 0);
lean_dec(v_unused_2850_);
v___x_2843_ = v___x_2841_;
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
else
{
lean_dec(v___x_2841_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2845_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2845_);
v___x_2847_ = v___x_2843_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
v_a_2851_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2841_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2841_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_dec(v___x_2837_);
lean_dec_ref(v_x_2819_);
lean_dec_ref(v_e_2813_);
v___x_2859_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2861_, lean_object* v___x_2862_, lean_object* v_val_2863_, lean_object* v_e_2864_, lean_object* v_next_2865_, lean_object* v_params_2866_, lean_object* v___x_2867_, lean_object* v___x_2868_, lean_object* v_x_2869_, lean_object* v_x_2870_, lean_object* v_x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2861_, v___x_2862_, v_val_2863_, v_e_2864_, v_next_2865_, v_params_2866_, v___x_2867_, v___x_2868_, v_x_2869_, v_x_2870_, v_x_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec_ref(v_params_2866_);
lean_dec(v_next_2865_);
lean_dec(v_val_2863_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2878_, lean_object* v___x_2879_, lean_object* v_val_2880_, lean_object* v_a_2881_, lean_object* v_params_2882_, lean_object* v___x_2883_, lean_object* v___x_2884_, lean_object* v_e_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_dummy_2891_; lean_object* v_nargs_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_dummy_2891_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2892_ = l_Lean_Expr_getAppNumArgs(v_e_2885_);
lean_inc(v_nargs_2892_);
v___x_2893_ = lean_mk_array(v_nargs_2892_, v_dummy_2891_);
v___x_2894_ = lean_unsigned_to_nat(1u);
v___x_2895_ = lean_nat_sub(v_nargs_2892_, v___x_2894_);
lean_dec(v_nargs_2892_);
lean_inc_ref(v_e_2885_);
v___x_2896_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2878_, v___x_2879_, v_val_2880_, v_e_2885_, v_a_2881_, v_params_2882_, v___x_2883_, v___x_2884_, v_e_2885_, v___x_2893_, v___x_2895_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2897_, lean_object* v___x_2898_, lean_object* v_val_2899_, lean_object* v_a_2900_, lean_object* v_params_2901_, lean_object* v___x_2902_, lean_object* v___x_2903_, lean_object* v_e_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2897_, v___x_2898_, v_val_2899_, v_a_2900_, v_params_2901_, v___x_2902_, v___x_2903_, v_e_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___x_2903_);
lean_dec(v___x_2902_);
lean_dec_ref(v_params_2901_);
lean_dec(v_a_2900_);
lean_dec(v_val_2899_);
lean_dec_ref(v___x_2898_);
lean_dec_ref(v_preDefs_2897_);
return v_res_2910_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2914_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2915_ = lean_unsigned_to_nat(6u);
v___x_2916_ = lean_unsigned_to_nat(201u);
v___x_2917_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2918_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2919_ = l_mkPanicMessageWithDecl(v___x_2918_, v___x_2917_, v___x_2916_, v___x_2915_, v___x_2914_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2920_, lean_object* v___x_2921_, lean_object* v_a_2922_, lean_object* v_preDefs_2923_, lean_object* v_val_2924_, lean_object* v___f_2925_, lean_object* v___x_2926_, lean_object* v_params_2927_, lean_object* v_body_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2934_ = lean_array_get_size(v_params_2927_);
v___x_2935_ = lean_array_get(v___x_2920_, v___x_2921_, v_a_2922_);
v___x_2936_ = lean_nat_dec_eq(v___x_2934_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_dec(v___x_2935_);
lean_dec_ref(v_body_2928_);
lean_dec_ref(v_params_2927_);
lean_dec_ref(v___f_2925_);
lean_dec(v_val_2924_);
lean_dec_ref(v_preDefs_2923_);
lean_dec(v_a_2922_);
lean_dec_ref(v___x_2921_);
v___x_2937_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2938_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2937_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
return v___x_2938_;
}
else
{
lean_object* v___f_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; 
v___f_2939_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2939_, 0, v_preDefs_2923_);
lean_closure_set(v___f_2939_, 1, v___x_2921_);
lean_closure_set(v___f_2939_, 2, v_val_2924_);
lean_closure_set(v___f_2939_, 3, v_a_2922_);
lean_closure_set(v___f_2939_, 4, v_params_2927_);
lean_closure_set(v___f_2939_, 5, v___x_2934_);
lean_closure_set(v___f_2939_, 6, v___x_2935_);
v___x_2940_ = 0;
v___x_2941_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2928_, v___f_2939_, v___f_2925_, v___x_2940_, v___x_2936_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; 
v_unused_2949_ = lean_ctor_get(v___x_2941_, 0);
lean_dec(v_unused_2949_);
v___x_2943_ = v___x_2941_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_dec(v___x_2941_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2926_);
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2926_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_a_2950_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2941_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2941_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2958_, lean_object* v___x_2959_, lean_object* v_a_2960_, lean_object* v_preDefs_2961_, lean_object* v_val_2962_, lean_object* v___f_2963_, lean_object* v___x_2964_, lean_object* v_params_2965_, lean_object* v_body_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2958_, v___x_2959_, v_a_2960_, v_preDefs_2961_, v_val_2962_, v___f_2963_, v___x_2964_, v_params_2965_, v_body_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___x_2958_);
return v_res_2972_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_e_2973_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v___x_2989_, lean_object* v_preDefs_2990_, lean_object* v_val_2991_, lean_object* v_upperBound_2992_, lean_object* v_a_2993_, lean_object* v_b_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_nat_dec_lt(v_a_2993_, v_upperBound_2992_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_a_2993_);
lean_dec(v_val_2991_);
lean_dec_ref(v_preDefs_2990_);
lean_dec_ref(v___x_2989_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_b_2994_);
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; lean_object* v_value_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___f_3007_; uint8_t v___x_3008_; lean_object* v___x_3009_; 
v___x_3002_ = lean_array_fget_borrowed(v_preDefs_2990_, v_a_2993_);
v_value_3003_ = lean_ctor_get(v___x_3002_, 7);
v___f_3004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3005_ = lean_unsigned_to_nat(0u);
v___x_3006_ = lean_box(0);
lean_inc(v_val_2991_);
lean_inc_ref(v_preDefs_2990_);
lean_inc(v_a_2993_);
lean_inc_ref(v___x_2989_);
v___f_3007_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3007_, 0, v___x_3005_);
lean_closure_set(v___f_3007_, 1, v___x_2989_);
lean_closure_set(v___f_3007_, 2, v_a_2993_);
lean_closure_set(v___f_3007_, 3, v_preDefs_2990_);
lean_closure_set(v___f_3007_, 4, v_val_2991_);
lean_closure_set(v___f_3007_, 5, v___f_3004_);
lean_closure_set(v___f_3007_, 6, v___x_3006_);
v___x_3008_ = 0;
lean_inc_ref(v_value_3003_);
v___x_3009_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3003_, v___f_3007_, v___x_3008_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_dec_ref_known(v___x_3009_, 1);
v___x_3010_ = lean_unsigned_to_nat(1u);
v___x_3011_ = lean_nat_add(v_a_2993_, v___x_3010_);
lean_dec(v_a_2993_);
v_a_2993_ = v___x_3011_;
v_b_2994_ = v___x_3006_;
goto _start;
}
else
{
lean_dec(v_a_2993_);
lean_dec(v_val_2991_);
lean_dec_ref(v_preDefs_2990_);
lean_dec_ref(v___x_2989_);
return v___x_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v___x_3013_, lean_object* v_preDefs_3014_, lean_object* v_val_3015_, lean_object* v_upperBound_3016_, lean_object* v_a_3017_, lean_object* v_b_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3013_, v_preDefs_3014_, v_val_3015_, v_upperBound_3016_, v_a_3017_, v_b_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v_upperBound_3016_);
return v_res_3024_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3027_ = l_Lean_stringToMessageData(v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
size_t v_sz_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v_sz_3034_ = lean_array_size(v_preDefs_3028_);
v___x_3035_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3028_);
v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3034_, v___x_3035_, v_preDefs_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; size_t v_sz_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc_n(v_a_3037_, 2);
lean_dec_ref_known(v___x_3036_, 1);
v_sz_3038_ = lean_array_size(v_a_3037_);
v___x_3039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3038_, v___x_3035_, v_a_3037_);
v___x_3040_ = l_Lean_Elab_FixedParams_Info_init(v_a_3037_);
v___x_3041_ = lean_st_mk_ref(v___x_3040_);
v___x_3042_ = lean_st_ref_take(v___x_3041_);
v___x_3043_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3042_);
v___x_3044_ = lean_st_ref_put(v___x_3041_, v___x_3043_);
v___x_3045_ = lean_array_get_size(v_preDefs_3028_);
v___x_3046_ = lean_unsigned_to_nat(0u);
v___x_3047_ = lean_box(0);
lean_inc(v___x_3041_);
v___x_3048_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3039_, v_preDefs_3028_, v___x_3041_, v___x_3045_, v___x_3046_, v___x_3047_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3088_; 
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3088_ == 0)
{
lean_object* v_unused_3089_; 
v_unused_3089_ = lean_ctor_get(v___x_3048_, 0);
lean_dec(v_unused_3089_);
v___x_3050_ = v___x_3048_;
v_isShared_3051_ = v_isSharedCheck_3088_;
goto v_resetjp_3049_;
}
else
{
lean_dec(v___x_3048_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3088_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v_options_3053_; uint8_t v_hasTrace_3054_; 
v___x_3052_ = lean_st_ref_get(v___x_3041_);
lean_dec(v___x_3041_);
v_options_3053_ = lean_ctor_get(v_a_3031_, 1);
v_hasTrace_3054_ = lean_ctor_get_uint8(v_options_3053_, sizeof(void*)*1);
if (v_hasTrace_3054_ == 0)
{
lean_object* v___x_3056_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3052_);
v___x_3056_ = v___x_3050_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3052_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
else
{
lean_object* v_toCold_3058_; lean_object* v_inheritedTraceOptions_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_toCold_3058_ = lean_ctor_get(v_a_3031_, 0);
v_inheritedTraceOptions_3059_ = lean_ctor_get(v_toCold_3058_, 4);
v___x_3060_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3061_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3062_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3059_, v_options_3053_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3064_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3052_);
v___x_3064_ = v___x_3050_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3052_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
lean_del_object(v___x_3050_);
v___x_3066_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3052_);
v___x_3067_ = l_Lean_Elab_FixedParams_Info_format(v___x_3052_);
v___x_3068_ = l_Std_Format_indentD(v___x_3067_);
v___x_3069_ = l_Lean_MessageData_ofFormat(v___x_3068_);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3066_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3060_, v___x_3070_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v___x_3071_, 0);
lean_dec(v_unused_3079_);
v___x_3073_ = v___x_3071_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_dec(v___x_3071_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3052_);
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3052_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v___x_3052_);
v_a_3080_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3071_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3071_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v___x_3041_);
v_a_3090_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3048_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3048_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref(v_preDefs_3028_);
v_a_3098_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3036_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3036_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3106_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
lean_dec(v_a_3108_);
lean_dec_ref(v_a_3107_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3113_, lean_object* v_val_3114_, lean_object* v_next_3115_, lean_object* v_next_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v_upperBound_3119_, lean_object* v_params_3120_, lean_object* v___x_3121_, lean_object* v_inst_3122_, lean_object* v_R_3123_, lean_object* v_a_3124_, uint8_t v_b_3125_, lean_object* v_c_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3113_, v_val_3114_, v_next_3115_, v_next_3116_, v___x_3117_, v___x_3118_, v_upperBound_3119_, v_params_3120_, v___x_3121_, v_a_3124_, v_b_3125_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3133_ = _args[0];
lean_object* v_val_3134_ = _args[1];
lean_object* v_next_3135_ = _args[2];
lean_object* v_next_3136_ = _args[3];
lean_object* v___x_3137_ = _args[4];
lean_object* v___x_3138_ = _args[5];
lean_object* v_upperBound_3139_ = _args[6];
lean_object* v_params_3140_ = _args[7];
lean_object* v___x_3141_ = _args[8];
lean_object* v_inst_3142_ = _args[9];
lean_object* v_R_3143_ = _args[10];
lean_object* v_a_3144_ = _args[11];
lean_object* v_b_3145_ = _args[12];
lean_object* v_c_3146_ = _args[13];
lean_object* v___y_3147_ = _args[14];
lean_object* v___y_3148_ = _args[15];
lean_object* v___y_3149_ = _args[16];
lean_object* v___y_3150_ = _args[17];
lean_object* v___y_3151_ = _args[18];
_start:
{
uint8_t v_b_boxed_3152_; lean_object* v_res_3153_; 
v_b_boxed_3152_ = lean_unbox(v_b_3145_);
v_res_3153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3133_, v_val_3134_, v_next_3135_, v_next_3136_, v___x_3137_, v___x_3138_, v_upperBound_3139_, v_params_3140_, v___x_3141_, v_inst_3142_, v_R_3143_, v_a_3144_, v_b_boxed_3152_, v_c_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec_ref(v_params_3140_);
lean_dec(v_upperBound_3139_);
lean_dec(v___x_3138_);
lean_dec(v___x_3137_);
lean_dec(v_next_3136_);
lean_dec(v_val_3134_);
lean_dec(v_val_3133_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3154_, lean_object* v_val_3155_, lean_object* v_upperBound_3156_, lean_object* v_args_3157_, lean_object* v_e_3158_, lean_object* v_next_3159_, lean_object* v_params_3160_, lean_object* v___x_3161_, lean_object* v___x_3162_, lean_object* v_inst_3163_, lean_object* v_R_3164_, lean_object* v_a_3165_, lean_object* v_b_3166_, lean_object* v_c_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3154_, v_val_3155_, v_upperBound_3156_, v_args_3157_, v_e_3158_, v_next_3159_, v_params_3160_, v___x_3161_, v___x_3162_, v_a_3165_, v_b_3166_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3174_ = _args[0];
lean_object* v_val_3175_ = _args[1];
lean_object* v_upperBound_3176_ = _args[2];
lean_object* v_args_3177_ = _args[3];
lean_object* v_e_3178_ = _args[4];
lean_object* v_next_3179_ = _args[5];
lean_object* v_params_3180_ = _args[6];
lean_object* v___x_3181_ = _args[7];
lean_object* v___x_3182_ = _args[8];
lean_object* v_inst_3183_ = _args[9];
lean_object* v_R_3184_ = _args[10];
lean_object* v_a_3185_ = _args[11];
lean_object* v_b_3186_ = _args[12];
lean_object* v_c_3187_ = _args[13];
lean_object* v___y_3188_ = _args[14];
lean_object* v___y_3189_ = _args[15];
lean_object* v___y_3190_ = _args[16];
lean_object* v___y_3191_ = _args[17];
lean_object* v___y_3192_ = _args[18];
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3174_, v_val_3175_, v_upperBound_3176_, v_args_3177_, v_e_3178_, v_next_3179_, v_params_3180_, v___x_3181_, v___x_3182_, v_inst_3183_, v_R_3184_, v_a_3185_, v_b_3186_, v_c_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___x_3182_);
lean_dec(v___x_3181_);
lean_dec_ref(v_params_3180_);
lean_dec(v_next_3179_);
lean_dec_ref(v_args_3177_);
lean_dec(v_upperBound_3176_);
lean_dec(v_val_3174_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v___x_3194_, lean_object* v_preDefs_3195_, lean_object* v_val_3196_, lean_object* v_upperBound_3197_, lean_object* v_inst_3198_, lean_object* v_R_3199_, lean_object* v_a_3200_, lean_object* v_b_3201_, lean_object* v_c_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3194_, v_preDefs_3195_, v_val_3196_, v_upperBound_3197_, v_a_3200_, v_b_3201_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v___x_3209_, lean_object* v_preDefs_3210_, lean_object* v_val_3211_, lean_object* v_upperBound_3212_, lean_object* v_inst_3213_, lean_object* v_R_3214_, lean_object* v_a_3215_, lean_object* v_b_3216_, lean_object* v_c_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3209_, v_preDefs_3210_, v_val_3211_, v_upperBound_3212_, v_inst_3213_, v_R_3214_, v_a_3215_, v_b_3216_, v_c_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v_upperBound_3212_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3224_, lean_object* v___x_3225_, lean_object* v_pre_3226_, lean_object* v_post_3227_, uint8_t v_usedLetOnly_3228_, uint8_t v_skipConstInApp_3229_, uint8_t v_skipInstances_3230_, lean_object* v___x_3231_, lean_object* v_inst_3232_, lean_object* v_R_3233_, lean_object* v_a_3234_, lean_object* v_b_3235_, lean_object* v_c_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3224_, v___x_3225_, v_pre_3226_, v_post_3227_, v_usedLetOnly_3228_, v_skipConstInApp_3229_, v_skipInstances_3230_, v_a_3234_, v_b_3235_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3244_ = _args[0];
lean_object* v___x_3245_ = _args[1];
lean_object* v_pre_3246_ = _args[2];
lean_object* v_post_3247_ = _args[3];
lean_object* v_usedLetOnly_3248_ = _args[4];
lean_object* v_skipConstInApp_3249_ = _args[5];
lean_object* v_skipInstances_3250_ = _args[6];
lean_object* v___x_3251_ = _args[7];
lean_object* v_inst_3252_ = _args[8];
lean_object* v_R_3253_ = _args[9];
lean_object* v_a_3254_ = _args[10];
lean_object* v_b_3255_ = _args[11];
lean_object* v_c_3256_ = _args[12];
lean_object* v___y_3257_ = _args[13];
lean_object* v___y_3258_ = _args[14];
lean_object* v___y_3259_ = _args[15];
lean_object* v___y_3260_ = _args[16];
lean_object* v___y_3261_ = _args[17];
lean_object* v___y_3262_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3263_; uint8_t v_skipConstInApp_boxed_3264_; uint8_t v_skipInstances_boxed_3265_; lean_object* v_res_3266_; 
v_usedLetOnly_boxed_3263_ = lean_unbox(v_usedLetOnly_3248_);
v_skipConstInApp_boxed_3264_ = lean_unbox(v_skipConstInApp_3249_);
v_skipInstances_boxed_3265_ = lean_unbox(v_skipInstances_3250_);
v_res_3266_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3244_, v___x_3245_, v_pre_3246_, v_post_3247_, v_usedLetOnly_boxed_3263_, v_skipConstInApp_boxed_3264_, v_skipInstances_boxed_3265_, v___x_3251_, v_inst_3252_, v_R_3253_, v_a_3254_, v_b_3255_, v_c_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec(v___x_3251_);
lean_dec_ref(v___x_3245_);
lean_dec(v_upperBound_3244_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3267_, lean_object* v_m_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3268_, v_a_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3271_, lean_object* v_m_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3271_, v_m_3272_, v_a_3273_);
lean_dec_ref(v_a_3273_);
lean_dec_ref(v_m_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3275_, lean_object* v_name_3276_, uint8_t v_bi_3277_, lean_object* v_type_3278_, lean_object* v_k_3279_, uint8_t v_kind_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3276_, v_bi_3277_, v_type_3278_, v_k_3279_, v_kind_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3288_, lean_object* v_name_3289_, lean_object* v_bi_3290_, lean_object* v_type_3291_, lean_object* v_k_3292_, lean_object* v_kind_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
uint8_t v_bi_boxed_3300_; uint8_t v_kind_boxed_3301_; lean_object* v_res_3302_; 
v_bi_boxed_3300_ = lean_unbox(v_bi_3290_);
v_kind_boxed_3301_ = lean_unbox(v_kind_3293_);
v_res_3302_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3288_, v_name_3289_, v_bi_boxed_3300_, v_type_3291_, v_k_3292_, v_kind_boxed_3301_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3303_, lean_object* v_name_3304_, lean_object* v_type_3305_, lean_object* v_val_3306_, lean_object* v_k_3307_, uint8_t v_nondep_3308_, uint8_t v_kind_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3304_, v_type_3305_, v_val_3306_, v_k_3307_, v_nondep_3308_, v_kind_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3317_, lean_object* v_name_3318_, lean_object* v_type_3319_, lean_object* v_val_3320_, lean_object* v_k_3321_, lean_object* v_nondep_3322_, lean_object* v_kind_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v_nondep_boxed_3330_; uint8_t v_kind_boxed_3331_; lean_object* v_res_3332_; 
v_nondep_boxed_3330_ = lean_unbox(v_nondep_3322_);
v_kind_boxed_3331_ = lean_unbox(v_kind_3323_);
v_res_3332_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3317_, v_name_3318_, v_type_3319_, v_val_3320_, v_k_3321_, v_nondep_boxed_3330_, v_kind_boxed_3331_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3333_, lean_object* v_ref_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3334_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3341_, lean_object* v_ref_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3341_, v_ref_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3349_, lean_object* v_x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3358_, lean_object* v_x_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3358_, v_x_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3367_, lean_object* v_m_3368_, lean_object* v_a_3369_, lean_object* v_b_3370_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3368_, v_a_3369_, v_b_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3372_, lean_object* v_a_3373_, lean_object* v_x_3374_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3373_, v_x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3376_, lean_object* v_a_3377_, lean_object* v_x_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3376_, v_a_3377_, v_x_3378_);
lean_dec(v_x_3378_);
lean_dec_ref(v_a_3377_);
return v_res_3379_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3380_, lean_object* v_a_3381_, lean_object* v_x_3382_){
_start:
{
uint8_t v___x_3383_; 
v___x_3383_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3381_, v_x_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3384_, lean_object* v_a_3385_, lean_object* v_x_3386_){
_start:
{
uint8_t v_res_3387_; lean_object* v_r_3388_; 
v_res_3387_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3384_, v_a_3385_, v_x_3386_);
lean_dec(v_x_3386_);
lean_dec_ref(v_a_3385_);
v_r_3388_ = lean_box(v_res_3387_);
return v_r_3388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3389_, lean_object* v_data_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3392_, lean_object* v_a_3393_, lean_object* v_b_3394_, lean_object* v_x_3395_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3393_, v_b_3394_, v_x_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3397_, lean_object* v_i_3398_, lean_object* v_source_3399_, lean_object* v_target_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3398_, v_source_3399_, v_target_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3402_, lean_object* v_x_3403_, lean_object* v_x_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3403_, v_x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3419_, lean_object* v_x_3420_){
_start:
{
if (lean_obj_tag(v_x_3419_) == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3421_;
}
else
{
lean_object* v_val_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3433_; 
v_val_3422_ = lean_ctor_get(v_x_3419_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_x_3419_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3424_ = v_x_3419_;
v_isShared_3425_ = v_isSharedCheck_3433_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_val_3422_);
lean_dec(v_x_3419_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3433_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3429_; 
v___x_3426_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3427_ = l_Nat_reprFast(v_val_3422_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set_tag(v___x_3424_, 3);
lean_ctor_set(v___x_3424_, 0, v___x_3427_);
v___x_3429_ = v___x_3424_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3426_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Repr_addAppParen(v___x_3430_, v_x_3420_);
return v___x_3431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3434_, lean_object* v_x_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3434_, v_x_3435_);
lean_dec(v_x_3435_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3437_, lean_object* v_x_3438_, lean_object* v_x_3439_){
_start:
{
if (lean_obj_tag(v_x_3439_) == 0)
{
lean_dec(v_x_3437_);
return v_x_3438_;
}
else
{
lean_object* v_head_3440_; lean_object* v_tail_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3452_; 
v_head_3440_ = lean_ctor_get(v_x_3439_, 0);
v_tail_3441_ = lean_ctor_get(v_x_3439_, 1);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_x_3439_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3443_ = v_x_3439_;
v_isShared_3444_ = v_isSharedCheck_3452_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_tail_3441_);
lean_inc(v_head_3440_);
lean_dec(v_x_3439_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3452_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
lean_inc(v_x_3437_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set_tag(v___x_3443_, 5);
lean_ctor_set(v___x_3443_, 1, v_x_3437_);
lean_ctor_set(v___x_3443_, 0, v_x_3438_);
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_x_3438_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_x_3437_);
v___x_3446_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3440_, v___x_3447_);
v___x_3449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3446_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v_x_3438_ = v___x_3449_;
v_x_3439_ = v_tail_3441_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3453_, lean_object* v_x_3454_, lean_object* v_x_3455_){
_start:
{
if (lean_obj_tag(v_x_3455_) == 0)
{
lean_dec(v_x_3453_);
return v_x_3454_;
}
else
{
lean_object* v_head_3456_; lean_object* v_tail_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3468_; 
v_head_3456_ = lean_ctor_get(v_x_3455_, 0);
v_tail_3457_ = lean_ctor_get(v_x_3455_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_x_3455_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3459_ = v_x_3455_;
v_isShared_3460_ = v_isSharedCheck_3468_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_tail_3457_);
lean_inc(v_head_3456_);
lean_dec(v_x_3455_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3468_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
lean_inc(v_x_3453_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 5);
lean_ctor_set(v___x_3459_, 1, v_x_3453_);
lean_ctor_set(v___x_3459_, 0, v_x_3454_);
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_x_3454_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_x_3453_);
v___x_3462_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3463_ = lean_unsigned_to_nat(0u);
v___x_3464_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3456_, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3462_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3453_, v___x_3465_, v_tail_3457_);
return v___x_3466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = lean_unsigned_to_nat(0u);
v___x_3471_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3469_, v___x_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3472_, lean_object* v_x_3473_){
_start:
{
if (lean_obj_tag(v_x_3472_) == 0)
{
lean_object* v___x_3474_; 
lean_dec(v_x_3473_);
v___x_3474_ = lean_box(0);
return v___x_3474_;
}
else
{
lean_object* v_tail_3475_; 
v_tail_3475_ = lean_ctor_get(v_x_3472_, 1);
if (lean_obj_tag(v_tail_3475_) == 0)
{
lean_object* v_head_3476_; lean_object* v___x_3477_; 
lean_dec(v_x_3473_);
v_head_3476_ = lean_ctor_get(v_x_3472_, 0);
lean_inc(v_head_3476_);
lean_dec_ref_known(v_x_3472_, 2);
v___x_3477_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3476_);
return v___x_3477_;
}
else
{
lean_object* v_head_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_inc(v_tail_3475_);
v_head_3478_ = lean_ctor_get(v_x_3472_, 0);
lean_inc(v_head_3478_);
lean_dec_ref_known(v_x_3472_, 2);
v___x_3479_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3478_);
v___x_3480_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3473_, v___x_3479_, v_tail_3475_);
return v___x_3480_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3489_ = lean_string_length(v___x_3488_);
return v___x_3489_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3491_ = lean_nat_to_int(v___x_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3497_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3498_ = lean_array_get_size(v_xs_3497_);
v___x_3499_ = lean_unsigned_to_nat(0u);
v___x_3500_ = lean_nat_dec_eq(v___x_3498_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3501_ = lean_array_to_list(v_xs_3497_);
v___x_3502_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3503_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3501_, v___x_3502_);
v___x_3504_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3505_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
lean_ctor_set(v___x_3506_, 1, v___x_3503_);
v___x_3507_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3506_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v___x_3509_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3504_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
v___x_3510_ = l_Std_Format_fill(v___x_3509_);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; 
lean_dec_ref(v_xs_3497_);
v___x_3511_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3512_, lean_object* v_x_3513_, lean_object* v_x_3514_){
_start:
{
if (lean_obj_tag(v_x_3514_) == 0)
{
lean_dec(v_x_3512_);
return v_x_3513_;
}
else
{
lean_object* v_head_3515_; lean_object* v_tail_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3526_; 
v_head_3515_ = lean_ctor_get(v_x_3514_, 0);
v_tail_3516_ = lean_ctor_get(v_x_3514_, 1);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_x_3514_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3518_ = v_x_3514_;
v_isShared_3519_ = v_isSharedCheck_3526_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_tail_3516_);
lean_inc(v_head_3515_);
lean_dec(v_x_3514_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3526_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
lean_inc(v_x_3512_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set_tag(v___x_3518_, 5);
lean_ctor_set(v___x_3518_, 1, v_x_3512_);
lean_ctor_set(v___x_3518_, 0, v_x_3513_);
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_x_3513_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_x_3512_);
v___x_3521_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3515_);
v___x_3523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3521_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v_x_3513_ = v___x_3523_;
v_x_3514_ = v_tail_3516_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3527_, lean_object* v_x_3528_){
_start:
{
if (lean_obj_tag(v_x_3527_) == 0)
{
lean_object* v___x_3529_; 
lean_dec(v_x_3528_);
v___x_3529_ = lean_box(0);
return v___x_3529_;
}
else
{
lean_object* v_tail_3530_; 
v_tail_3530_ = lean_ctor_get(v_x_3527_, 1);
if (lean_obj_tag(v_tail_3530_) == 0)
{
lean_object* v_head_3531_; lean_object* v___x_3532_; 
lean_dec(v_x_3528_);
v_head_3531_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_head_3531_);
lean_dec_ref_known(v_x_3527_, 2);
v___x_3532_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3531_);
return v___x_3532_;
}
else
{
lean_object* v_head_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_inc(v_tail_3530_);
v_head_3533_ = lean_ctor_get(v_x_3527_, 0);
lean_inc(v_head_3533_);
lean_dec_ref_known(v_x_3527_, 2);
v___x_3534_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3533_);
v___x_3535_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3528_, v___x_3534_, v_tail_3530_);
return v___x_3535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3536_){
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
v___x_3542_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3540_, v___x_3541_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3551_, lean_object* v_x_3552_, lean_object* v_x_3553_){
_start:
{
if (lean_obj_tag(v_x_3553_) == 0)
{
lean_dec(v_x_3551_);
return v_x_3552_;
}
else
{
lean_object* v_head_3554_; lean_object* v_tail_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3566_; 
v_head_3554_ = lean_ctor_get(v_x_3553_, 0);
v_tail_3555_ = lean_ctor_get(v_x_3553_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_x_3553_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3557_ = v_x_3553_;
v_isShared_3558_ = v_isSharedCheck_3566_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_tail_3555_);
lean_inc(v_head_3554_);
lean_dec(v_x_3553_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3566_;
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
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_x_3552_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_x_3551_);
v___x_3560_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = l_Nat_reprFast(v_head_3554_);
v___x_3562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
v___x_3563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3560_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v_x_3552_ = v___x_3563_;
v_x_3553_ = v_tail_3555_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3567_, lean_object* v_x_3568_, lean_object* v_x_3569_){
_start:
{
if (lean_obj_tag(v_x_3569_) == 0)
{
lean_dec(v_x_3567_);
return v_x_3568_;
}
else
{
lean_object* v_head_3570_; lean_object* v_tail_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3582_; 
v_head_3570_ = lean_ctor_get(v_x_3569_, 0);
v_tail_3571_ = lean_ctor_get(v_x_3569_, 1);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_x_3569_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3573_ = v_x_3569_;
v_isShared_3574_ = v_isSharedCheck_3582_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_tail_3571_);
lean_inc(v_head_3570_);
lean_dec(v_x_3569_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3582_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
lean_inc(v_x_3567_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set_tag(v___x_3573_, 5);
lean_ctor_set(v___x_3573_, 1, v_x_3567_);
lean_ctor_set(v___x_3573_, 0, v_x_3568_);
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_x_3568_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_x_3567_);
v___x_3576_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3577_ = l_Nat_reprFast(v_head_3570_);
v___x_3578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
v___x_3579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3576_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3567_, v___x_3579_, v_tail_3571_);
return v___x_3580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3583_){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = l_Nat_reprFast(v___y_3583_);
v___x_3585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
if (lean_obj_tag(v_x_3586_) == 0)
{
lean_object* v___x_3588_; 
lean_dec(v_x_3587_);
v___x_3588_ = lean_box(0);
return v___x_3588_;
}
else
{
lean_object* v_tail_3589_; 
v_tail_3589_ = lean_ctor_get(v_x_3586_, 1);
if (lean_obj_tag(v_tail_3589_) == 0)
{
lean_object* v_head_3590_; lean_object* v___x_3591_; 
lean_dec(v_x_3587_);
v_head_3590_ = lean_ctor_get(v_x_3586_, 0);
lean_inc(v_head_3590_);
lean_dec_ref_known(v_x_3586_, 2);
v___x_3591_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3590_);
return v___x_3591_;
}
else
{
lean_object* v_head_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
lean_inc(v_tail_3589_);
v_head_3592_ = lean_ctor_get(v_x_3586_, 0);
lean_inc(v_head_3592_);
lean_dec_ref_known(v_x_3586_, 2);
v___x_3593_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3592_);
v___x_3594_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3587_, v___x_3593_, v_tail_3589_);
return v___x_3594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3595_){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3596_ = lean_array_get_size(v_xs_3595_);
v___x_3597_ = lean_unsigned_to_nat(0u);
v___x_3598_ = lean_nat_dec_eq(v___x_3596_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3599_ = lean_array_to_list(v_xs_3595_);
v___x_3600_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3601_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3599_, v___x_3600_);
v___x_3602_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3603_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
lean_ctor_set(v___x_3604_, 1, v___x_3601_);
v___x_3605_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3602_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Std_Format_fill(v___x_3607_);
return v___x_3608_;
}
else
{
lean_object* v___x_3609_; 
lean_dec_ref(v_xs_3595_);
v___x_3609_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3609_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3610_, lean_object* v_x_3611_, lean_object* v_x_3612_){
_start:
{
if (lean_obj_tag(v_x_3612_) == 0)
{
lean_dec(v_x_3610_);
return v_x_3611_;
}
else
{
lean_object* v_head_3613_; lean_object* v_tail_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3624_; 
v_head_3613_ = lean_ctor_get(v_x_3612_, 0);
v_tail_3614_ = lean_ctor_get(v_x_3612_, 1);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_x_3612_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3616_ = v_x_3612_;
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_tail_3614_);
lean_inc(v_head_3613_);
lean_dec(v_x_3612_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3624_;
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
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_x_3611_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_x_3610_);
v___x_3619_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3613_);
v___x_3621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3619_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v_x_3611_ = v___x_3621_;
v_x_3612_ = v_tail_3614_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3625_, lean_object* v_x_3626_){
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
v___x_3630_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3629_);
return v___x_3630_;
}
else
{
lean_object* v_head_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_inc(v_tail_3628_);
v_head_3631_ = lean_ctor_get(v_x_3625_, 0);
lean_inc(v_head_3631_);
lean_dec_ref_known(v_x_3625_, 2);
v___x_3632_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3631_);
v___x_3633_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3626_, v___x_3632_, v_tail_3628_);
return v___x_3633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3634_){
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
v___x_3640_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3638_, v___x_3639_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_){
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
v___x_3659_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3652_);
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3664_, lean_object* v_x_3665_){
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
v___x_3669_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3668_);
return v___x_3669_;
}
else
{
lean_object* v_head_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_inc(v_tail_3667_);
v_head_3670_ = lean_ctor_get(v_x_3664_, 0);
lean_inc(v_head_3670_);
lean_dec_ref_known(v_x_3664_, 2);
v___x_3671_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3670_);
v___x_3672_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3665_, v___x_3671_, v_tail_3667_);
return v___x_3672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3673_){
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
v___x_3679_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3677_, v___x_3678_);
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
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = lean_unsigned_to_nat(12u);
v___x_3702_ = lean_nat_to_int(v___x_3701_);
return v___x_3702_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = lean_unsigned_to_nat(9u);
v___x_3707_ = lean_nat_to_int(v___x_3706_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = lean_unsigned_to_nat(11u);
v___x_3712_ = lean_nat_to_int(v___x_3711_);
return v___x_3712_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3715_ = lean_string_length(v___x_3714_);
return v___x_3715_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3717_ = lean_nat_to_int(v___x_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3722_){
_start:
{
lean_object* v_numFixed_3723_; lean_object* v_perms_3724_; lean_object* v_revDeps_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_numFixed_3723_ = lean_ctor_get(v_x_3722_, 0);
lean_inc(v_numFixed_3723_);
v_perms_3724_ = lean_ctor_get(v_x_3722_, 1);
lean_inc_ref(v_perms_3724_);
v_revDeps_3725_ = lean_ctor_get(v_x_3722_, 2);
lean_inc_ref(v_revDeps_3725_);
lean_dec_ref(v_x_3722_);
v___x_3726_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3727_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3728_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3729_ = l_Nat_reprFast(v_numFixed_3723_);
v___x_3730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3728_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = 0;
v___x_3733_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set_uint8(v___x_3733_, sizeof(void*)*1, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3727_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_box(1);
v___x_3738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3738_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
lean_ctor_set(v___x_3741_, 1, v___x_3726_);
v___x_3742_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3743_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3724_);
v___x_3744_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
lean_ctor_set_uint8(v___x_3745_, sizeof(void*)*1, v___x_3732_);
v___x_3746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3741_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set(v___x_3747_, 1, v___x_3735_);
v___x_3748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
lean_ctor_set(v___x_3748_, 1, v___x_3737_);
v___x_3749_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v___x_3726_);
v___x_3752_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3753_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3725_);
v___x_3754_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
v___x_3755_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
lean_ctor_set_uint8(v___x_3755_, sizeof(void*)*1, v___x_3732_);
v___x_3756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3751_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3758_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set(v___x_3759_, 1, v___x_3756_);
v___x_3760_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3757_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
lean_ctor_set_uint8(v___x_3763_, sizeof(void*)*1, v___x_3732_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3764_, lean_object* v_prec_3765_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3764_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3767_, lean_object* v_prec_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3767_, v_prec_3768_);
lean_dec(v_prec_3768_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___f_3778_; lean_object* v___x_5728__overap_3779_; lean_object* v___x_3780_; 
v___f_3778_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5728__overap_3779_ = lean_panic_fn_borrowed(v___f_3778_, v_msg_3772_);
lean_inc(v___y_3776_);
lean_inc_ref(v___y_3775_);
lean_inc(v___y_3774_);
lean_inc_ref(v___y_3773_);
v___x_3780_ = lean_apply_5(v___x_5728__overap_3779_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, lean_box(0));
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___f_3794_; lean_object* v___x_5738__overap_3795_; lean_object* v___x_3796_; 
v___f_3794_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5738__overap_3795_ = lean_panic_fn_borrowed(v___f_3794_, v_msg_3788_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
v___x_3796_ = lean_apply_5(v___x_5738__overap_3795_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, lean_box(0));
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___f_3810_; lean_object* v___x_5748__overap_3811_; lean_object* v___x_3812_; 
v___f_3810_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5748__overap_3811_ = lean_panic_fn_borrowed(v___f_3810_, v_msg_3804_);
lean_inc(v___y_3808_);
lean_inc_ref(v___y_3807_);
lean_inc(v___y_3806_);
lean_inc_ref(v___y_3805_);
v___x_3812_ = lean_apply_5(v___x_5748__overap_3811_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, lean_box(0));
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
return v_res_3819_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3823_ = lean_unsigned_to_nat(12u);
v___x_3824_ = lean_unsigned_to_nat(294u);
v___x_3825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3826_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3827_ = l_mkPanicMessageWithDecl(v___x_3826_, v___x_3825_, v___x_3824_, v___x_3823_, v___x_3822_);
return v___x_3827_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3830_ = lean_unsigned_to_nat(12u);
v___x_3831_ = lean_unsigned_to_nat(297u);
v___x_3832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3833_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3834_ = l_mkPanicMessageWithDecl(v___x_3833_, v___x_3832_, v___x_3831_, v___x_3830_, v___x_3829_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3835_, lean_object* v_as_3836_, size_t v_sz_3837_, size_t v_i_3838_, lean_object* v_b_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v_a_3846_; uint8_t v___x_3850_; 
v___x_3850_ = lean_usize_dec_lt(v_i_3838_, v_sz_3837_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; 
v___x_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3851_, 0, v_b_3839_);
return v___x_3851_;
}
else
{
lean_object* v_a_3852_; 
v_a_3852_ = lean_array_uget_borrowed(v_as_3836_, v_i_3838_);
if (lean_obj_tag(v_a_3852_) == 1)
{
lean_object* v_val_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_val_3853_ = lean_ctor_get(v_a_3852_, 0);
v___x_3854_ = lean_box(0);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = lean_array_get_borrowed(v___x_3854_, v_val_3853_, v___x_3855_);
if (lean_obj_tag(v___x_3856_) == 1)
{
lean_object* v_val_3857_; lean_object* v___x_3858_; 
v_val_3857_ = lean_ctor_get(v___x_3856_, 0);
v___x_3858_ = lean_array_get_borrowed(v___x_3854_, v___x_3835_, v_val_3857_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_dec_ref(v_b_3839_);
v___x_3859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3860_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3859_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3870_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3870_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3870_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
if (lean_obj_tag(v_a_3861_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; 
v_a_3865_ = lean_ctor_get(v_a_3861_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v_a_3861_, 1);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v_a_3865_);
v___x_3867_ = v___x_3863_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
else
{
lean_object* v_a_3869_; 
lean_del_object(v___x_3863_);
v_a_3869_ = lean_ctor_get(v_a_3861_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v_a_3861_, 1);
v_a_3846_ = v_a_3869_;
goto v___jp_3845_;
}
}
}
else
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
v_a_3871_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3873_ = v___x_3860_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3860_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
else
{
lean_object* v___x_3879_; 
lean_inc_ref(v___x_3858_);
v___x_3879_ = lean_array_push(v_b_3839_, v___x_3858_);
v_a_3846_ = v___x_3879_;
goto v___jp_3845_;
}
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3881_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3880_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_dec_ref_known(v___x_3881_, 1);
v_a_3846_ = v_b_3839_;
goto v___jp_3845_;
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec_ref(v_b_3839_);
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_box(0);
v___x_3891_ = lean_array_push(v_b_3839_, v___x_3890_);
v_a_3846_ = v___x_3891_;
goto v___jp_3845_;
}
}
v___jp_3845_:
{
size_t v___x_3847_; size_t v___x_3848_; 
v___x_3847_ = ((size_t)1ULL);
v___x_3848_ = lean_usize_add(v_i_3838_, v___x_3847_);
v_i_3838_ = v___x_3848_;
v_b_3839_ = v_a_3846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3892_, lean_object* v_as_3893_, lean_object* v_sz_3894_, lean_object* v_i_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
size_t v_sz_boxed_3902_; size_t v_i_boxed_3903_; lean_object* v_res_3904_; 
v_sz_boxed_3902_ = lean_unbox_usize(v_sz_3894_);
lean_dec(v_sz_3894_);
v_i_boxed_3903_ = lean_unbox_usize(v_i_3895_);
lean_dec(v_i_3895_);
v_res_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3892_, v_as_3893_, v_sz_boxed_3902_, v_i_boxed_3903_, v_b_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_as_3893_);
lean_dec_ref(v___x_3892_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3907_, lean_object* v___x_3908_, lean_object* v___x_3909_, lean_object* v_a_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
uint8_t v___x_3917_; 
v___x_3917_ = lean_nat_dec_lt(v_a_3910_, v_upperBound_3907_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; 
lean_dec(v_a_3910_);
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v_b_3911_);
return v___x_3918_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; size_t v_sz_3921_; size_t v___x_3922_; lean_object* v___x_3923_; 
v___x_3919_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3920_ = lean_array_fget_borrowed(v___x_3908_, v_a_3910_);
v_sz_3921_ = lean_array_size(v___x_3920_);
v___x_3922_ = ((size_t)0ULL);
v___x_3923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3909_, v___x_3920_, v_sz_3921_, v___x_3922_, v___x_3919_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3925_ = lean_array_push(v_b_3911_, v_a_3924_);
v___x_3926_ = lean_unsigned_to_nat(1u);
v___x_3927_ = lean_nat_add(v_a_3910_, v___x_3926_);
lean_dec(v_a_3910_);
v_a_3910_ = v___x_3927_;
v_b_3911_ = v___x_3925_;
goto _start;
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec_ref(v_b_3911_);
lean_dec(v_a_3910_);
v_a_3929_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3923_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3923_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3937_, lean_object* v___x_3938_, lean_object* v___x_3939_, lean_object* v_a_3940_, lean_object* v_b_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3937_, v___x_3938_, v___x_3939_, v_a_3940_, v_b_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec_ref(v___x_3939_);
lean_dec_ref(v___x_3938_);
lean_dec(v_upperBound_3937_);
return v_res_3947_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3949_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3950_ = lean_unsigned_to_nat(8u);
v___x_3951_ = lean_unsigned_to_nat(281u);
v___x_3952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3953_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3954_ = l_mkPanicMessageWithDecl(v___x_3953_, v___x_3952_, v___x_3951_, v___x_3950_, v___x_3949_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3955_, lean_object* v_a_3956_, lean_object* v_b_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v_a_3964_; uint8_t v___x_3968_; 
v___x_3968_ = lean_nat_dec_lt(v_a_3956_, v_upperBound_3955_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_dec(v_a_3956_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v_b_3957_);
return v___x_3969_;
}
else
{
lean_object* v_snd_3970_; lean_object* v_snd_3971_; lean_object* v_snd_3972_; lean_object* v_fst_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_4097_; 
v_snd_3970_ = lean_ctor_get(v_b_3957_, 1);
lean_inc(v_snd_3970_);
v_snd_3971_ = lean_ctor_get(v_snd_3970_, 1);
lean_inc(v_snd_3971_);
v_snd_3972_ = lean_ctor_get(v_snd_3971_, 1);
lean_inc(v_snd_3972_);
v_fst_3973_ = lean_ctor_get(v_b_3957_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_b_3957_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; 
v_unused_4098_ = lean_ctor_get(v_b_3957_, 1);
lean_dec(v_unused_4098_);
v___x_3975_ = v_b_3957_;
v_isShared_3976_ = v_isSharedCheck_4097_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_fst_3973_);
lean_dec(v_b_3957_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_4097_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v_fst_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4095_; 
v_fst_3977_ = lean_ctor_get(v_snd_3970_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_snd_3970_);
if (v_isSharedCheck_4095_ == 0)
{
lean_object* v_unused_4096_; 
v_unused_4096_ = lean_ctor_get(v_snd_3970_, 1);
lean_dec(v_unused_4096_);
v___x_3979_ = v_snd_3970_;
v_isShared_3980_ = v_isSharedCheck_4095_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_fst_3977_);
lean_dec(v_snd_3970_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4095_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v_fst_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4093_; 
v_fst_3981_ = lean_ctor_get(v_snd_3971_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_snd_3971_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v_snd_3971_, 1);
lean_dec(v_unused_4094_);
v___x_3983_ = v_snd_3971_;
v_isShared_3984_ = v_isSharedCheck_4093_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_fst_3981_);
lean_dec(v_snd_3971_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4093_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v_array_3985_; lean_object* v_start_3986_; lean_object* v_stop_3987_; uint8_t v___x_3988_; 
v_array_3985_ = lean_ctor_get(v_snd_3972_, 0);
v_start_3986_ = lean_ctor_get(v_snd_3972_, 1);
v_stop_3987_ = lean_ctor_get(v_snd_3972_, 2);
v___x_3988_ = lean_nat_dec_lt(v_start_3986_, v_stop_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3990_; 
lean_dec(v_a_3956_);
if (v_isShared_3984_ == 0)
{
v___x_3990_ = v___x_3983_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_fst_3981_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_snd_3972_);
v___x_3990_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3992_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 1, v___x_3990_);
v___x_3992_ = v___x_3979_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_fst_3977_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3994_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 1, v___x_3992_);
v___x_3994_ = v___x_3975_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_fst_3973_);
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
lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4089_; 
lean_inc(v_stop_3987_);
lean_inc(v_start_3986_);
lean_inc_ref(v_array_3985_);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_snd_3972_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; lean_object* v_unused_4091_; lean_object* v_unused_4092_; 
v_unused_4090_ = lean_ctor_get(v_snd_3972_, 2);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_snd_3972_, 1);
lean_dec(v_unused_4091_);
v_unused_4092_ = lean_ctor_get(v_snd_3972_, 0);
lean_dec(v_unused_4092_);
v___x_4000_ = v_snd_3972_;
v_isShared_4001_ = v_isSharedCheck_4089_;
goto v_resetjp_3999_;
}
else
{
lean_dec(v_snd_3972_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4089_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v_array_4002_; lean_object* v_start_4003_; lean_object* v_stop_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v_array_4002_ = lean_ctor_get(v_fst_3981_, 0);
v_start_4003_ = lean_ctor_get(v_fst_3981_, 1);
v_stop_4004_ = lean_ctor_get(v_fst_3981_, 2);
v___x_4005_ = lean_array_fget(v_array_3985_, v_start_3986_);
v___x_4006_ = lean_unsigned_to_nat(1u);
v___x_4007_ = lean_nat_add(v_start_3986_, v___x_4006_);
lean_dec(v_start_3986_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 1, v___x_4007_);
v___x_4009_ = v___x_4000_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_array_3985_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v___x_4007_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v_stop_3987_);
v___x_4009_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
uint8_t v___x_4010_; 
v___x_4010_ = lean_nat_dec_lt(v_start_4003_, v_stop_4004_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4012_; 
lean_dec(v___x_4005_);
lean_dec(v_a_3956_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 1, v___x_4009_);
v___x_4012_ = v___x_3983_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_fst_3981_);
lean_ctor_set(v_reuseFailAlloc_4020_, 1, v___x_4009_);
v___x_4012_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4014_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 1, v___x_4012_);
v___x_4014_ = v___x_3979_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_fst_3977_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4016_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 1, v___x_4014_);
v___x_4016_ = v___x_3975_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_fst_3973_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; 
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
}
}
else
{
lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4084_; 
lean_inc(v_stop_4004_);
lean_inc(v_start_4003_);
lean_inc_ref(v_array_4002_);
v_isSharedCheck_4084_ = !lean_is_exclusive(v_fst_3981_);
if (v_isSharedCheck_4084_ == 0)
{
lean_object* v_unused_4085_; lean_object* v_unused_4086_; lean_object* v_unused_4087_; 
v_unused_4085_ = lean_ctor_get(v_fst_3981_, 2);
lean_dec(v_unused_4085_);
v_unused_4086_ = lean_ctor_get(v_fst_3981_, 1);
lean_dec(v_unused_4086_);
v_unused_4087_ = lean_ctor_get(v_fst_3981_, 0);
lean_dec(v_unused_4087_);
v___x_4022_ = v_fst_3981_;
v_isShared_4023_ = v_isSharedCheck_4084_;
goto v_resetjp_4021_;
}
else
{
lean_dec(v_fst_3981_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4084_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4024_ = lean_nat_add(v_start_4003_, v___x_4006_);
lean_dec(v_start_4003_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 1, v___x_4024_);
v___x_4026_ = v___x_4022_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_array_4002_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4024_);
lean_ctor_set(v_reuseFailAlloc_4083_, 2, v_stop_4004_);
v___x_4026_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
if (lean_obj_tag(v___x_4005_) == 1)
{
lean_object* v_val_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4071_; 
v_val_4027_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4029_ = v___x_4005_;
v_isShared_4030_ = v_isSharedCheck_4071_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_val_4027_);
lean_dec(v___x_4005_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4071_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4031_ = lean_box(0);
v___x_4032_ = lean_unsigned_to_nat(0u);
v___x_4033_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4034_ = lean_array_get(v___x_4031_, v_val_4027_, v___x_4032_);
lean_dec(v_val_4027_);
lean_inc(v_a_3956_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v_a_3956_);
v___x_4036_ = v___x_4029_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_3956_);
v___x_4036_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
uint8_t v___x_4037_; 
v___x_4037_ = l_Option_instDecidableEq___redArg(v___x_4033_, v___x_4034_, v___x_4036_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec_ref(v___x_4026_);
lean_dec_ref(v___x_4009_);
lean_del_object(v___x_3983_);
lean_del_object(v___x_3979_);
lean_dec(v_fst_3977_);
lean_del_object(v___x_3975_);
lean_dec(v_fst_3973_);
v___x_4038_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4039_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4038_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4049_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4042_ = v___x_4039_;
v_isShared_4043_ = v_isSharedCheck_4049_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4039_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4049_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
if (lean_obj_tag(v_a_4040_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4046_; 
lean_dec(v_a_3956_);
v_a_4044_ = lean_ctor_get(v_a_4040_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v_a_4040_, 1);
if (v_isShared_4043_ == 0)
{
lean_ctor_set(v___x_4042_, 0, v_a_4044_);
v___x_4046_ = v___x_4042_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4044_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
else
{
lean_object* v_a_4048_; 
lean_del_object(v___x_4042_);
v_a_4048_ = lean_ctor_get(v_a_4040_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v_a_4040_, 1);
v_a_3964_ = v_a_4048_;
goto v___jp_3963_;
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
lean_dec(v_a_3956_);
v_a_4050_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4039_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4039_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
else
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4062_; 
lean_inc(v_fst_3977_);
v___x_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4058_, 0, v_fst_3977_);
v___x_4059_ = lean_array_push(v_fst_3973_, v___x_4058_);
v___x_4060_ = lean_nat_add(v_fst_3977_, v___x_4006_);
lean_dec(v_fst_3977_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 1, v___x_4009_);
lean_ctor_set(v___x_3983_, 0, v___x_4026_);
v___x_4062_ = v___x_3983_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4009_);
v___x_4062_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4064_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 1, v___x_4062_);
lean_ctor_set(v___x_3979_, 0, v___x_4060_);
v___x_4064_ = v___x_3979_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4060_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4066_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 1, v___x_4064_);
lean_ctor_set(v___x_3975_, 0, v___x_4059_);
v___x_4066_ = v___x_3975_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4059_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
v_a_3964_ = v___x_4066_;
goto v___jp_3963_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4075_; 
lean_dec(v___x_4005_);
v___x_4072_ = lean_box(0);
v___x_4073_ = lean_array_push(v_fst_3973_, v___x_4072_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 1, v___x_4009_);
lean_ctor_set(v___x_3983_, 0, v___x_4026_);
v___x_4075_ = v___x_3983_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4009_);
v___x_4075_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4077_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 1, v___x_4075_);
v___x_4077_ = v___x_3979_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_fst_3977_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
lean_object* v___x_4079_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 1, v___x_4077_);
lean_ctor_set(v___x_3975_, 0, v___x_4073_);
v___x_4079_ = v___x_3975_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
v_a_3964_ = v___x_4079_;
goto v___jp_3963_;
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
v___jp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = lean_unsigned_to_nat(1u);
v___x_3966_ = lean_nat_add(v_a_3956_, v___x_3965_);
lean_dec(v_a_3956_);
v_a_3956_ = v___x_3966_;
v_b_3957_ = v_a_3964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4099_, lean_object* v_a_4100_, lean_object* v_b_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4099_, v_a_4100_, v_b_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v_upperBound_4099_);
return v_res_4107_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4109_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4110_ = lean_unsigned_to_nat(4u);
v___x_4111_ = lean_unsigned_to_nat(275u);
v___x_4112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4113_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4114_ = l_mkPanicMessageWithDecl(v___x_4113_, v___x_4112_, v___x_4111_, v___x_4110_, v___x_4109_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4115_, lean_object* v___x_4116_, lean_object* v___x_4117_, lean_object* v_xs_4118_, lean_object* v_x_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_graph_4125_; lean_object* v_revDeps_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4179_; 
v_graph_4125_ = lean_ctor_get(v_a_4115_, 0);
v_revDeps_4126_ = lean_ctor_get(v_a_4115_, 1);
v_isSharedCheck_4179_ = !lean_is_exclusive(v_a_4115_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4128_ = v_a_4115_;
v_isShared_4129_ = v_isSharedCheck_4179_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_revDeps_4126_);
lean_inc(v_graph_4125_);
lean_dec(v_a_4115_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4179_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; 
v___x_4130_ = lean_array_get_borrowed(v___x_4116_, v_graph_4125_, v___x_4117_);
v___x_4131_ = lean_array_get_size(v_xs_4118_);
v___x_4132_ = lean_array_get_size(v___x_4130_);
v___x_4133_ = lean_nat_dec_eq(v___x_4131_, v___x_4132_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_del_object(v___x_4128_);
lean_dec_ref(v_revDeps_4126_);
lean_dec_ref(v_graph_4125_);
lean_dec_ref(v_xs_4118_);
lean_dec(v___x_4117_);
v___x_4134_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4135_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4134_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
return v___x_4135_;
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4136_ = lean_mk_empty_array_with_capacity(v___x_4117_);
lean_inc_n(v___x_4117_, 2);
v___x_4137_ = l_Array_toSubarray___redArg(v_xs_4118_, v___x_4117_, v___x_4131_);
lean_inc(v___x_4130_);
v___x_4138_ = l_Array_toSubarray___redArg(v___x_4130_, v___x_4117_, v___x_4132_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 1, v___x_4138_);
lean_ctor_set(v___x_4128_, 0, v___x_4137_);
v___x_4140_ = v___x_4128_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4137_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
lean_inc(v___x_4117_);
v___x_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4117_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4136_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4131_, v___x_4117_, v___x_4142_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v_snd_4145_; lean_object* v_fst_4146_; lean_object* v_fst_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
v_snd_4145_ = lean_ctor_get(v_a_4144_, 1);
lean_inc(v_snd_4145_);
v_fst_4146_ = lean_ctor_get(v_a_4144_, 0);
lean_inc_n(v_fst_4146_, 2);
lean_dec(v_a_4144_);
v_fst_4147_ = lean_ctor_get(v_snd_4145_, 0);
lean_inc(v_fst_4147_);
lean_dec(v_snd_4145_);
v___x_4148_ = lean_unsigned_to_nat(1u);
v___x_4149_ = lean_array_get_size(v_graph_4125_);
v___x_4150_ = lean_mk_empty_array_with_capacity(v___x_4148_);
v___x_4151_ = lean_array_push(v___x_4150_, v_fst_4146_);
v___x_4152_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4149_, v_graph_4125_, v_fst_4146_, v___x_4148_, v___x_4151_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v_fst_4146_);
lean_dec_ref(v_graph_4125_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4161_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4155_ = v___x_4152_;
v_isShared_4156_ = v_isSharedCheck_4161_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4161_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v___x_4159_; 
v___x_4157_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4157_, 0, v_fst_4147_);
lean_ctor_set(v___x_4157_, 1, v_a_4153_);
lean_ctor_set(v___x_4157_, 2, v_revDeps_4126_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 0, v___x_4157_);
v___x_4159_ = v___x_4155_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4157_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec(v_fst_4147_);
lean_dec_ref(v_revDeps_4126_);
v_a_4162_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4152_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4152_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v_revDeps_4126_);
lean_dec_ref(v_graph_4125_);
v_a_4170_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4143_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4143_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4180_, lean_object* v___x_4181_, lean_object* v___x_4182_, lean_object* v_xs_4183_, lean_object* v_x_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4180_, v___x_4181_, v___x_4182_, v_xs_4183_, v_x_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec_ref(v_x_4184_);
lean_dec_ref(v___x_4181_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v___x_4197_; 
lean_inc_ref(v_preDefs_4191_);
v___x_4197_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v_value_4202_; lean_object* v___x_4203_; lean_object* v___f_4204_; uint8_t v___x_4205_; lean_object* v___x_4206_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
v___x_4199_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4200_ = lean_unsigned_to_nat(0u);
v___x_4201_ = lean_array_get(v___x_4199_, v_preDefs_4191_, v___x_4200_);
lean_dec_ref(v_preDefs_4191_);
v_value_4202_ = lean_ctor_get(v___x_4201_, 7);
lean_inc_ref(v_value_4202_);
lean_dec(v___x_4201_);
v___x_4203_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4204_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4204_, 0, v_a_4198_);
lean_closure_set(v___f_4204_, 1, v___x_4203_);
lean_closure_set(v___f_4204_, 2, v___x_4200_);
v___x_4205_ = 0;
v___x_4206_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4202_, v___f_4204_, v___x_4205_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
return v___x_4206_;
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v_preDefs_4191_);
v_a_4207_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4197_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4197_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4222_, lean_object* v___x_4223_, lean_object* v___x_4224_, lean_object* v_inst_4225_, lean_object* v_R_4226_, lean_object* v_a_4227_, lean_object* v_b_4228_, lean_object* v_c_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4222_, v___x_4223_, v___x_4224_, v_a_4227_, v_b_4228_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4236_, lean_object* v___x_4237_, lean_object* v___x_4238_, lean_object* v_inst_4239_, lean_object* v_R_4240_, lean_object* v_a_4241_, lean_object* v_b_4242_, lean_object* v_c_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4236_, v___x_4237_, v___x_4238_, v_inst_4239_, v_R_4240_, v_a_4241_, v_b_4242_, v_c_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec_ref(v___x_4238_);
lean_dec_ref(v___x_4237_);
lean_dec(v_upperBound_4236_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4250_, lean_object* v_inst_4251_, lean_object* v_R_4252_, lean_object* v_a_4253_, lean_object* v_b_4254_, lean_object* v_c_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4250_, v_a_4253_, v_b_4254_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4262_, lean_object* v_inst_4263_, lean_object* v_R_4264_, lean_object* v_a_4265_, lean_object* v_b_4266_, lean_object* v_c_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4262_, v_inst_4263_, v_R_4264_, v_a_4265_, v_b_4266_, v_c_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v_upperBound_4262_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4274_, size_t v_i_4275_, size_t v_stop_4276_, lean_object* v_b_4277_){
_start:
{
uint8_t v___x_4278_; 
v___x_4278_ = lean_usize_dec_eq(v_i_4275_, v_stop_4276_);
if (v___x_4278_ == 0)
{
size_t v___x_4279_; size_t v___x_4280_; lean_object* v___x_4281_; 
v___x_4279_ = ((size_t)1ULL);
v___x_4280_ = lean_usize_sub(v_i_4275_, v___x_4279_);
v___x_4281_ = lean_array_uget_borrowed(v_as_4274_, v___x_4280_);
if (lean_obj_tag(v___x_4281_) == 0)
{
v_i_4275_ = v___x_4280_;
goto _start;
}
else
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = lean_unsigned_to_nat(1u);
v___x_4284_ = lean_nat_add(v_b_4277_, v___x_4283_);
lean_dec(v_b_4277_);
v_i_4275_ = v___x_4280_;
v_b_4277_ = v___x_4284_;
goto _start;
}
}
else
{
return v_b_4277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4286_, lean_object* v_i_4287_, lean_object* v_stop_4288_, lean_object* v_b_4289_){
_start:
{
size_t v_i_boxed_4290_; size_t v_stop_boxed_4291_; lean_object* v_res_4292_; 
v_i_boxed_4290_ = lean_unbox_usize(v_i_4287_);
lean_dec(v_i_4287_);
v_stop_boxed_4291_ = lean_unbox_usize(v_stop_4288_);
lean_dec(v_stop_4288_);
v_res_4292_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4286_, v_i_boxed_4290_, v_stop_boxed_4291_, v_b_4289_);
lean_dec_ref(v_as_4286_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4293_){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; 
v___x_4294_ = lean_unsigned_to_nat(0u);
v___x_4295_ = lean_array_get_size(v_perm_4293_);
v___x_4296_ = lean_nat_dec_lt(v___x_4294_, v___x_4295_);
if (v___x_4296_ == 0)
{
return v___x_4294_;
}
else
{
size_t v___x_4297_; size_t v___x_4298_; lean_object* v___x_4299_; 
v___x_4297_ = lean_usize_of_nat(v___x_4295_);
v___x_4298_ = ((size_t)0ULL);
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4293_, v___x_4297_, v___x_4298_, v___x_4294_);
return v___x_4299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4300_);
lean_dec_ref(v_perm_4300_);
return v_res_4301_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4302_, lean_object* v_i_4303_){
_start:
{
lean_object* v___x_4304_; uint8_t v___x_4305_; 
v___x_4304_ = lean_array_get_size(v_perm_4302_);
v___x_4305_ = lean_nat_dec_lt(v_i_4303_, v___x_4304_);
if (v___x_4305_ == 0)
{
return v___x_4305_;
}
else
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_array_fget_borrowed(v_perm_4302_, v_i_4303_);
if (lean_obj_tag(v___x_4306_) == 0)
{
uint8_t v___x_4307_; 
v___x_4307_ = 0;
return v___x_4307_;
}
else
{
return v___x_4305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4308_, lean_object* v_i_4309_){
_start:
{
uint8_t v_res_4310_; lean_object* v_r_4311_; 
v_res_4310_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4308_, v_i_4309_);
lean_dec(v_i_4309_);
lean_dec_ref(v_perm_4308_);
v_r_4311_ = lean_box(v_res_4310_);
return v_r_4311_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___f_4318_; lean_object* v___x_907__overap_4319_; lean_object* v___x_4320_; 
v___f_4318_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_907__overap_4319_ = lean_panic_fn_borrowed(v___f_4318_, v_msg_4312_);
lean_inc(v___y_4316_);
lean_inc_ref(v___y_4315_);
lean_inc(v___y_4314_);
lean_inc_ref(v___y_4313_);
v___x_4320_ = lean_apply_5(v___x_907__overap_4319_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, lean_box(0));
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4328_, lean_object* v_msg_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; 
v___x_4335_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4336_, lean_object* v_msg_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4336_, v_msg_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4344_, lean_object* v_maxFVars_x3f_4345_, lean_object* v_k_4346_, uint8_t v_cleanupAnnotations_4347_, uint8_t v_whnfType_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v___f_4354_; lean_object* v___x_4355_; 
v___f_4354_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4354_, 0, v_k_4346_);
v___x_4355_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4344_, v_maxFVars_x3f_4345_, v___f_4354_, v_cleanupAnnotations_4347_, v_whnfType_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4355_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
v_a_4364_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4355_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4355_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4372_, lean_object* v_maxFVars_x3f_4373_, lean_object* v_k_4374_, lean_object* v_cleanupAnnotations_4375_, lean_object* v_whnfType_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4382_; uint8_t v_whnfType_boxed_4383_; lean_object* v_res_4384_; 
v_cleanupAnnotations_boxed_4382_ = lean_unbox(v_cleanupAnnotations_4375_);
v_whnfType_boxed_4383_ = lean_unbox(v_whnfType_4376_);
v_res_4384_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4372_, v_maxFVars_x3f_4373_, v_k_4374_, v_cleanupAnnotations_boxed_4382_, v_whnfType_boxed_4383_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4385_, lean_object* v_type_4386_, lean_object* v_maxFVars_x3f_4387_, lean_object* v_k_4388_, uint8_t v_cleanupAnnotations_4389_, uint8_t v_whnfType_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___x_4396_; 
v___x_4396_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4386_, v_maxFVars_x3f_4387_, v_k_4388_, v_cleanupAnnotations_4389_, v_whnfType_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4397_, lean_object* v_type_4398_, lean_object* v_maxFVars_x3f_4399_, lean_object* v_k_4400_, lean_object* v_cleanupAnnotations_4401_, lean_object* v_whnfType_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4408_; uint8_t v_whnfType_boxed_4409_; lean_object* v_res_4410_; 
v_cleanupAnnotations_boxed_4408_ = lean_unbox(v_cleanupAnnotations_4401_);
v_whnfType_boxed_4409_ = lean_unbox(v_whnfType_4402_);
v_res_4410_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4397_, v_type_4398_, v_maxFVars_x3f_4399_, v_k_4400_, v_cleanupAnnotations_boxed_4408_, v_whnfType_boxed_4409_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
return v_res_4410_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4413_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4414_ = lean_unsigned_to_nat(6u);
v___x_4415_ = lean_unsigned_to_nat(329u);
v___x_4416_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4417_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4418_ = l_mkPanicMessageWithDecl(v___x_4417_, v___x_4416_, v___x_4415_, v___x_4414_, v___x_4413_);
return v___x_4418_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
v___x_4422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4423_ = lean_unsigned_to_nat(8u);
v___x_4424_ = lean_unsigned_to_nat(322u);
v___x_4425_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4426_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4427_ = l_mkPanicMessageWithDecl(v___x_4426_, v___x_4425_, v___x_4424_, v___x_4423_, v___x_4422_);
return v___x_4427_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4429_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4430_ = lean_unsigned_to_nat(8u);
v___x_4431_ = lean_unsigned_to_nat(325u);
v___x_4432_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4433_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4434_ = l_mkPanicMessageWithDecl(v___x_4433_, v___x_4432_, v___x_4431_, v___x_4430_, v___x_4429_);
return v___x_4434_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4436_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4437_ = lean_unsigned_to_nat(8u);
v___x_4438_ = lean_unsigned_to_nat(324u);
v___x_4439_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4440_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4441_ = l_mkPanicMessageWithDecl(v___x_4440_, v___x_4439_, v___x_4438_, v___x_4437_, v___x_4436_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4442_, lean_object* v___x_4443_, lean_object* v_xs_4444_, lean_object* v_val_4445_, lean_object* v_i_4446_, lean_object* v_perm_4447_, lean_object* v_k_4448_, lean_object* v_xs_x27_4449_, lean_object* v_type_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v___x_4456_; uint8_t v___x_4457_; 
v___x_4456_ = lean_array_get_size(v_xs_x27_4449_);
v___x_4457_ = lean_nat_dec_eq(v___x_4456_, v___x_4442_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_dec_ref(v_type_4450_);
lean_dec_ref(v_k_4448_);
lean_dec_ref(v_perm_4447_);
lean_dec_ref(v_xs_4444_);
v___x_4458_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4459_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4458_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
return v___x_4459_;
}
else
{
lean_object* v___x_4460_; lean_object* v_x_4461_; lean_object* v___x_4462_; 
v___x_4460_ = lean_unsigned_to_nat(0u);
v_x_4461_ = lean_array_get_borrowed(v___x_4443_, v_xs_x27_4449_, v___x_4460_);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
lean_inc(v_x_4461_);
v___x_4462_ = lean_infer_type(v_x_4461_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_object* v_a_4463_; uint8_t v___x_4464_; 
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_a_4463_);
lean_dec_ref_known(v___x_4462_, 1);
v___x_4464_ = l_Lean_Expr_hasLooseBVars(v_a_4463_);
lean_dec(v_a_4463_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; uint8_t v___x_4466_; 
v___x_4465_ = lean_array_get_size(v_xs_4444_);
v___x_4466_ = lean_nat_dec_lt(v_val_4445_, v___x_4465_);
if (v___x_4466_ == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref(v_type_4450_);
lean_dec_ref(v_k_4448_);
lean_dec_ref(v_perm_4447_);
lean_dec_ref(v_xs_4444_);
v___x_4467_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4468_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4467_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
return v___x_4468_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = lean_nat_add(v_i_4446_, v___x_4442_);
lean_inc(v_x_4461_);
v___x_4470_ = lean_array_set(v_xs_4444_, v_val_4445_, v_x_4461_);
v___x_4471_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4447_, v_k_4448_, v___x_4469_, v_type_4450_, v___x_4470_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
return v___x_4471_;
}
}
else
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
lean_dec_ref(v_type_4450_);
lean_dec_ref(v_k_4448_);
lean_dec_ref(v_perm_4447_);
lean_dec_ref(v_xs_4444_);
v___x_4472_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4473_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4472_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
return v___x_4473_;
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec_ref(v_type_4450_);
lean_dec_ref(v_k_4448_);
lean_dec_ref(v_perm_4447_);
lean_dec_ref(v_xs_4444_);
v_a_4474_ = lean_ctor_get(v___x_4462_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4462_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4462_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4462_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4482_, lean_object* v___x_4483_, lean_object* v_xs_4484_, lean_object* v_val_4485_, lean_object* v_i_4486_, lean_object* v_perm_4487_, lean_object* v_k_4488_, lean_object* v_xs_x27_4489_, lean_object* v_type_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4482_, v___x_4483_, v_xs_4484_, v_val_4485_, v_i_4486_, v_perm_4487_, v_k_4488_, v_xs_x27_4489_, v_type_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec_ref(v_xs_x27_4489_);
lean_dec(v_i_4486_);
lean_dec(v_val_4485_);
lean_dec_ref(v___x_4483_);
lean_dec(v___x_4482_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4497_, lean_object* v_k_4498_, lean_object* v_i_4499_, lean_object* v_type_4500_, lean_object* v_xs_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4507_ = lean_array_get_size(v_perm_4497_);
v___x_4508_ = lean_nat_dec_lt(v_i_4499_, v___x_4507_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; 
lean_dec_ref(v_type_4500_);
lean_dec(v_i_4499_);
lean_dec_ref(v_perm_4497_);
lean_inc(v_a_4505_);
lean_inc_ref(v_a_4504_);
lean_inc(v_a_4503_);
lean_inc_ref(v_a_4502_);
v___x_4509_ = lean_apply_6(v_k_4498_, v_xs_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, lean_box(0));
return v___x_4509_;
}
else
{
lean_object* v___x_4510_; 
v___x_4510_ = lean_array_fget_borrowed(v_perm_4497_, v_i_4499_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v___x_4511_; 
lean_inc(v_a_4505_);
lean_inc_ref(v_a_4504_);
lean_inc(v_a_4503_);
lean_inc_ref(v_a_4502_);
v___x_4511_ = lean_whnf(v_type_4500_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; uint8_t v___x_4513_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref_known(v___x_4511_, 1);
v___x_4513_ = l_Lean_Expr_isForall(v_a_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; 
lean_dec(v_a_4512_);
lean_dec_ref(v_xs_4501_);
lean_dec(v_i_4499_);
lean_dec_ref(v_k_4498_);
lean_dec_ref(v_perm_4497_);
v___x_4514_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4515_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4514_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
return v___x_4515_;
}
else
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4516_ = lean_unsigned_to_nat(1u);
v___x_4517_ = lean_nat_add(v_i_4499_, v___x_4516_);
lean_dec(v_i_4499_);
v___x_4518_ = l_Lean_Expr_bindingBody_x21(v_a_4512_);
lean_dec(v_a_4512_);
v_i_4499_ = v___x_4517_;
v_type_4500_ = v___x_4518_;
goto _start;
}
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
lean_dec_ref(v_xs_4501_);
lean_dec(v_i_4499_);
lean_dec_ref(v_k_4498_);
lean_dec_ref(v_perm_4497_);
v_a_4520_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4511_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4511_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
else
{
lean_object* v_val_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___f_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; lean_object* v___x_4534_; 
v_val_4528_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_val_4528_);
v___x_4529_ = l_Lean_instInhabitedExpr;
v___x_4530_ = lean_unsigned_to_nat(1u);
v___f_4531_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4531_, 0, v___x_4530_);
lean_closure_set(v___f_4531_, 1, v___x_4529_);
lean_closure_set(v___f_4531_, 2, v_xs_4501_);
lean_closure_set(v___f_4531_, 3, v_val_4528_);
lean_closure_set(v___f_4531_, 4, v_i_4499_);
lean_closure_set(v___f_4531_, 5, v_perm_4497_);
lean_closure_set(v___f_4531_, 6, v_k_4498_);
v___x_4532_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4533_ = 0;
v___x_4534_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4500_, v___x_4532_, v___f_4531_, v___x_4508_, v___x_4533_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
return v___x_4534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4535_, lean_object* v_k_4536_, lean_object* v_i_4537_, lean_object* v_type_4538_, lean_object* v_xs_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4535_, v_k_4536_, v_i_4537_, v_type_4538_, v_xs_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4546_, lean_object* v_perm_4547_, lean_object* v_k_4548_, lean_object* v_i_4549_, lean_object* v_type_4550_, lean_object* v_xs_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_){
_start:
{
lean_object* v___x_4557_; 
v___x_4557_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4547_, v_k_4548_, v_i_4549_, v_type_4550_, v_xs_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4558_, lean_object* v_perm_4559_, lean_object* v_k_4560_, lean_object* v_i_4561_, lean_object* v_type_4562_, lean_object* v_xs_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4558_, v_perm_4559_, v_k_4560_, v_i_4561_, v_type_4562_, v_xs_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
return v_res_4569_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = lean_unsigned_to_nat(0u);
v___x_4571_ = l_Lean_Level_ofNat(v___x_4570_);
return v___x_4571_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4572_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4573_ = l_Lean_mkSort(v___x_4572_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4574_, lean_object* v_type_4575_, lean_object* v_k_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4582_ = lean_unsigned_to_nat(0u);
v___x_4583_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4574_);
v___x_4584_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4585_ = lean_mk_array(v___x_4583_, v___x_4584_);
v___x_4586_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4574_, v_k_4576_, v___x_4582_, v_type_4575_, v___x_4585_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4587_, lean_object* v_type_4588_, lean_object* v_k_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4587_, v_type_4588_, v_k_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4596_, lean_object* v_perm_4597_, lean_object* v_type_4598_, lean_object* v_k_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4597_, v_type_4598_, v_k_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4606_, lean_object* v_perm_4607_, lean_object* v_type_4608_, lean_object* v_k_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4606_, v_perm_4607_, v_type_4608_, v_k_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_);
lean_dec(v_a_4613_);
lean_dec_ref(v_a_4612_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4610_);
return v_res_4615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4616_, lean_object* v_runInBase_4617_, lean_object* v_b_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4624_ = lean_apply_1(v_k_4616_, v_b_4618_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
v___x_4625_ = lean_apply_7(v_runInBase_4617_, lean_box(0), v___x_4624_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, lean_box(0));
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4626_, lean_object* v_runInBase_4627_, lean_object* v_b_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4626_, v_runInBase_4627_, v_b_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4635_, lean_object* v_perm_4636_, lean_object* v_type_4637_, lean_object* v_runInBase_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v___f_4644_; lean_object* v___x_4645_; 
v___f_4644_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4644_, 0, v_k_4635_);
lean_closure_set(v___f_4644_, 1, v_runInBase_4638_);
v___x_4645_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4636_, v_type_4637_, v___f_4644_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4646_, lean_object* v_perm_4647_, lean_object* v_type_4648_, lean_object* v_runInBase_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4646_, v_perm_4647_, v_type_4648_, v_runInBase_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4656_, lean_object* v_inst_4657_, lean_object* v_perm_4658_, lean_object* v_type_4659_, lean_object* v_k_4660_){
_start:
{
lean_object* v_toBind_4661_; lean_object* v_liftWith_4662_; lean_object* v_restoreM_4663_; lean_object* v___f_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v_toBind_4661_ = lean_ctor_get(v_inst_4657_, 1);
lean_inc(v_toBind_4661_);
lean_dec_ref(v_inst_4657_);
v_liftWith_4662_ = lean_ctor_get(v_inst_4656_, 0);
lean_inc(v_liftWith_4662_);
v_restoreM_4663_ = lean_ctor_get(v_inst_4656_, 1);
lean_inc(v_restoreM_4663_);
lean_dec_ref(v_inst_4656_);
v___f_4664_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4664_, 0, v_k_4660_);
lean_closure_set(v___f_4664_, 1, v_perm_4658_);
lean_closure_set(v___f_4664_, 2, v_type_4659_);
v___x_4665_ = lean_apply_2(v_liftWith_4662_, lean_box(0), v___f_4664_);
v___x_4666_ = lean_apply_1(v_restoreM_4663_, lean_box(0));
v___x_4667_ = lean_apply_4(v_toBind_4661_, lean_box(0), lean_box(0), v___x_4665_, v___x_4666_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4668_, lean_object* v_00_u03b1_4669_, lean_object* v_inst_4670_, lean_object* v_inst_4671_, lean_object* v_perm_4672_, lean_object* v_type_4673_, lean_object* v_k_4674_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4670_, v_inst_4671_, v_perm_4672_, v_type_4673_, v_k_4674_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v___f_4682_; lean_object* v___x_598__overap_4683_; lean_object* v___x_4684_; 
v___f_4682_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_598__overap_4683_ = lean_panic_fn_borrowed(v___f_4682_, v_msg_4676_);
lean_inc(v___y_4680_);
lean_inc_ref(v___y_4679_);
lean_inc(v___y_4678_);
lean_inc_ref(v___y_4677_);
v___x_4684_ = lean_apply_5(v___x_598__overap_4683_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, lean_box(0));
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
return v_res_4691_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4694_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4695_ = lean_unsigned_to_nat(10u);
v___x_4696_ = lean_unsigned_to_nat(353u);
v___x_4697_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4698_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4699_ = l_mkPanicMessageWithDecl(v___x_4698_, v___x_4697_, v___x_4696_, v___x_4695_, v___x_4694_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4700_, lean_object* v_xs_4701_, lean_object* v_tail_4702_, lean_object* v_ys_4703_, lean_object* v_type_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4700_, v_xs_4701_, v_tail_4702_, v_ys_4703_, v_type_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec_ref(v_ys_4703_);
lean_dec(v___x_4700_);
return v_res_4710_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4711_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4712_ = lean_unsigned_to_nat(8u);
v___x_4713_ = lean_unsigned_to_nat(349u);
v___x_4714_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4715_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4716_ = l_mkPanicMessageWithDecl(v___x_4715_, v___x_4714_, v___x_4713_, v___x_4712_, v___x_4711_);
return v___x_4716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4717_, lean_object* v_x_4718_, lean_object* v_x_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
if (lean_obj_tag(v_x_4718_) == 0)
{
lean_object* v___x_4725_; 
lean_dec_ref(v_xs_4717_);
v___x_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4725_, 0, v_x_4719_);
return v___x_4725_;
}
else
{
lean_object* v_head_4726_; 
v_head_4726_ = lean_ctor_get(v_x_4718_, 0);
if (lean_obj_tag(v_head_4726_) == 0)
{
lean_object* v_tail_4727_; lean_object* v___x_4728_; lean_object* v___f_4729_; lean_object* v___x_4730_; uint8_t v___x_4731_; lean_object* v___x_4732_; 
v_tail_4727_ = lean_ctor_get(v_x_4718_, 1);
lean_inc(v_tail_4727_);
lean_dec_ref_known(v_x_4718_, 2);
v___x_4728_ = lean_unsigned_to_nat(1u);
v___f_4729_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4729_, 0, v___x_4728_);
lean_closure_set(v___f_4729_, 1, v_xs_4717_);
lean_closure_set(v___f_4729_, 2, v_tail_4727_);
v___x_4730_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4731_ = 0;
v___x_4732_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4719_, v___x_4730_, v___f_4729_, v___x_4731_, v___x_4731_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_);
return v___x_4732_;
}
else
{
lean_object* v_tail_4733_; lean_object* v_val_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; 
lean_inc_ref(v_head_4726_);
v_tail_4733_ = lean_ctor_get(v_x_4718_, 1);
lean_inc(v_tail_4733_);
lean_dec_ref_known(v_x_4718_, 2);
v_val_4734_ = lean_ctor_get(v_head_4726_, 0);
lean_inc(v_val_4734_);
lean_dec_ref_known(v_head_4726_, 1);
v___x_4735_ = lean_array_get_size(v_xs_4717_);
v___x_4736_ = lean_nat_dec_lt(v_val_4734_, v___x_4735_);
if (v___x_4736_ == 0)
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
lean_dec(v_val_4734_);
lean_dec(v_tail_4733_);
lean_dec_ref(v_x_4719_);
lean_dec_ref(v_xs_4717_);
v___x_4737_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4738_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4737_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_);
return v___x_4738_;
}
else
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4739_ = l_Lean_instInhabitedExpr;
v___x_4740_ = lean_array_get_borrowed(v___x_4739_, v_xs_4717_, v_val_4734_);
lean_dec(v_val_4734_);
v___x_4741_ = lean_unsigned_to_nat(1u);
v___x_4742_ = lean_mk_empty_array_with_capacity(v___x_4741_);
lean_inc(v___x_4740_);
v___x_4743_ = lean_array_push(v___x_4742_, v___x_4740_);
v___x_4744_ = l_Lean_Meta_instantiateForall(v_x_4719_, v___x_4743_, v_a_4720_, v_a_4721_, v_a_4722_, v_a_4723_);
lean_dec_ref(v___x_4743_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
v_x_4718_ = v_tail_4733_;
v_x_4719_ = v_a_4745_;
goto _start;
}
else
{
lean_dec(v_tail_4733_);
lean_dec_ref(v_xs_4717_);
return v___x_4744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4747_, lean_object* v_xs_4748_, lean_object* v_tail_4749_, lean_object* v_ys_4750_, lean_object* v_type_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
lean_object* v___x_4757_; uint8_t v___x_4758_; 
v___x_4757_ = lean_array_get_size(v_ys_4750_);
v___x_4758_ = lean_nat_dec_eq(v___x_4757_, v___x_4747_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
lean_dec_ref(v_type_4751_);
lean_dec(v_tail_4749_);
lean_dec_ref(v_xs_4748_);
v___x_4759_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4760_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4759_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
return v___x_4760_;
}
else
{
lean_object* v___x_4761_; 
v___x_4761_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4748_, v_tail_4749_, v_type_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; uint8_t v___x_4763_; uint8_t v___x_4764_; lean_object* v___x_4765_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v___x_4761_, 1);
v___x_4763_ = 0;
v___x_4764_ = 1;
v___x_4765_ = l_Lean_Meta_mkForallFVars(v_ys_4750_, v_a_4762_, v___x_4763_, v___x_4758_, v___x_4758_, v___x_4764_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
return v___x_4765_;
}
else
{
return v___x_4761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4766_, lean_object* v_x_4767_, lean_object* v_x_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4766_, v_x_4767_, v_x_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
return v_res_4774_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4777_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4778_ = lean_unsigned_to_nat(2u);
v___x_4779_ = lean_unsigned_to_nat(343u);
v___x_4780_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4781_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4782_ = l_mkPanicMessageWithDecl(v___x_4781_, v___x_4780_, v___x_4779_, v___x_4778_, v___x_4777_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4783_, lean_object* v_type_u2080_4784_, lean_object* v_xs_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4791_ = lean_array_get_size(v_xs_4785_);
v___x_4792_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4783_);
v___x_4793_ = lean_nat_dec_eq(v___x_4791_, v___x_4792_);
lean_dec(v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
lean_dec_ref(v_xs_4785_);
lean_dec_ref(v_type_u2080_4784_);
lean_dec_ref(v_perm_4783_);
v___x_4794_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4795_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4794_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_);
return v___x_4795_;
}
else
{
lean_object* v_mask_4796_; lean_object* v___x_4797_; 
v_mask_4796_ = lean_array_to_list(v_perm_4783_);
v___x_4797_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4785_, v_mask_4796_, v_type_u2080_4784_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_);
return v___x_4797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4798_, lean_object* v_type_u2080_4799_, lean_object* v_xs_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4798_, v_type_u2080_4799_, v_xs_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4807_, lean_object* v_maxFVars_4808_, lean_object* v_k_4809_, uint8_t v_cleanupAnnotations_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_){
_start:
{
lean_object* v___f_4816_; uint8_t v___x_4817_; uint8_t v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___f_4816_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4816_, 0, v_k_4809_);
v___x_4817_ = 1;
v___x_4818_ = 0;
v___x_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4819_, 0, v_maxFVars_4808_);
v___x_4820_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4807_, v___x_4817_, v___x_4818_, v___x_4817_, v___x_4818_, v___x_4819_, v___f_4816_, v_cleanupAnnotations_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
lean_dec_ref_known(v___x_4819_, 1);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4820_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4820_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
v_a_4829_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4820_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4820_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4837_, lean_object* v_maxFVars_4838_, lean_object* v_k_4839_, lean_object* v_cleanupAnnotations_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4846_; lean_object* v_res_4847_; 
v_cleanupAnnotations_boxed_4846_ = lean_unbox(v_cleanupAnnotations_4840_);
v_res_4847_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4837_, v_maxFVars_4838_, v_k_4839_, v_cleanupAnnotations_boxed_4846_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4848_, lean_object* v_e_4849_, lean_object* v_maxFVars_4850_, lean_object* v_k_4851_, uint8_t v_cleanupAnnotations_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v___x_4858_; 
v___x_4858_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4849_, v_maxFVars_4850_, v_k_4851_, v_cleanupAnnotations_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4859_, lean_object* v_e_4860_, lean_object* v_maxFVars_4861_, lean_object* v_k_4862_, lean_object* v_cleanupAnnotations_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4869_; lean_object* v_res_4870_; 
v_cleanupAnnotations_boxed_4869_ = lean_unbox(v_cleanupAnnotations_4863_);
v_res_4870_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4859_, v_e_4860_, v_maxFVars_4861_, v_k_4862_, v_cleanupAnnotations_boxed_4869_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
return v_res_4870_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4871_){
_start:
{
if (lean_obj_tag(v_x_4871_) == 0)
{
uint8_t v___x_4872_; 
v___x_4872_ = 1;
return v___x_4872_;
}
else
{
lean_object* v_head_4873_; 
v_head_4873_ = lean_ctor_get(v_x_4871_, 0);
if (lean_obj_tag(v_head_4873_) == 0)
{
lean_object* v_tail_4874_; 
v_tail_4874_ = lean_ctor_get(v_x_4871_, 1);
v_x_4871_ = v_tail_4874_;
goto _start;
}
else
{
uint8_t v___x_4876_; 
v___x_4876_ = 0;
return v___x_4876_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4877_){
_start:
{
uint8_t v_res_4878_; lean_object* v_r_4879_; 
v_res_4878_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4877_);
lean_dec(v_x_4877_);
v_r_4879_ = lean_box(v_res_4878_);
return v_r_4879_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4882_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4883_ = lean_unsigned_to_nat(12u);
v___x_4884_ = lean_unsigned_to_nat(376u);
v___x_4885_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4886_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4887_ = l_mkPanicMessageWithDecl(v___x_4886_, v___x_4885_, v___x_4884_, v___x_4883_, v___x_4882_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4888_, lean_object* v_xs_4889_, lean_object* v_tail_4890_, lean_object* v___x_4891_, lean_object* v___x_4892_, lean_object* v_ys_4893_, lean_object* v_value_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
uint8_t v___x_1213__boxed_4900_; uint8_t v___x_1214__boxed_4901_; lean_object* v_res_4902_; 
v___x_1213__boxed_4900_ = lean_unbox(v___x_4891_);
v___x_1214__boxed_4901_ = lean_unbox(v___x_4892_);
v_res_4902_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4888_, v_xs_4889_, v_tail_4890_, v___x_1213__boxed_4900_, v___x_1214__boxed_4901_, v_ys_4893_, v_value_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
lean_dec_ref(v_ys_4893_);
lean_dec(v___x_4888_);
return v_res_4902_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4903_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4904_ = lean_unsigned_to_nat(8u);
v___x_4905_ = lean_unsigned_to_nat(368u);
v___x_4906_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4907_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4908_ = l_mkPanicMessageWithDecl(v___x_4907_, v___x_4906_, v___x_4905_, v___x_4904_, v___x_4903_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4909_, lean_object* v_x_4910_, lean_object* v_x_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
if (lean_obj_tag(v_x_4910_) == 0)
{
lean_object* v___x_4917_; 
lean_dec_ref(v_xs_4909_);
v___x_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4917_, 0, v_x_4911_);
return v___x_4917_;
}
else
{
lean_object* v_head_4918_; 
v_head_4918_ = lean_ctor_get(v_x_4910_, 0);
if (lean_obj_tag(v_head_4918_) == 0)
{
lean_object* v_tail_4919_; uint8_t v___x_4920_; 
v_tail_4919_ = lean_ctor_get(v_x_4910_, 1);
lean_inc(v_tail_4919_);
lean_dec_ref_known(v_x_4910_, 2);
v___x_4920_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4919_);
if (v___x_4920_ == 0)
{
uint8_t v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___f_4925_; lean_object* v___x_4926_; 
v___x_4921_ = 1;
v___x_4922_ = lean_unsigned_to_nat(1u);
v___x_4923_ = lean_box(v___x_4920_);
v___x_4924_ = lean_box(v___x_4921_);
v___f_4925_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4925_, 0, v___x_4922_);
lean_closure_set(v___f_4925_, 1, v_xs_4909_);
lean_closure_set(v___f_4925_, 2, v_tail_4919_);
lean_closure_set(v___f_4925_, 3, v___x_4923_);
lean_closure_set(v___f_4925_, 4, v___x_4924_);
v___x_4926_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4911_, v___x_4922_, v___f_4925_, v___x_4920_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
return v___x_4926_;
}
else
{
lean_object* v___x_4927_; 
lean_dec(v_tail_4919_);
lean_dec_ref(v_xs_4909_);
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v_x_4911_);
return v___x_4927_;
}
}
else
{
lean_object* v_tail_4928_; lean_object* v_val_4929_; lean_object* v___x_4930_; uint8_t v___x_4931_; 
lean_inc_ref(v_head_4918_);
v_tail_4928_ = lean_ctor_get(v_x_4910_, 1);
lean_inc(v_tail_4928_);
lean_dec_ref_known(v_x_4910_, 2);
v_val_4929_ = lean_ctor_get(v_head_4918_, 0);
lean_inc(v_val_4929_);
lean_dec_ref_known(v_head_4918_, 1);
v___x_4930_ = lean_array_get_size(v_xs_4909_);
v___x_4931_ = lean_nat_dec_lt(v_val_4929_, v___x_4930_);
if (v___x_4931_ == 0)
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_dec(v_val_4929_);
lean_dec(v_tail_4928_);
lean_dec_ref(v_x_4911_);
lean_dec_ref(v_xs_4909_);
v___x_4932_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4933_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4932_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
return v___x_4933_;
}
else
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4934_ = l_Lean_instInhabitedExpr;
v___x_4935_ = lean_array_get_borrowed(v___x_4934_, v_xs_4909_, v_val_4929_);
lean_dec(v_val_4929_);
v___x_4936_ = lean_unsigned_to_nat(1u);
v___x_4937_ = lean_mk_empty_array_with_capacity(v___x_4936_);
lean_inc(v___x_4935_);
v___x_4938_ = lean_array_push(v___x_4937_, v___x_4935_);
v___x_4939_ = l_Lean_Meta_instantiateLambda(v_x_4911_, v___x_4938_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_);
lean_dec_ref(v___x_4938_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v_a_4940_; 
v_a_4940_ = lean_ctor_get(v___x_4939_, 0);
lean_inc(v_a_4940_);
lean_dec_ref_known(v___x_4939_, 1);
v_x_4910_ = v_tail_4928_;
v_x_4911_ = v_a_4940_;
goto _start;
}
else
{
lean_dec(v_tail_4928_);
lean_dec_ref(v_xs_4909_);
return v___x_4939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4942_, lean_object* v_xs_4943_, lean_object* v_tail_4944_, uint8_t v___x_4945_, uint8_t v___x_4946_, lean_object* v_ys_4947_, lean_object* v_value_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
lean_object* v___x_4954_; uint8_t v___x_4955_; 
v___x_4954_ = lean_array_get_size(v_ys_4947_);
v___x_4955_ = lean_nat_dec_eq(v___x_4954_, v___x_4942_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
lean_dec_ref(v_value_4948_);
lean_dec(v_tail_4944_);
lean_dec_ref(v_xs_4943_);
v___x_4956_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4957_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4956_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
return v___x_4957_;
}
else
{
lean_object* v___x_4958_; 
v___x_4958_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4943_, v_tail_4944_, v_value_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; uint8_t v___x_4960_; lean_object* v___x_4961_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4958_, 1);
v___x_4960_ = 1;
v___x_4961_ = l_Lean_Meta_mkLambdaFVars(v_ys_4947_, v_a_4959_, v___x_4945_, v___x_4946_, v___x_4945_, v___x_4946_, v___x_4960_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
return v___x_4961_;
}
else
{
return v___x_4958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4962_, lean_object* v_x_4963_, lean_object* v_x_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4962_, v_x_4963_, v_x_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_);
lean_dec(v_a_4968_);
lean_dec_ref(v_a_4967_);
lean_dec(v_a_4966_);
lean_dec_ref(v_a_4965_);
return v_res_4970_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4972_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4973_ = lean_unsigned_to_nat(2u);
v___x_4974_ = lean_unsigned_to_nat(362u);
v___x_4975_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_4976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4977_ = l_mkPanicMessageWithDecl(v___x_4976_, v___x_4975_, v___x_4974_, v___x_4973_, v___x_4972_);
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_4978_, lean_object* v_value_u2080_4979_, lean_object* v_xs_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_){
_start:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; uint8_t v___x_4988_; 
v___x_4986_ = lean_array_get_size(v_xs_4980_);
v___x_4987_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4978_);
v___x_4988_ = lean_nat_dec_eq(v___x_4986_, v___x_4987_);
lean_dec(v___x_4987_);
if (v___x_4988_ == 0)
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
lean_dec_ref(v_xs_4980_);
lean_dec_ref(v_value_u2080_4979_);
lean_dec_ref(v_perm_4978_);
v___x_4989_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_4990_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4989_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
return v___x_4990_;
}
else
{
lean_object* v_mask_4991_; lean_object* v___x_4992_; 
v_mask_4991_ = lean_array_to_list(v_perm_4978_);
v___x_4992_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4980_, v_mask_4991_, v_value_u2080_4979_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_);
return v___x_4992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_4993_, lean_object* v_value_u2080_4994_, lean_object* v_xs_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_4993_, v_value_u2080_4994_, v_xs_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
lean_dec(v_a_4999_);
lean_dec_ref(v_a_4998_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
return v_res_5001_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5009_; 
v___x_5009_ = l_Array_instInhabited(lean_box(0));
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5010_){
_start:
{
lean_object* v___f_5011_; lean_object* v___f_5012_; lean_object* v___f_5013_; lean_object* v___f_5014_; lean_object* v___f_5015_; lean_object* v___f_5016_; lean_object* v___f_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___f_5011_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5012_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5013_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5014_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5015_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5016_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5017_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___f_5011_);
lean_ctor_set(v___x_5018_, 1, v___f_5012_);
v___x_5019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
lean_ctor_set(v___x_5019_, 1, v___f_5013_);
lean_ctor_set(v___x_5019_, 2, v___f_5014_);
lean_ctor_set(v___x_5019_, 3, v___f_5015_);
lean_ctor_set(v___x_5019_, 4, v___f_5016_);
v___x_5020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
lean_ctor_set(v___x_5020_, 1, v___f_5017_);
v___x_5021_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5022_ = l_instInhabitedOfMonad___redArg(v___x_5020_, v___x_5021_);
v___x_5023_ = lean_panic_fn_borrowed(v___x_5022_, v_msg_5010_);
lean_dec(v___x_5022_);
return v___x_5023_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5024_, lean_object* v_msg_5025_){
_start:
{
lean_object* v___x_5026_; 
v___x_5026_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5025_);
return v___x_5026_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5029_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5030_ = lean_unsigned_to_nat(8u);
v___x_5031_ = lean_unsigned_to_nat(394u);
v___x_5032_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5033_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5034_ = l_mkPanicMessageWithDecl(v___x_5033_, v___x_5032_, v___x_5031_, v___x_5030_, v___x_5029_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5035_, lean_object* v_x_5036_){
_start:
{
if (lean_obj_tag(v_x_5035_) == 0)
{
return v_x_5036_;
}
else
{
lean_object* v_head_5037_; lean_object* v_fst_5038_; 
v_head_5037_ = lean_ctor_get(v_x_5035_, 0);
v_fst_5038_ = lean_ctor_get(v_head_5037_, 0);
if (lean_obj_tag(v_fst_5038_) == 0)
{
lean_object* v_tail_5039_; 
v_tail_5039_ = lean_ctor_get(v_x_5035_, 1);
lean_inc(v_tail_5039_);
lean_dec_ref_known(v_x_5035_, 2);
v_x_5035_ = v_tail_5039_;
goto _start;
}
else
{
lean_object* v_tail_5041_; lean_object* v_snd_5042_; lean_object* v_val_5043_; lean_object* v___x_5044_; uint8_t v___x_5045_; 
lean_inc_ref(v_fst_5038_);
lean_inc(v_head_5037_);
v_tail_5041_ = lean_ctor_get(v_x_5035_, 1);
lean_inc(v_tail_5041_);
lean_dec_ref_known(v_x_5035_, 2);
v_snd_5042_ = lean_ctor_get(v_head_5037_, 1);
lean_inc(v_snd_5042_);
lean_dec(v_head_5037_);
v_val_5043_ = lean_ctor_get(v_fst_5038_, 0);
lean_inc(v_val_5043_);
lean_dec_ref_known(v_fst_5038_, 1);
v___x_5044_ = lean_array_get_size(v_x_5036_);
v___x_5045_ = lean_nat_dec_lt(v_val_5043_, v___x_5044_);
if (v___x_5045_ == 0)
{
lean_object* v___x_5046_; lean_object* v___x_5047_; 
lean_dec(v_val_5043_);
lean_dec(v_snd_5042_);
lean_dec(v_tail_5041_);
lean_dec_ref(v_x_5036_);
v___x_5046_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5047_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5046_);
return v___x_5047_;
}
else
{
lean_object* v___x_5048_; 
v___x_5048_ = lean_array_set(v_x_5036_, v_val_5043_, v_snd_5042_);
lean_dec(v_val_5043_);
v_x_5035_ = v_tail_5041_;
v_x_5036_ = v___x_5048_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5050_, lean_object* v_x_5051_, lean_object* v_x_5052_){
_start:
{
lean_object* v___x_5053_; 
v___x_5053_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5051_, v_x_5052_);
return v___x_5053_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5056_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5057_ = lean_unsigned_to_nat(2u);
v___x_5058_ = lean_unsigned_to_nat(384u);
v___x_5059_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5060_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5061_ = l_mkPanicMessageWithDecl(v___x_5060_, v___x_5059_, v___x_5058_, v___x_5057_, v___x_5056_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5064_, lean_object* v_xs_5065_){
_start:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; uint8_t v___x_5068_; 
v___x_5066_ = lean_array_get_size(v_xs_5065_);
v___x_5067_ = lean_array_get_size(v_perm_5064_);
v___x_5068_ = lean_nat_dec_eq(v___x_5066_, v___x_5067_);
if (v___x_5068_ == 0)
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5070_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5069_);
return v___x_5070_;
}
else
{
lean_object* v___x_5071_; uint8_t v___x_5072_; 
v___x_5071_ = lean_unsigned_to_nat(0u);
v___x_5072_ = lean_nat_dec_eq(v___x_5066_, v___x_5071_);
if (v___x_5072_ == 0)
{
lean_object* v_dummy_5073_; lean_object* v___x_5074_; lean_object* v_ys_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
v_dummy_5073_ = lean_array_fget_borrowed(v_xs_5065_, v___x_5071_);
v___x_5074_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5064_);
lean_inc(v_dummy_5073_);
v_ys_5075_ = lean_mk_array(v___x_5074_, v_dummy_5073_);
v___x_5076_ = l_Array_zip___redArg(v_perm_5064_, v_xs_5065_);
v___x_5077_ = lean_array_to_list(v___x_5076_);
v___x_5078_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5077_, v_ys_5075_);
return v___x_5078_;
}
else
{
lean_object* v___x_5079_; 
v___x_5079_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5080_, lean_object* v_xs_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5080_, v_xs_5081_);
lean_dec_ref(v_xs_5081_);
lean_dec_ref(v_perm_5080_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5083_, lean_object* v_perm_5084_, lean_object* v_xs_5085_){
_start:
{
lean_object* v___x_5086_; 
v___x_5086_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5084_, v_xs_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5087_, lean_object* v_perm_5088_, lean_object* v_xs_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5087_, v_perm_5088_, v_xs_5089_);
lean_dec_ref(v_xs_5089_);
lean_dec_ref(v_perm_5088_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5091_, lean_object* v_upperBound_5092_, lean_object* v_perm_5093_, lean_object* v_a_5094_, lean_object* v_b_5095_){
_start:
{
lean_object* v_a_5097_; uint8_t v___x_5104_; 
v___x_5104_ = lean_nat_dec_lt(v_a_5094_, v_upperBound_5092_);
if (v___x_5104_ == 0)
{
lean_dec(v_a_5094_);
return v_b_5095_;
}
else
{
lean_object* v___x_5105_; uint8_t v___x_5106_; 
v___x_5105_ = lean_array_get_size(v_perm_5093_);
v___x_5106_ = lean_nat_dec_lt(v_a_5094_, v___x_5105_);
if (v___x_5106_ == 0)
{
goto v___jp_5101_;
}
else
{
lean_object* v___x_5107_; 
v___x_5107_ = lean_array_fget_borrowed(v_perm_5093_, v_a_5094_);
if (lean_obj_tag(v___x_5107_) == 0)
{
goto v___jp_5101_;
}
else
{
v_a_5097_ = v_b_5095_;
goto v___jp_5096_;
}
}
}
v___jp_5096_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
v___x_5098_ = lean_unsigned_to_nat(1u);
v___x_5099_ = lean_nat_add(v_a_5094_, v___x_5098_);
lean_dec(v_a_5094_);
v_a_5094_ = v___x_5099_;
v_b_5095_ = v_a_5097_;
goto _start;
}
v___jp_5101_:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5102_ = lean_array_fget_borrowed(v_xs_5091_, v_a_5094_);
lean_inc(v___x_5102_);
v___x_5103_ = lean_array_push(v_b_5095_, v___x_5102_);
v_a_5097_ = v___x_5103_;
goto v___jp_5096_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5108_, lean_object* v_upperBound_5109_, lean_object* v_perm_5110_, lean_object* v_a_5111_, lean_object* v_b_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5108_, v_upperBound_5109_, v_perm_5110_, v_a_5111_, v_b_5112_);
lean_dec_ref(v_perm_5110_);
lean_dec(v_upperBound_5109_);
lean_dec_ref(v_xs_5108_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5114_, lean_object* v_xs_5115_){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v_ys_5118_; lean_object* v___x_5119_; 
v___x_5116_ = lean_array_get_size(v_xs_5115_);
v___x_5117_ = lean_unsigned_to_nat(0u);
v_ys_5118_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5119_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5115_, v___x_5116_, v_perm_5114_, v___x_5117_, v_ys_5118_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5120_, lean_object* v_xs_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5120_, v_xs_5121_);
lean_dec_ref(v_xs_5121_);
lean_dec_ref(v_perm_5120_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5123_, lean_object* v_perm_5124_, lean_object* v_xs_5125_){
_start:
{
lean_object* v___x_5126_; 
v___x_5126_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5124_, v_xs_5125_);
return v___x_5126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5127_, lean_object* v_perm_5128_, lean_object* v_xs_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5127_, v_perm_5128_, v_xs_5129_);
lean_dec_ref(v_xs_5129_);
lean_dec_ref(v_perm_5128_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5131_, lean_object* v_xs_5132_, lean_object* v_upperBound_5133_, lean_object* v_perm_5134_, lean_object* v_inst_5135_, lean_object* v_R_5136_, lean_object* v_a_5137_, lean_object* v_b_5138_, lean_object* v_c_5139_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5132_, v_upperBound_5133_, v_perm_5134_, v_a_5137_, v_b_5138_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5141_, lean_object* v_xs_5142_, lean_object* v_upperBound_5143_, lean_object* v_perm_5144_, lean_object* v_inst_5145_, lean_object* v_R_5146_, lean_object* v_a_5147_, lean_object* v_b_5148_, lean_object* v_c_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5141_, v_xs_5142_, v_upperBound_5143_, v_perm_5144_, v_inst_5145_, v_R_5146_, v_a_5147_, v_b_5148_, v_c_5149_);
lean_dec_ref(v_perm_5144_);
lean_dec(v_upperBound_5143_);
lean_dec_ref(v_xs_5142_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5151_){
_start:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5152_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5153_ = lean_panic_fn_borrowed(v___x_5152_, v_msg_5151_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5154_, lean_object* v_msg_5155_){
_start:
{
lean_object* v___x_5156_; 
v___x_5156_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5155_);
return v___x_5156_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5157_, lean_object* v___x_5158_, lean_object* v_i_5159_, lean_object* v___x_5160_, lean_object* v_as_5161_, size_t v_i_5162_, size_t v_stop_5163_){
_start:
{
uint8_t v___x_5164_; 
v___x_5164_ = lean_usize_dec_eq(v_i_5162_, v_stop_5163_);
if (v___x_5164_ == 0)
{
uint8_t v___x_5165_; uint8_t v___y_5167_; lean_object* v___x_5171_; 
v___x_5165_ = 1;
v___x_5171_ = lean_array_uget_borrowed(v_as_5161_, v_i_5162_);
if (lean_obj_tag(v___x_5171_) == 0)
{
uint8_t v___x_5172_; 
v___x_5172_ = lean_nat_dec_lt(v_j_5157_, v___x_5158_);
v___y_5167_ = v___x_5172_;
goto v___jp_5166_;
}
else
{
uint8_t v___x_5173_; 
v___x_5173_ = lean_nat_dec_lt(v_i_5159_, v___x_5160_);
v___y_5167_ = v___x_5173_;
goto v___jp_5166_;
}
v___jp_5166_:
{
if (v___y_5167_ == 0)
{
size_t v___x_5168_; size_t v___x_5169_; 
v___x_5168_ = ((size_t)1ULL);
v___x_5169_ = lean_usize_add(v_i_5162_, v___x_5168_);
v_i_5162_ = v___x_5169_;
goto _start;
}
else
{
return v___x_5165_;
}
}
}
else
{
uint8_t v___x_5174_; 
v___x_5174_ = 0;
return v___x_5174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5175_, lean_object* v___x_5176_, lean_object* v_i_5177_, lean_object* v___x_5178_, lean_object* v_as_5179_, lean_object* v_i_5180_, lean_object* v_stop_5181_){
_start:
{
size_t v_i_boxed_5182_; size_t v_stop_boxed_5183_; uint8_t v_res_5184_; lean_object* v_r_5185_; 
v_i_boxed_5182_ = lean_unbox_usize(v_i_5180_);
lean_dec(v_i_5180_);
v_stop_boxed_5183_ = lean_unbox_usize(v_stop_5181_);
lean_dec(v_stop_5181_);
v_res_5184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5175_, v___x_5176_, v_i_5177_, v___x_5178_, v_as_5179_, v_i_boxed_5182_, v_stop_boxed_5183_);
lean_dec_ref(v_as_5179_);
lean_dec(v___x_5178_);
lean_dec(v_i_5177_);
lean_dec(v___x_5176_);
lean_dec(v_j_5175_);
v_r_5185_ = lean_box(v_res_5184_);
return v_r_5185_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
v___x_5188_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5189_ = lean_unsigned_to_nat(10u);
v___x_5190_ = lean_unsigned_to_nat(425u);
v___x_5191_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5193_ = l_mkPanicMessageWithDecl(v___x_5192_, v___x_5191_, v___x_5190_, v___x_5189_, v___x_5188_);
return v___x_5193_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; 
v___x_5195_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5196_ = lean_unsigned_to_nat(12u);
v___x_5197_ = lean_unsigned_to_nat(433u);
v___x_5198_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5199_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5200_ = l_mkPanicMessageWithDecl(v___x_5199_, v___x_5198_, v___x_5197_, v___x_5196_, v___x_5195_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5201_, lean_object* v_fixedArgs_5202_, lean_object* v_varyingArgs_5203_, lean_object* v_i_5204_, lean_object* v_j_5205_, lean_object* v_xs_5206_){
_start:
{
lean_object* v_lower_5208_; lean_object* v_upper_5209_; lean_object* v___x_5213_; uint8_t v___x_5214_; 
v___x_5213_ = lean_array_get_size(v_perm_5201_);
v___x_5214_ = lean_nat_dec_lt(v_i_5204_, v___x_5213_);
if (v___x_5214_ == 0)
{
lean_object* v___x_5215_; lean_object* v___x_5216_; uint8_t v___x_5217_; 
lean_dec(v_i_5204_);
lean_dec_ref(v_perm_5201_);
v___x_5215_ = lean_unsigned_to_nat(0u);
v___x_5216_ = lean_array_get_size(v_varyingArgs_5203_);
v___x_5217_ = lean_nat_dec_le(v_j_5205_, v___x_5215_);
if (v___x_5217_ == 0)
{
v_lower_5208_ = v_j_5205_;
v_upper_5209_ = v___x_5216_;
goto v___jp_5207_;
}
else
{
lean_dec(v_j_5205_);
v_lower_5208_ = v___x_5215_;
v_upper_5209_ = v___x_5216_;
goto v___jp_5207_;
}
}
else
{
lean_object* v___x_5218_; 
v___x_5218_ = lean_array_fget_borrowed(v_perm_5201_, v_i_5204_);
if (lean_obj_tag(v___x_5218_) == 1)
{
lean_object* v_val_5219_; lean_object* v___x_5220_; uint8_t v___x_5221_; 
v_val_5219_ = lean_ctor_get(v___x_5218_, 0);
v___x_5220_ = lean_array_get_size(v_fixedArgs_5202_);
v___x_5221_ = lean_nat_dec_lt(v_val_5219_, v___x_5220_);
if (v___x_5221_ == 0)
{
lean_object* v___x_5222_; lean_object* v___x_5223_; 
lean_dec_ref(v_xs_5206_);
lean_dec(v_j_5205_);
lean_dec(v_i_5204_);
lean_dec_ref(v_varyingArgs_5203_);
lean_dec_ref(v_perm_5201_);
v___x_5222_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5223_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5222_);
return v___x_5223_;
}
else
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v___x_5224_ = lean_unsigned_to_nat(1u);
v___x_5225_ = lean_nat_add(v_i_5204_, v___x_5224_);
lean_dec(v_i_5204_);
v___x_5226_ = lean_array_fget_borrowed(v_fixedArgs_5202_, v_val_5219_);
lean_inc(v___x_5226_);
v___x_5227_ = lean_array_push(v_xs_5206_, v___x_5226_);
v_i_5204_ = v___x_5225_;
v_xs_5206_ = v___x_5227_;
goto _start;
}
}
else
{
lean_object* v___x_5229_; lean_object* v___y_5231_; lean_object* v___y_5232_; lean_object* v___y_5233_; lean_object* v_lower_5241_; lean_object* v_upper_5242_; uint8_t v___x_5250_; 
v___x_5229_ = lean_array_get_size(v_varyingArgs_5203_);
v___x_5250_ = lean_nat_dec_lt(v_j_5205_, v___x_5229_);
if (v___x_5250_ == 0)
{
lean_object* v___x_5251_; uint8_t v___x_5252_; 
lean_dec_ref(v_varyingArgs_5203_);
v___x_5251_ = lean_unsigned_to_nat(0u);
v___x_5252_ = lean_nat_dec_le(v_i_5204_, v___x_5251_);
if (v___x_5252_ == 0)
{
lean_inc(v_i_5204_);
v_lower_5241_ = v_i_5204_;
v_upper_5242_ = v___x_5213_;
goto v___jp_5240_;
}
else
{
v_lower_5241_ = v___x_5251_;
v_upper_5242_ = v___x_5213_;
goto v___jp_5240_;
}
}
else
{
lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5253_ = lean_unsigned_to_nat(1u);
v___x_5254_ = lean_nat_add(v_i_5204_, v___x_5253_);
lean_dec(v_i_5204_);
v___x_5255_ = lean_nat_add(v_j_5205_, v___x_5253_);
v___x_5256_ = lean_array_fget_borrowed(v_varyingArgs_5203_, v_j_5205_);
lean_dec(v_j_5205_);
lean_inc(v___x_5256_);
v___x_5257_ = lean_array_push(v_xs_5206_, v___x_5256_);
v_i_5204_ = v___x_5254_;
v_j_5205_ = v___x_5255_;
v_xs_5206_ = v___x_5257_;
goto _start;
}
v___jp_5230_:
{
uint8_t v___x_5234_; 
v___x_5234_ = lean_nat_dec_lt(v___y_5232_, v___y_5233_);
if (v___x_5234_ == 0)
{
lean_dec(v___y_5233_);
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
lean_dec(v_j_5205_);
lean_dec(v_i_5204_);
return v_xs_5206_;
}
else
{
size_t v___x_5235_; size_t v___x_5236_; uint8_t v___x_5237_; 
v___x_5235_ = lean_usize_of_nat(v___y_5232_);
lean_dec(v___y_5232_);
v___x_5236_ = lean_usize_of_nat(v___y_5233_);
lean_dec(v___y_5233_);
v___x_5237_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5205_, v___x_5229_, v_i_5204_, v___x_5213_, v___y_5231_, v___x_5235_, v___x_5236_);
lean_dec_ref(v___y_5231_);
lean_dec(v_i_5204_);
lean_dec(v_j_5205_);
if (v___x_5237_ == 0)
{
return v_xs_5206_;
}
else
{
lean_object* v___x_5238_; lean_object* v___x_5239_; 
lean_dec_ref(v_xs_5206_);
v___x_5238_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5239_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5238_);
return v___x_5239_;
}
}
}
v___jp_5240_:
{
lean_object* v___x_5243_; lean_object* v_array_5244_; lean_object* v_start_5245_; lean_object* v_stop_5246_; uint8_t v___x_5247_; 
v___x_5243_ = l_Array_toSubarray___redArg(v_perm_5201_, v_lower_5241_, v_upper_5242_);
v_array_5244_ = lean_ctor_get(v___x_5243_, 0);
lean_inc_ref(v_array_5244_);
v_start_5245_ = lean_ctor_get(v___x_5243_, 1);
lean_inc(v_start_5245_);
v_stop_5246_ = lean_ctor_get(v___x_5243_, 2);
lean_inc(v_stop_5246_);
lean_dec_ref(v___x_5243_);
v___x_5247_ = lean_nat_dec_lt(v_start_5245_, v_stop_5246_);
if (v___x_5247_ == 0)
{
lean_dec(v_stop_5246_);
lean_dec(v_start_5245_);
lean_dec_ref(v_array_5244_);
lean_dec(v_j_5205_);
lean_dec(v_i_5204_);
return v_xs_5206_;
}
else
{
lean_object* v___x_5248_; uint8_t v___x_5249_; 
v___x_5248_ = lean_array_get_size(v_array_5244_);
v___x_5249_ = lean_nat_dec_le(v_stop_5246_, v___x_5248_);
if (v___x_5249_ == 0)
{
lean_dec(v_stop_5246_);
v___y_5231_ = v_array_5244_;
v___y_5232_ = v_start_5245_;
v___y_5233_ = v___x_5248_;
goto v___jp_5230_;
}
else
{
v___y_5231_ = v_array_5244_;
v___y_5232_ = v_start_5245_;
v___y_5233_ = v_stop_5246_;
goto v___jp_5230_;
}
}
}
}
}
v___jp_5207_:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5210_ = l_Array_toSubarray___redArg(v_varyingArgs_5203_, v_lower_5208_, v_upper_5209_);
v___x_5211_ = l_Subarray_copy___redArg(v___x_5210_);
v___x_5212_ = l_Array_append___redArg(v_xs_5206_, v___x_5211_);
lean_dec_ref(v___x_5211_);
return v___x_5212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5259_, lean_object* v_fixedArgs_5260_, lean_object* v_varyingArgs_5261_, lean_object* v_i_5262_, lean_object* v_j_5263_, lean_object* v_xs_5264_){
_start:
{
lean_object* v_res_5265_; 
v_res_5265_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5259_, v_fixedArgs_5260_, v_varyingArgs_5261_, v_i_5262_, v_j_5263_, v_xs_5264_);
lean_dec_ref(v_fixedArgs_5260_);
return v_res_5265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5266_, lean_object* v_perm_5267_, lean_object* v_fixedArgs_5268_, lean_object* v_varyingArgs_5269_, lean_object* v_i_5270_, lean_object* v_j_5271_, lean_object* v_xs_5272_){
_start:
{
lean_object* v___x_5273_; 
v___x_5273_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5267_, v_fixedArgs_5268_, v_varyingArgs_5269_, v_i_5270_, v_j_5271_, v_xs_5272_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5274_, lean_object* v_perm_5275_, lean_object* v_fixedArgs_5276_, lean_object* v_varyingArgs_5277_, lean_object* v_i_5278_, lean_object* v_j_5279_, lean_object* v_xs_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5274_, v_perm_5275_, v_fixedArgs_5276_, v_varyingArgs_5277_, v_i_5278_, v_j_5279_, v_xs_5280_);
lean_dec_ref(v_fixedArgs_5276_);
return v_res_5281_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
v___x_5284_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5285_ = lean_unsigned_to_nat(2u);
v___x_5286_ = lean_unsigned_to_nat(416u);
v___x_5287_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5288_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5289_ = l_mkPanicMessageWithDecl(v___x_5288_, v___x_5287_, v___x_5286_, v___x_5285_, v___x_5284_);
return v___x_5289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5290_, lean_object* v_fixedArgs_5291_, lean_object* v_varyingArgs_5292_){
_start:
{
lean_object* v___x_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; 
v___x_5293_ = lean_array_get_size(v_fixedArgs_5291_);
v___x_5294_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5290_);
v___x_5295_ = lean_nat_dec_eq(v___x_5293_, v___x_5294_);
lean_dec(v___x_5294_);
if (v___x_5295_ == 0)
{
lean_object* v___x_5296_; lean_object* v___x_5297_; 
lean_dec_ref(v_varyingArgs_5292_);
lean_dec_ref(v_perm_5290_);
v___x_5296_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5297_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5296_);
return v___x_5297_;
}
else
{
lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; 
v___x_5298_ = lean_unsigned_to_nat(0u);
v___x_5299_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5300_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5290_, v_fixedArgs_5291_, v_varyingArgs_5292_, v___x_5298_, v___x_5298_, v___x_5299_);
return v___x_5300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5301_, lean_object* v_fixedArgs_5302_, lean_object* v_varyingArgs_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5301_, v_fixedArgs_5302_, v_varyingArgs_5303_);
lean_dec_ref(v_fixedArgs_5302_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5305_, lean_object* v_perm_5306_, lean_object* v_fixedArgs_5307_, lean_object* v_varyingArgs_5308_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5306_, v_fixedArgs_5307_, v_varyingArgs_5308_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5310_, lean_object* v_perm_5311_, lean_object* v_fixedArgs_5312_, lean_object* v_varyingArgs_5313_){
_start:
{
lean_object* v_res_5314_; 
v_res_5314_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5310_, v_perm_5311_, v_fixedArgs_5312_, v_varyingArgs_5313_);
lean_dec_ref(v_fixedArgs_5312_);
return v_res_5314_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5315_, lean_object* v_x_5316_){
_start:
{
if (lean_obj_tag(v_x_5315_) == 0)
{
if (lean_obj_tag(v_x_5316_) == 0)
{
uint8_t v___x_5317_; 
v___x_5317_ = 1;
return v___x_5317_;
}
else
{
uint8_t v___x_5318_; 
v___x_5318_ = 0;
return v___x_5318_;
}
}
else
{
if (lean_obj_tag(v_x_5316_) == 0)
{
uint8_t v___x_5319_; 
v___x_5319_ = 0;
return v___x_5319_;
}
else
{
lean_object* v_val_5320_; lean_object* v_val_5321_; uint8_t v___x_5322_; 
v_val_5320_ = lean_ctor_get(v_x_5315_, 0);
v_val_5321_ = lean_ctor_get(v_x_5316_, 0);
v___x_5322_ = lean_nat_dec_eq(v_val_5320_, v_val_5321_);
return v___x_5322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5323_, lean_object* v_x_5324_){
_start:
{
uint8_t v_res_5325_; lean_object* v_r_5326_; 
v_res_5325_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5323_, v_x_5324_);
lean_dec(v_x_5324_);
lean_dec(v_x_5323_);
v_r_5326_ = lean_box(v_res_5325_);
return v_r_5326_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5327_, lean_object* v_ys_5328_, lean_object* v_x_5329_){
_start:
{
lean_object* v_zero_5330_; uint8_t v_isZero_5331_; 
v_zero_5330_ = lean_unsigned_to_nat(0u);
v_isZero_5331_ = lean_nat_dec_eq(v_x_5329_, v_zero_5330_);
if (v_isZero_5331_ == 1)
{
lean_dec(v_x_5329_);
return v_isZero_5331_;
}
else
{
lean_object* v_one_5332_; lean_object* v_n_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; uint8_t v___x_5336_; 
v_one_5332_ = lean_unsigned_to_nat(1u);
v_n_5333_ = lean_nat_sub(v_x_5329_, v_one_5332_);
lean_dec(v_x_5329_);
v___x_5334_ = lean_array_fget_borrowed(v_xs_5327_, v_n_5333_);
v___x_5335_ = lean_array_fget_borrowed(v_ys_5328_, v_n_5333_);
v___x_5336_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5334_, v___x_5335_);
if (v___x_5336_ == 0)
{
lean_dec(v_n_5333_);
return v___x_5336_;
}
else
{
v_x_5329_ = v_n_5333_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5338_, lean_object* v_ys_5339_, lean_object* v_x_5340_){
_start:
{
uint8_t v_res_5341_; lean_object* v_r_5342_; 
v_res_5341_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5338_, v_ys_5339_, v_x_5340_);
lean_dec_ref(v_ys_5339_);
lean_dec_ref(v_xs_5338_);
v_r_5342_ = lean_box(v_res_5341_);
return v_r_5342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5343_, size_t v_i_5344_, lean_object* v_bs_5345_){
_start:
{
uint8_t v___x_5346_; 
v___x_5346_ = lean_usize_dec_lt(v_i_5344_, v_sz_5343_);
if (v___x_5346_ == 0)
{
return v_bs_5345_;
}
else
{
lean_object* v_v_5347_; lean_object* v___x_5348_; lean_object* v_bs_x27_5349_; lean_object* v___x_5350_; size_t v___x_5351_; size_t v___x_5352_; lean_object* v___x_5353_; 
v_v_5347_ = lean_array_uget(v_bs_5345_, v_i_5344_);
v___x_5348_ = lean_unsigned_to_nat(0u);
v_bs_x27_5349_ = lean_array_uset(v_bs_5345_, v_i_5344_, v___x_5348_);
v___x_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5350_, 0, v_v_5347_);
v___x_5351_ = ((size_t)1ULL);
v___x_5352_ = lean_usize_add(v_i_5344_, v___x_5351_);
v___x_5353_ = lean_array_uset(v_bs_x27_5349_, v_i_5344_, v___x_5350_);
v_i_5344_ = v___x_5352_;
v_bs_5345_ = v___x_5353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5355_, lean_object* v_i_5356_, lean_object* v_bs_5357_){
_start:
{
size_t v_sz_boxed_5358_; size_t v_i_boxed_5359_; lean_object* v_res_5360_; 
v_sz_boxed_5358_ = lean_unbox_usize(v_sz_5355_);
lean_dec(v_sz_5355_);
v_i_boxed_5359_ = lean_unbox_usize(v_i_5356_);
lean_dec(v_i_5356_);
v_res_5360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5358_, v_i_boxed_5359_, v_bs_5357_);
return v_res_5360_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5361_, lean_object* v_as_5362_, size_t v_i_5363_, size_t v_stop_5364_){
_start:
{
uint8_t v___x_5365_; 
v___x_5365_ = lean_usize_dec_eq(v_i_5363_, v_stop_5364_);
if (v___x_5365_ == 0)
{
lean_object* v_numFixed_5366_; uint8_t v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; size_t v_sz_5370_; size_t v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; uint8_t v___x_5379_; 
v_numFixed_5366_ = lean_ctor_get(v_fixedParamPerms_5361_, 0);
v___x_5367_ = 1;
v___x_5368_ = lean_array_uget_borrowed(v_as_5362_, v_i_5363_);
lean_inc(v_numFixed_5366_);
v___x_5369_ = l_Array_range(v_numFixed_5366_);
v_sz_5370_ = lean_array_size(v___x_5369_);
v___x_5371_ = ((size_t)0ULL);
v___x_5372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5370_, v___x_5371_, v___x_5369_);
v___x_5373_ = lean_array_get_size(v___x_5368_);
v___x_5374_ = lean_nat_sub(v___x_5373_, v_numFixed_5366_);
v___x_5375_ = lean_box(0);
v___x_5376_ = lean_mk_array(v___x_5374_, v___x_5375_);
v___x_5377_ = l_Array_append___redArg(v___x_5372_, v___x_5376_);
lean_dec_ref(v___x_5376_);
v___x_5378_ = lean_array_get_size(v___x_5377_);
v___x_5379_ = lean_nat_dec_eq(v___x_5373_, v___x_5378_);
if (v___x_5379_ == 0)
{
lean_dec_ref(v___x_5377_);
lean_dec_ref(v_fixedParamPerms_5361_);
return v___x_5367_;
}
else
{
uint8_t v___x_5380_; 
v___x_5380_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5368_, v___x_5377_, v___x_5373_);
lean_dec_ref(v___x_5377_);
if (v___x_5380_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5361_);
return v___x_5367_;
}
else
{
size_t v___x_5381_; size_t v___x_5382_; 
v___x_5381_ = ((size_t)1ULL);
v___x_5382_ = lean_usize_add(v_i_5363_, v___x_5381_);
v_i_5363_ = v___x_5382_;
goto _start;
}
}
}
else
{
uint8_t v___x_5384_; 
lean_dec_ref(v_fixedParamPerms_5361_);
v___x_5384_ = 0;
return v___x_5384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5385_, lean_object* v_as_5386_, lean_object* v_i_5387_, lean_object* v_stop_5388_){
_start:
{
size_t v_i_boxed_5389_; size_t v_stop_boxed_5390_; uint8_t v_res_5391_; lean_object* v_r_5392_; 
v_i_boxed_5389_ = lean_unbox_usize(v_i_5387_);
lean_dec(v_i_5387_);
v_stop_boxed_5390_ = lean_unbox_usize(v_stop_5388_);
lean_dec(v_stop_5388_);
v_res_5391_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5385_, v_as_5386_, v_i_boxed_5389_, v_stop_boxed_5390_);
lean_dec_ref(v_as_5386_);
v_r_5392_ = lean_box(v_res_5391_);
return v_r_5392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5393_){
_start:
{
lean_object* v_perms_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; uint8_t v___x_5397_; 
v_perms_5394_ = lean_ctor_get(v_fixedParamPerms_5393_, 1);
lean_inc_ref(v_perms_5394_);
v___x_5395_ = lean_unsigned_to_nat(0u);
v___x_5396_ = lean_array_get_size(v_perms_5394_);
v___x_5397_ = lean_nat_dec_lt(v___x_5395_, v___x_5396_);
if (v___x_5397_ == 0)
{
uint8_t v___x_5398_; 
lean_dec_ref(v_perms_5394_);
lean_dec_ref(v_fixedParamPerms_5393_);
v___x_5398_ = 1;
return v___x_5398_;
}
else
{
if (v___x_5397_ == 0)
{
lean_dec_ref(v_perms_5394_);
lean_dec_ref(v_fixedParamPerms_5393_);
return v___x_5397_;
}
else
{
size_t v___x_5399_; size_t v___x_5400_; uint8_t v___x_5401_; 
v___x_5399_ = ((size_t)0ULL);
v___x_5400_ = lean_usize_of_nat(v___x_5396_);
v___x_5401_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5393_, v_perms_5394_, v___x_5399_, v___x_5400_);
lean_dec_ref(v_perms_5394_);
if (v___x_5401_ == 0)
{
return v___x_5397_;
}
else
{
uint8_t v___x_5402_; 
v___x_5402_ = 0;
return v___x_5402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5403_){
_start:
{
uint8_t v_res_5404_; lean_object* v_r_5405_; 
v_res_5404_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5403_);
v_r_5405_ = lean_box(v_res_5404_);
return v_r_5405_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5406_, lean_object* v_ys_5407_, lean_object* v_hsz_5408_, lean_object* v_x_5409_, lean_object* v_x_5410_){
_start:
{
uint8_t v___x_5411_; 
v___x_5411_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5406_, v_ys_5407_, v_x_5409_);
return v___x_5411_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5412_, lean_object* v_ys_5413_, lean_object* v_hsz_5414_, lean_object* v_x_5415_, lean_object* v_x_5416_){
_start:
{
uint8_t v_res_5417_; lean_object* v_r_5418_; 
v_res_5417_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5412_, v_ys_5413_, v_hsz_5414_, v_x_5415_, v_x_5416_);
lean_dec_ref(v_ys_5413_);
lean_dec_ref(v_xs_5412_);
v_r_5418_ = lean_box(v_res_5417_);
return v_r_5418_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5419_; 
v___x_5419_ = l_Array_instInhabited(lean_box(0));
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5420_){
_start:
{
lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___f_5423_; lean_object* v___f_5424_; lean_object* v___f_5425_; lean_object* v___f_5426_; lean_object* v___f_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; 
v___f_5421_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5422_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5423_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5424_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5425_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5426_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5427_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5428_, 0, v___f_5421_);
lean_ctor_set(v___x_5428_, 1, v___f_5422_);
v___x_5429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5428_);
lean_ctor_set(v___x_5429_, 1, v___f_5423_);
lean_ctor_set(v___x_5429_, 2, v___f_5424_);
lean_ctor_set(v___x_5429_, 3, v___f_5425_);
lean_ctor_set(v___x_5429_, 4, v___f_5426_);
v___x_5430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5430_, 0, v___x_5429_);
lean_ctor_set(v___x_5430_, 1, v___f_5427_);
v___x_5431_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5432_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5432_);
lean_ctor_set(v___x_5433_, 1, v___x_5432_);
v___x_5434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5434_, 0, v___x_5431_);
lean_ctor_set(v___x_5434_, 1, v___x_5433_);
v___x_5435_ = l_instInhabitedOfMonad___redArg(v___x_5430_, v___x_5434_);
v___x_5436_ = lean_panic_fn_borrowed(v___x_5435_, v_msg_5420_);
lean_dec(v___x_5435_);
return v___x_5436_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5437_; 
v___x_5437_ = l_Array_instInhabited(lean_box(0));
return v___x_5437_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5438_){
_start:
{
lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___f_5441_; lean_object* v___f_5442_; lean_object* v___f_5443_; lean_object* v___f_5444_; lean_object* v___f_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; 
v___f_5439_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5440_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5441_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5442_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5443_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5444_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5445_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5446_, 0, v___f_5439_);
lean_ctor_set(v___x_5446_, 1, v___f_5440_);
v___x_5447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5447_, 0, v___x_5446_);
lean_ctor_set(v___x_5447_, 1, v___f_5441_);
lean_ctor_set(v___x_5447_, 2, v___f_5442_);
lean_ctor_set(v___x_5447_, 3, v___f_5443_);
lean_ctor_set(v___x_5447_, 4, v___f_5444_);
v___x_5448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5448_, 0, v___x_5447_);
lean_ctor_set(v___x_5448_, 1, v___f_5445_);
v___x_5449_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5450_, 0, v___x_5449_);
v___x_5451_ = l_instInhabitedOfMonad___redArg(v___x_5448_, v___x_5450_);
v___x_5452_ = lean_panic_fn_borrowed(v___x_5451_, v_msg_5438_);
lean_dec(v___x_5451_);
return v___x_5452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5453_, uint8_t v___x_5454_, lean_object* v___x_5455_, lean_object* v___x_5456_, lean_object* v_as_5457_, size_t v_sz_5458_, size_t v_i_5459_, lean_object* v_b_5460_){
_start:
{
lean_object* v_a_5462_; uint8_t v___x_5466_; 
v___x_5466_ = lean_usize_dec_lt(v_i_5459_, v_sz_5458_);
if (v___x_5466_ == 0)
{
return v_b_5460_;
}
else
{
lean_object* v_fst_5467_; lean_object* v_snd_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5490_; 
v_fst_5467_ = lean_ctor_get(v_b_5460_, 0);
v_snd_5468_ = lean_ctor_get(v_b_5460_, 1);
v_isSharedCheck_5490_ = !lean_is_exclusive(v_b_5460_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5470_ = v_b_5460_;
v_isShared_5471_ = v_isSharedCheck_5490_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_snd_5468_);
lean_inc(v_fst_5467_);
lean_dec(v_b_5460_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5490_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5476_; lean_object* v_a_5477_; lean_object* v___x_5478_; 
v___x_5476_ = lean_box(0);
v_a_5477_ = lean_array_uget_borrowed(v_as_5457_, v_i_5459_);
v___x_5478_ = lean_array_get_borrowed(v___x_5476_, v___x_5453_, v_a_5477_);
if (lean_obj_tag(v___x_5478_) == 1)
{
lean_object* v_val_5479_; uint8_t v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; uint8_t v___x_5483_; 
v_val_5479_ = lean_ctor_get(v___x_5478_, 0);
v___x_5480_ = 0;
v___x_5481_ = lean_box(v___x_5480_);
v___x_5482_ = lean_array_get(v___x_5481_, v_fst_5467_, v_val_5479_);
lean_dec(v___x_5481_);
v___x_5483_ = lean_unbox(v___x_5482_);
lean_dec(v___x_5482_);
if (v___x_5483_ == 0)
{
if (v___x_5454_ == 0)
{
goto v___jp_5472_;
}
else
{
uint8_t v_changed_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; 
lean_del_object(v___x_5470_);
lean_dec(v_snd_5468_);
v_changed_5484_ = lean_nat_dec_eq(v___x_5455_, v___x_5456_);
v___x_5485_ = lean_box(v_changed_5484_);
v___x_5486_ = lean_array_set(v_fst_5467_, v_val_5479_, v___x_5485_);
v___x_5487_ = lean_box(v_changed_5484_);
v___x_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5488_, 0, v___x_5486_);
lean_ctor_set(v___x_5488_, 1, v___x_5487_);
v_a_5462_ = v___x_5488_;
goto v___jp_5461_;
}
}
else
{
goto v___jp_5472_;
}
}
else
{
lean_object* v___x_5489_; 
lean_del_object(v___x_5470_);
v___x_5489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5489_, 0, v_fst_5467_);
lean_ctor_set(v___x_5489_, 1, v_snd_5468_);
v_a_5462_ = v___x_5489_;
goto v___jp_5461_;
}
v___jp_5472_:
{
lean_object* v___x_5474_; 
if (v_isShared_5471_ == 0)
{
v___x_5474_ = v___x_5470_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_fst_5467_);
lean_ctor_set(v_reuseFailAlloc_5475_, 1, v_snd_5468_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
v_a_5462_ = v___x_5474_;
goto v___jp_5461_;
}
}
}
}
v___jp_5461_:
{
size_t v___x_5463_; size_t v___x_5464_; 
v___x_5463_ = ((size_t)1ULL);
v___x_5464_ = lean_usize_add(v_i_5459_, v___x_5463_);
v_i_5459_ = v___x_5464_;
v_b_5460_ = v_a_5462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5491_, lean_object* v___x_5492_, lean_object* v___x_5493_, lean_object* v___x_5494_, lean_object* v_as_5495_, lean_object* v_sz_5496_, lean_object* v_i_5497_, lean_object* v_b_5498_){
_start:
{
uint8_t v___x_6987__boxed_5499_; size_t v_sz_boxed_5500_; size_t v_i_boxed_5501_; lean_object* v_res_5502_; 
v___x_6987__boxed_5499_ = lean_unbox(v___x_5492_);
v_sz_boxed_5500_ = lean_unbox_usize(v_sz_5496_);
lean_dec(v_sz_5496_);
v_i_boxed_5501_ = lean_unbox_usize(v_i_5497_);
lean_dec(v_i_5497_);
v_res_5502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5491_, v___x_6987__boxed_5499_, v___x_5493_, v___x_5494_, v_as_5495_, v_sz_boxed_5500_, v_i_boxed_5501_, v_b_5498_);
lean_dec_ref(v_as_5495_);
lean_dec(v___x_5494_);
lean_dec(v___x_5493_);
lean_dec_ref(v___x_5491_);
return v_res_5502_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5503_; 
v___x_5503_ = l_Array_instInhabited(lean_box(0));
return v___x_5503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object* v_upperBound_5504_, lean_object* v___x_5505_, lean_object* v_fixedParamPerms_5506_, lean_object* v_next_5507_, lean_object* v___x_5508_, lean_object* v___x_5509_, lean_object* v_a_5510_, lean_object* v_b_5511_){
_start:
{
lean_object* v_a_5513_; uint8_t v___x_5517_; 
v___x_5517_ = lean_nat_dec_lt(v_a_5510_, v_upperBound_5504_);
if (v___x_5517_ == 0)
{
lean_dec(v_a_5510_);
return v_b_5511_;
}
else
{
lean_object* v_fst_5518_; lean_object* v_snd_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5555_; 
v_fst_5518_ = lean_ctor_get(v_b_5511_, 0);
v_snd_5519_ = lean_ctor_get(v_b_5511_, 1);
v_isSharedCheck_5555_ = !lean_is_exclusive(v_b_5511_);
if (v_isSharedCheck_5555_ == 0)
{
v___x_5521_ = v_b_5511_;
v_isShared_5522_ = v_isSharedCheck_5555_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_snd_5519_);
lean_inc(v_fst_5518_);
lean_dec(v_b_5511_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5555_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5523_; 
v___x_5523_ = lean_array_fget_borrowed(v___x_5505_, v_a_5510_);
if (lean_obj_tag(v___x_5523_) == 1)
{
lean_object* v_val_5524_; uint8_t v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; uint8_t v___x_5528_; 
v_val_5524_ = lean_ctor_get(v___x_5523_, 0);
v___x_5525_ = 0;
v___x_5526_ = lean_box(v___x_5525_);
v___x_5527_ = lean_array_get(v___x_5526_, v_fst_5518_, v_val_5524_);
lean_dec(v___x_5526_);
v___x_5528_ = lean_unbox(v___x_5527_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5530_; 
lean_dec(v___x_5527_);
if (v_isShared_5522_ == 0)
{
v___x_5530_ = v___x_5521_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_fst_5518_);
lean_ctor_set(v_reuseFailAlloc_5531_, 1, v_snd_5519_);
v___x_5530_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
v_a_5513_ = v___x_5530_;
goto v___jp_5512_;
}
}
else
{
lean_object* v_revDeps_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5537_; 
v_revDeps_5532_ = lean_ctor_get(v_fixedParamPerms_5506_, 2);
v___x_5533_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0);
v___x_5534_ = lean_array_get_borrowed(v___x_5533_, v_revDeps_5532_, v_next_5507_);
v___x_5535_ = lean_array_get_borrowed(v___x_5533_, v___x_5534_, v_a_5510_);
if (v_isShared_5522_ == 0)
{
v___x_5537_ = v___x_5521_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_fst_5518_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v_snd_5519_);
v___x_5537_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
size_t v_sz_5538_; size_t v___x_5539_; uint8_t v___x_5540_; lean_object* v___x_5541_; lean_object* v_fst_5542_; lean_object* v_snd_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5550_; 
v_sz_5538_ = lean_array_size(v___x_5535_);
v___x_5539_ = ((size_t)0ULL);
v___x_5540_ = lean_unbox(v___x_5527_);
lean_dec(v___x_5527_);
v___x_5541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5505_, v___x_5540_, v___x_5508_, v___x_5509_, v___x_5535_, v_sz_5538_, v___x_5539_, v___x_5537_);
v_fst_5542_ = lean_ctor_get(v___x_5541_, 0);
v_snd_5543_ = lean_ctor_get(v___x_5541_, 1);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5550_ == 0)
{
v___x_5545_ = v___x_5541_;
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_snd_5543_);
lean_inc(v_fst_5542_);
lean_dec(v___x_5541_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5548_; 
if (v_isShared_5546_ == 0)
{
v___x_5548_ = v___x_5545_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_fst_5542_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v_snd_5543_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
v_a_5513_ = v___x_5548_;
goto v___jp_5512_;
}
}
}
}
}
else
{
lean_object* v___x_5553_; 
if (v_isShared_5522_ == 0)
{
v___x_5553_ = v___x_5521_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_fst_5518_);
lean_ctor_set(v_reuseFailAlloc_5554_, 1, v_snd_5519_);
v___x_5553_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
v_a_5513_ = v___x_5553_;
goto v___jp_5512_;
}
}
}
}
v___jp_5512_:
{
lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5514_ = lean_unsigned_to_nat(1u);
v___x_5515_ = lean_nat_add(v_a_5510_, v___x_5514_);
lean_dec(v_a_5510_);
v_a_5510_ = v___x_5515_;
v_b_5511_ = v_a_5513_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object* v_upperBound_5556_, lean_object* v___x_5557_, lean_object* v_fixedParamPerms_5558_, lean_object* v_next_5559_, lean_object* v___x_5560_, lean_object* v___x_5561_, lean_object* v_a_5562_, lean_object* v_b_5563_){
_start:
{
lean_object* v_res_5564_; 
v_res_5564_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5556_, v___x_5557_, v_fixedParamPerms_5558_, v_next_5559_, v___x_5560_, v___x_5561_, v_a_5562_, v_b_5563_);
lean_dec(v___x_5561_);
lean_dec(v___x_5560_);
lean_dec(v_next_5559_);
lean_dec_ref(v_fixedParamPerms_5558_);
lean_dec_ref(v___x_5557_);
lean_dec(v_upperBound_5556_);
return v_res_5564_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5565_, lean_object* v___x_5566_, lean_object* v___x_5567_, lean_object* v___x_5568_, lean_object* v_fixedParamPerms_5569_, lean_object* v_next_5570_, lean_object* v_a_5571_, lean_object* v_b_5572_){
_start:
{
lean_object* v_a_5574_; uint8_t v___x_5578_; 
v___x_5578_ = lean_nat_dec_lt(v_a_5571_, v_upperBound_5565_);
if (v___x_5578_ == 0)
{
return v_b_5572_;
}
else
{
lean_object* v_fst_5579_; lean_object* v_snd_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5616_; 
v_fst_5579_ = lean_ctor_get(v_b_5572_, 0);
v_snd_5580_ = lean_ctor_get(v_b_5572_, 1);
v_isSharedCheck_5616_ = !lean_is_exclusive(v_b_5572_);
if (v_isSharedCheck_5616_ == 0)
{
v___x_5582_ = v_b_5572_;
v_isShared_5583_ = v_isSharedCheck_5616_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_snd_5580_);
lean_inc(v_fst_5579_);
lean_dec(v_b_5572_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5616_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5584_; 
v___x_5584_ = lean_array_fget_borrowed(v___x_5566_, v_a_5571_);
if (lean_obj_tag(v___x_5584_) == 1)
{
lean_object* v_val_5585_; uint8_t v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; uint8_t v___x_5589_; 
v_val_5585_ = lean_ctor_get(v___x_5584_, 0);
v___x_5586_ = 0;
v___x_5587_ = lean_box(v___x_5586_);
v___x_5588_ = lean_array_get(v___x_5587_, v_fst_5579_, v_val_5585_);
lean_dec(v___x_5587_);
v___x_5589_ = lean_unbox(v___x_5588_);
if (v___x_5589_ == 0)
{
lean_object* v___x_5591_; 
lean_dec(v___x_5588_);
if (v_isShared_5583_ == 0)
{
v___x_5591_ = v___x_5582_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_fst_5579_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v_snd_5580_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
v_a_5574_ = v___x_5591_;
goto v___jp_5573_;
}
}
else
{
lean_object* v_revDeps_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5598_; 
v_revDeps_5593_ = lean_ctor_get(v_fixedParamPerms_5569_, 2);
v___x_5594_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0);
v___x_5595_ = lean_array_get_borrowed(v___x_5594_, v_revDeps_5593_, v_next_5570_);
v___x_5596_ = lean_array_get_borrowed(v___x_5594_, v___x_5595_, v_a_5571_);
if (v_isShared_5583_ == 0)
{
v___x_5598_ = v___x_5582_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_fst_5579_);
lean_ctor_set(v_reuseFailAlloc_5612_, 1, v_snd_5580_);
v___x_5598_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
size_t v_sz_5599_; size_t v___x_5600_; uint8_t v___x_5601_; lean_object* v___x_5602_; lean_object* v_fst_5603_; lean_object* v_snd_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5611_; 
v_sz_5599_ = lean_array_size(v___x_5596_);
v___x_5600_ = ((size_t)0ULL);
v___x_5601_ = lean_unbox(v___x_5588_);
lean_dec(v___x_5588_);
v___x_5602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5566_, v___x_5601_, v___x_5567_, v___x_5568_, v___x_5596_, v_sz_5599_, v___x_5600_, v___x_5598_);
v_fst_5603_ = lean_ctor_get(v___x_5602_, 0);
v_snd_5604_ = lean_ctor_get(v___x_5602_, 1);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5602_);
if (v_isSharedCheck_5611_ == 0)
{
v___x_5606_ = v___x_5602_;
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_snd_5604_);
lean_inc(v_fst_5603_);
lean_dec(v___x_5602_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5611_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v___x_5609_; 
if (v_isShared_5607_ == 0)
{
v___x_5609_ = v___x_5606_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_fst_5603_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v_snd_5604_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
v_a_5574_ = v___x_5609_;
goto v___jp_5573_;
}
}
}
}
}
else
{
lean_object* v___x_5614_; 
if (v_isShared_5583_ == 0)
{
v___x_5614_ = v___x_5582_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5615_; 
v_reuseFailAlloc_5615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5615_, 0, v_fst_5579_);
lean_ctor_set(v_reuseFailAlloc_5615_, 1, v_snd_5580_);
v___x_5614_ = v_reuseFailAlloc_5615_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
v_a_5574_ = v___x_5614_;
goto v___jp_5573_;
}
}
}
}
v___jp_5573_:
{
lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; 
v___x_5575_ = lean_unsigned_to_nat(1u);
v___x_5576_ = lean_nat_add(v_a_5571_, v___x_5575_);
v___x_5577_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5565_, v___x_5566_, v_fixedParamPerms_5569_, v_next_5570_, v___x_5567_, v___x_5568_, v___x_5576_, v_a_5574_);
return v___x_5577_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5617_, lean_object* v___x_5618_, lean_object* v___x_5619_, lean_object* v___x_5620_, lean_object* v_fixedParamPerms_5621_, lean_object* v_next_5622_, lean_object* v_a_5623_, lean_object* v_b_5624_){
_start:
{
lean_object* v_res_5625_; 
v_res_5625_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5617_, v___x_5618_, v___x_5619_, v___x_5620_, v_fixedParamPerms_5621_, v_next_5622_, v_a_5623_, v_b_5624_);
lean_dec(v_a_5623_);
lean_dec(v_next_5622_);
lean_dec_ref(v_fixedParamPerms_5621_);
lean_dec(v___x_5620_);
lean_dec(v___x_5619_);
lean_dec_ref(v___x_5618_);
lean_dec(v_upperBound_5617_);
return v_res_5625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5626_, lean_object* v___x_5627_, lean_object* v___x_5628_, lean_object* v___x_5629_, lean_object* v_fixedParamPerms_5630_, lean_object* v_a_5631_, lean_object* v_b_5632_){
_start:
{
uint8_t v___x_5633_; 
v___x_5633_ = lean_nat_dec_lt(v_a_5631_, v_upperBound_5626_);
if (v___x_5633_ == 0)
{
lean_dec(v_a_5631_);
return v_b_5632_;
}
else
{
lean_object* v_fst_5634_; lean_object* v_snd_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5658_; 
v_fst_5634_ = lean_ctor_get(v_b_5632_, 0);
v_snd_5635_ = lean_ctor_get(v_b_5632_, 1);
v_isSharedCheck_5658_ = !lean_is_exclusive(v_b_5632_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5637_ = v_b_5632_;
v_isShared_5638_ = v_isSharedCheck_5658_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_snd_5635_);
lean_inc(v_fst_5634_);
lean_dec(v_b_5632_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5658_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5643_; 
v___x_5639_ = lean_array_fget_borrowed(v___x_5627_, v_a_5631_);
v___x_5640_ = lean_array_get_size(v___x_5639_);
v___x_5641_ = lean_unsigned_to_nat(0u);
if (v_isShared_5638_ == 0)
{
v___x_5643_ = v___x_5637_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_fst_5634_);
lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_snd_5635_);
v___x_5643_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
lean_object* v___x_5644_; lean_object* v_fst_5645_; lean_object* v_snd_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5656_; 
v___x_5644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5640_, v___x_5639_, v___x_5628_, v___x_5629_, v_fixedParamPerms_5630_, v_a_5631_, v___x_5641_, v___x_5643_);
v_fst_5645_ = lean_ctor_get(v___x_5644_, 0);
v_snd_5646_ = lean_ctor_get(v___x_5644_, 1);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5644_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5648_ = v___x_5644_;
v_isShared_5649_ = v_isSharedCheck_5656_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_snd_5646_);
lean_inc(v_fst_5645_);
lean_dec(v___x_5644_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5656_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5651_; 
if (v_isShared_5649_ == 0)
{
v___x_5651_ = v___x_5648_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_fst_5645_);
lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_snd_5646_);
v___x_5651_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
lean_object* v___x_5652_; lean_object* v___x_5653_; 
v___x_5652_ = lean_unsigned_to_nat(1u);
v___x_5653_ = lean_nat_add(v_a_5631_, v___x_5652_);
lean_dec(v_a_5631_);
v_a_5631_ = v___x_5653_;
v_b_5632_ = v___x_5651_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5659_, lean_object* v___x_5660_, lean_object* v___x_5661_, lean_object* v___x_5662_, lean_object* v_fixedParamPerms_5663_, lean_object* v_a_5664_, lean_object* v_b_5665_){
_start:
{
lean_object* v_res_5666_; 
v_res_5666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5659_, v___x_5660_, v___x_5661_, v___x_5662_, v_fixedParamPerms_5663_, v_a_5664_, v_b_5665_);
lean_dec_ref(v_fixedParamPerms_5663_);
lean_dec(v___x_5662_);
lean_dec(v___x_5661_);
lean_dec_ref(v___x_5660_);
lean_dec(v_upperBound_5659_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5667_, lean_object* v___x_5668_, lean_object* v___x_5669_, lean_object* v_fixedParamPerms_5670_, lean_object* v_a_5671_){
_start:
{
lean_object* v_snd_5672_; uint8_t v___x_5673_; 
v_snd_5672_ = lean_ctor_get(v_a_5671_, 1);
v___x_5673_ = lean_unbox(v_snd_5672_);
if (v___x_5673_ == 0)
{
lean_object* v_fst_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_inc(v_snd_5672_);
v_fst_5674_ = lean_ctor_get(v_a_5671_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v_a_5671_);
if (v_isSharedCheck_5681_ == 0)
{
lean_object* v_unused_5682_; 
v_unused_5682_ = lean_ctor_get(v_a_5671_, 1);
lean_dec(v_unused_5682_);
v___x_5676_ = v_a_5671_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_fst_5674_);
lean_dec(v_a_5671_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_fst_5674_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v_snd_5672_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
else
{
lean_object* v_fst_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5704_; 
v_fst_5683_ = lean_ctor_get(v_a_5671_, 0);
v_isSharedCheck_5704_ = !lean_is_exclusive(v_a_5671_);
if (v_isSharedCheck_5704_ == 0)
{
lean_object* v_unused_5705_; 
v_unused_5705_ = lean_ctor_get(v_a_5671_, 1);
lean_dec(v_unused_5705_);
v___x_5685_ = v_a_5671_;
v_isShared_5686_ = v_isSharedCheck_5704_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_fst_5683_);
lean_dec(v_a_5671_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5704_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
uint8_t v_changed_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5691_; 
v_changed_5687_ = 0;
v___x_5688_ = lean_unsigned_to_nat(0u);
v___x_5689_ = lean_box(v_changed_5687_);
if (v_isShared_5686_ == 0)
{
lean_ctor_set(v___x_5685_, 1, v___x_5689_);
v___x_5691_ = v___x_5685_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_fst_5683_);
lean_ctor_set(v_reuseFailAlloc_5703_, 1, v___x_5689_);
v___x_5691_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
lean_object* v___x_5692_; lean_object* v_fst_5693_; lean_object* v_snd_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5702_; 
v___x_5692_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5667_, v___x_5668_, v___x_5669_, v___x_5667_, v_fixedParamPerms_5670_, v___x_5688_, v___x_5691_);
v_fst_5693_ = lean_ctor_get(v___x_5692_, 0);
v_snd_5694_ = lean_ctor_get(v___x_5692_, 1);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5692_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5696_ = v___x_5692_;
v_isShared_5697_ = v_isSharedCheck_5702_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_snd_5694_);
lean_inc(v_fst_5693_);
lean_dec(v___x_5692_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5702_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5699_; 
if (v_isShared_5697_ == 0)
{
v___x_5699_ = v___x_5696_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_fst_5693_);
lean_ctor_set(v_reuseFailAlloc_5701_, 1, v_snd_5694_);
v___x_5699_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
v_a_5671_ = v___x_5699_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5706_, lean_object* v___x_5707_, lean_object* v___x_5708_, lean_object* v_fixedParamPerms_5709_, lean_object* v_a_5710_){
_start:
{
lean_object* v_res_5711_; 
v_res_5711_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5706_, v___x_5707_, v___x_5708_, v_fixedParamPerms_5709_, v_a_5710_);
lean_dec_ref(v_fixedParamPerms_5709_);
lean_dec(v___x_5708_);
lean_dec_ref(v___x_5707_);
lean_dec(v___x_5706_);
return v_res_5711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5712_, lean_object* v_a_5713_, lean_object* v_b_5714_){
_start:
{
lean_object* v_a_5716_; uint8_t v___x_5720_; 
v___x_5720_ = lean_nat_dec_lt(v_a_5713_, v_upperBound_5712_);
if (v___x_5720_ == 0)
{
lean_dec(v_a_5713_);
return v_b_5714_;
}
else
{
lean_object* v_snd_5721_; lean_object* v_snd_5722_; lean_object* v_snd_5723_; lean_object* v_snd_5724_; lean_object* v_fst_5725_; lean_object* v___x_5727_; uint8_t v_isShared_5728_; uint8_t v_isSharedCheck_5837_; 
v_snd_5721_ = lean_ctor_get(v_b_5714_, 1);
lean_inc(v_snd_5721_);
v_snd_5722_ = lean_ctor_get(v_snd_5721_, 1);
lean_inc(v_snd_5722_);
v_snd_5723_ = lean_ctor_get(v_snd_5722_, 1);
lean_inc(v_snd_5723_);
v_snd_5724_ = lean_ctor_get(v_snd_5723_, 1);
lean_inc(v_snd_5724_);
v_fst_5725_ = lean_ctor_get(v_b_5714_, 0);
v_isSharedCheck_5837_ = !lean_is_exclusive(v_b_5714_);
if (v_isSharedCheck_5837_ == 0)
{
lean_object* v_unused_5838_; 
v_unused_5838_ = lean_ctor_get(v_b_5714_, 1);
lean_dec(v_unused_5838_);
v___x_5727_ = v_b_5714_;
v_isShared_5728_ = v_isSharedCheck_5837_;
goto v_resetjp_5726_;
}
else
{
lean_inc(v_fst_5725_);
lean_dec(v_b_5714_);
v___x_5727_ = lean_box(0);
v_isShared_5728_ = v_isSharedCheck_5837_;
goto v_resetjp_5726_;
}
v_resetjp_5726_:
{
lean_object* v_fst_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5835_; 
v_fst_5729_ = lean_ctor_get(v_snd_5721_, 0);
v_isSharedCheck_5835_ = !lean_is_exclusive(v_snd_5721_);
if (v_isSharedCheck_5835_ == 0)
{
lean_object* v_unused_5836_; 
v_unused_5836_ = lean_ctor_get(v_snd_5721_, 1);
lean_dec(v_unused_5836_);
v___x_5731_ = v_snd_5721_;
v_isShared_5732_ = v_isSharedCheck_5835_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_fst_5729_);
lean_dec(v_snd_5721_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5835_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v_fst_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5833_; 
v_fst_5733_ = lean_ctor_get(v_snd_5722_, 0);
v_isSharedCheck_5833_ = !lean_is_exclusive(v_snd_5722_);
if (v_isSharedCheck_5833_ == 0)
{
lean_object* v_unused_5834_; 
v_unused_5834_ = lean_ctor_get(v_snd_5722_, 1);
lean_dec(v_unused_5834_);
v___x_5735_ = v_snd_5722_;
v_isShared_5736_ = v_isSharedCheck_5833_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_fst_5733_);
lean_dec(v_snd_5722_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5833_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v_fst_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5831_; 
v_fst_5737_ = lean_ctor_get(v_snd_5723_, 0);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_snd_5723_);
if (v_isSharedCheck_5831_ == 0)
{
lean_object* v_unused_5832_; 
v_unused_5832_ = lean_ctor_get(v_snd_5723_, 1);
lean_dec(v_unused_5832_);
v___x_5739_ = v_snd_5723_;
v_isShared_5740_ = v_isSharedCheck_5831_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_fst_5737_);
lean_dec(v_snd_5723_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5831_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v_array_5741_; lean_object* v_start_5742_; lean_object* v_stop_5743_; uint8_t v___x_5744_; 
v_array_5741_ = lean_ctor_get(v_snd_5724_, 0);
v_start_5742_ = lean_ctor_get(v_snd_5724_, 1);
v_stop_5743_ = lean_ctor_get(v_snd_5724_, 2);
v___x_5744_ = lean_nat_dec_lt(v_start_5742_, v_stop_5743_);
if (v___x_5744_ == 0)
{
lean_object* v___x_5746_; 
lean_dec(v_a_5713_);
if (v_isShared_5740_ == 0)
{
v___x_5746_ = v___x_5739_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_fst_5737_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v_snd_5724_);
v___x_5746_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
lean_object* v___x_5748_; 
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5746_);
v___x_5748_ = v___x_5735_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_fst_5733_);
lean_ctor_set(v_reuseFailAlloc_5755_, 1, v___x_5746_);
v___x_5748_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
lean_object* v___x_5750_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5748_);
v___x_5750_ = v___x_5731_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_fst_5729_);
lean_ctor_set(v_reuseFailAlloc_5754_, 1, v___x_5748_);
v___x_5750_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
lean_object* v___x_5752_; 
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5750_);
v___x_5752_ = v___x_5727_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v_fst_5725_);
lean_ctor_set(v_reuseFailAlloc_5753_, 1, v___x_5750_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
}
}
}
else
{
lean_object* v___x_5758_; uint8_t v_isShared_5759_; uint8_t v_isSharedCheck_5827_; 
lean_inc(v_stop_5743_);
lean_inc(v_start_5742_);
lean_inc_ref(v_array_5741_);
v_isSharedCheck_5827_ = !lean_is_exclusive(v_snd_5724_);
if (v_isSharedCheck_5827_ == 0)
{
lean_object* v_unused_5828_; lean_object* v_unused_5829_; lean_object* v_unused_5830_; 
v_unused_5828_ = lean_ctor_get(v_snd_5724_, 2);
lean_dec(v_unused_5828_);
v_unused_5829_ = lean_ctor_get(v_snd_5724_, 1);
lean_dec(v_unused_5829_);
v_unused_5830_ = lean_ctor_get(v_snd_5724_, 0);
lean_dec(v_unused_5830_);
v___x_5758_ = v_snd_5724_;
v_isShared_5759_ = v_isSharedCheck_5827_;
goto v_resetjp_5757_;
}
else
{
lean_dec(v_snd_5724_);
v___x_5758_ = lean_box(0);
v_isShared_5759_ = v_isSharedCheck_5827_;
goto v_resetjp_5757_;
}
v_resetjp_5757_:
{
lean_object* v_array_5760_; lean_object* v_start_5761_; lean_object* v_stop_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5767_; 
v_array_5760_ = lean_ctor_get(v_fst_5737_, 0);
v_start_5761_ = lean_ctor_get(v_fst_5737_, 1);
v_stop_5762_ = lean_ctor_get(v_fst_5737_, 2);
v___x_5763_ = lean_array_fget(v_array_5741_, v_start_5742_);
v___x_5764_ = lean_unsigned_to_nat(1u);
v___x_5765_ = lean_nat_add(v_start_5742_, v___x_5764_);
lean_dec(v_start_5742_);
if (v_isShared_5759_ == 0)
{
lean_ctor_set(v___x_5758_, 1, v___x_5765_);
v___x_5767_ = v___x_5758_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v_array_5741_);
lean_ctor_set(v_reuseFailAlloc_5826_, 1, v___x_5765_);
lean_ctor_set(v_reuseFailAlloc_5826_, 2, v_stop_5743_);
v___x_5767_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
uint8_t v___x_5768_; 
v___x_5768_ = lean_nat_dec_lt(v_start_5761_, v_stop_5762_);
if (v___x_5768_ == 0)
{
lean_object* v___x_5770_; 
lean_dec(v___x_5763_);
lean_dec(v_a_5713_);
if (v_isShared_5740_ == 0)
{
lean_ctor_set(v___x_5739_, 1, v___x_5767_);
v___x_5770_ = v___x_5739_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_fst_5737_);
lean_ctor_set(v_reuseFailAlloc_5780_, 1, v___x_5767_);
v___x_5770_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
lean_object* v___x_5772_; 
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5770_);
v___x_5772_ = v___x_5735_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_fst_5733_);
lean_ctor_set(v_reuseFailAlloc_5779_, 1, v___x_5770_);
v___x_5772_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
lean_object* v___x_5774_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5772_);
v___x_5774_ = v___x_5731_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_fst_5729_);
lean_ctor_set(v_reuseFailAlloc_5778_, 1, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
lean_object* v___x_5776_; 
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5774_);
v___x_5776_ = v___x_5727_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_fst_5725_);
lean_ctor_set(v_reuseFailAlloc_5777_, 1, v___x_5774_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
}
}
else
{
lean_object* v___x_5782_; uint8_t v_isShared_5783_; uint8_t v_isSharedCheck_5822_; 
lean_inc(v_stop_5762_);
lean_inc(v_start_5761_);
lean_inc_ref(v_array_5760_);
v_isSharedCheck_5822_ = !lean_is_exclusive(v_fst_5737_);
if (v_isSharedCheck_5822_ == 0)
{
lean_object* v_unused_5823_; lean_object* v_unused_5824_; lean_object* v_unused_5825_; 
v_unused_5823_ = lean_ctor_get(v_fst_5737_, 2);
lean_dec(v_unused_5823_);
v_unused_5824_ = lean_ctor_get(v_fst_5737_, 1);
lean_dec(v_unused_5824_);
v_unused_5825_ = lean_ctor_get(v_fst_5737_, 0);
lean_dec(v_unused_5825_);
v___x_5782_ = v_fst_5737_;
v_isShared_5783_ = v_isSharedCheck_5822_;
goto v_resetjp_5781_;
}
else
{
lean_dec(v_fst_5737_);
v___x_5782_ = lean_box(0);
v_isShared_5783_ = v_isSharedCheck_5822_;
goto v_resetjp_5781_;
}
v_resetjp_5781_:
{
lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5787_; 
v___x_5784_ = lean_array_fget(v_array_5760_, v_start_5761_);
v___x_5785_ = lean_nat_add(v_start_5761_, v___x_5764_);
lean_dec(v_start_5761_);
if (v_isShared_5783_ == 0)
{
lean_ctor_set(v___x_5782_, 1, v___x_5785_);
v___x_5787_ = v___x_5782_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_array_5760_);
lean_ctor_set(v_reuseFailAlloc_5821_, 1, v___x_5785_);
lean_ctor_set(v_reuseFailAlloc_5821_, 2, v_stop_5762_);
v___x_5787_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
uint8_t v___x_5788_; 
v___x_5788_ = lean_unbox(v___x_5784_);
lean_dec(v___x_5784_);
if (v___x_5788_ == 0)
{
lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5794_; 
v___x_5789_ = lean_array_get_size(v_fst_5733_);
v___x_5790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5790_, 0, v___x_5789_);
v___x_5791_ = lean_array_push(v_fst_5725_, v___x_5790_);
v___x_5792_ = lean_array_push(v_fst_5733_, v___x_5763_);
if (v_isShared_5740_ == 0)
{
lean_ctor_set(v___x_5739_, 1, v___x_5767_);
lean_ctor_set(v___x_5739_, 0, v___x_5787_);
v___x_5794_ = v___x_5739_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5804_; 
v_reuseFailAlloc_5804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5804_, 0, v___x_5787_);
lean_ctor_set(v_reuseFailAlloc_5804_, 1, v___x_5767_);
v___x_5794_ = v_reuseFailAlloc_5804_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
lean_object* v___x_5796_; 
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5794_);
lean_ctor_set(v___x_5735_, 0, v___x_5792_);
v___x_5796_ = v___x_5735_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5792_);
lean_ctor_set(v_reuseFailAlloc_5803_, 1, v___x_5794_);
v___x_5796_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
lean_object* v___x_5798_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5796_);
v___x_5798_ = v___x_5731_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_fst_5729_);
lean_ctor_set(v_reuseFailAlloc_5802_, 1, v___x_5796_);
v___x_5798_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
lean_object* v___x_5800_; 
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5798_);
lean_ctor_set(v___x_5727_, 0, v___x_5791_);
v___x_5800_ = v___x_5727_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5791_);
lean_ctor_set(v_reuseFailAlloc_5801_, 1, v___x_5798_);
v___x_5800_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
v_a_5716_ = v___x_5800_;
goto v___jp_5715_;
}
}
}
}
}
else
{
lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5810_; 
v___x_5805_ = lean_box(0);
v___x_5806_ = lean_array_push(v_fst_5725_, v___x_5805_);
v___x_5807_ = l_Lean_Expr_fvarId_x21(v___x_5763_);
lean_dec(v___x_5763_);
v___x_5808_ = lean_array_push(v_fst_5729_, v___x_5807_);
if (v_isShared_5740_ == 0)
{
lean_ctor_set(v___x_5739_, 1, v___x_5767_);
lean_ctor_set(v___x_5739_, 0, v___x_5787_);
v___x_5810_ = v___x_5739_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v___x_5787_);
lean_ctor_set(v_reuseFailAlloc_5820_, 1, v___x_5767_);
v___x_5810_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
lean_object* v___x_5812_; 
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5810_);
v___x_5812_ = v___x_5735_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_fst_5733_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v___x_5810_);
v___x_5812_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
lean_object* v___x_5814_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5812_);
lean_ctor_set(v___x_5731_, 0, v___x_5808_);
v___x_5814_ = v___x_5731_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v___x_5808_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v___x_5812_);
v___x_5814_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
lean_object* v___x_5816_; 
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5814_);
lean_ctor_set(v___x_5727_, 0, v___x_5806_);
v___x_5816_ = v___x_5727_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v___x_5806_);
lean_ctor_set(v_reuseFailAlloc_5817_, 1, v___x_5814_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
v_a_5716_ = v___x_5816_;
goto v___jp_5715_;
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
v___jp_5715_:
{
lean_object* v___x_5717_; lean_object* v___x_5718_; 
v___x_5717_ = lean_unsigned_to_nat(1u);
v___x_5718_ = lean_nat_add(v_a_5713_, v___x_5717_);
lean_dec(v_a_5713_);
v_a_5713_ = v___x_5718_;
v_b_5714_ = v_a_5716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5839_, lean_object* v_a_5840_, lean_object* v_b_5841_){
_start:
{
lean_object* v_res_5842_; 
v_res_5842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5839_, v_a_5840_, v_b_5841_);
lean_dec(v_upperBound_5839_);
return v_res_5842_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5843_, size_t v_i_5844_, size_t v_stop_5845_){
_start:
{
uint8_t v___x_5846_; 
v___x_5846_ = lean_usize_dec_eq(v_i_5844_, v_stop_5845_);
if (v___x_5846_ == 0)
{
lean_object* v___x_5847_; uint8_t v___x_5848_; 
v___x_5847_ = lean_array_uget_borrowed(v_as_5843_, v_i_5844_);
v___x_5848_ = l_Lean_Expr_isFVar(v___x_5847_);
if (v___x_5848_ == 0)
{
uint8_t v___x_5849_; 
v___x_5849_ = 1;
return v___x_5849_;
}
else
{
size_t v___x_5850_; size_t v___x_5851_; 
v___x_5850_ = ((size_t)1ULL);
v___x_5851_ = lean_usize_add(v_i_5844_, v___x_5850_);
v_i_5844_ = v___x_5851_;
goto _start;
}
}
else
{
uint8_t v___x_5853_; 
v___x_5853_ = 0;
return v___x_5853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5854_, lean_object* v_i_5855_, lean_object* v_stop_5856_){
_start:
{
size_t v_i_boxed_5857_; size_t v_stop_boxed_5858_; uint8_t v_res_5859_; lean_object* v_r_5860_; 
v_i_boxed_5857_ = lean_unbox_usize(v_i_5855_);
lean_dec(v_i_5855_);
v_stop_boxed_5858_ = lean_unbox_usize(v_stop_5856_);
lean_dec(v_stop_5856_);
v_res_5859_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5854_, v_i_boxed_5857_, v_stop_boxed_5858_);
lean_dec_ref(v_as_5854_);
v_r_5860_ = lean_box(v_res_5859_);
return v_r_5860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5861_, size_t v_sz_5862_, size_t v_i_5863_, lean_object* v_bs_5864_){
_start:
{
uint8_t v___x_5865_; 
v___x_5865_ = lean_usize_dec_lt(v_i_5863_, v_sz_5862_);
if (v___x_5865_ == 0)
{
return v_bs_5864_;
}
else
{
lean_object* v_v_5866_; lean_object* v___x_5867_; lean_object* v_bs_x27_5868_; lean_object* v___y_5870_; 
v_v_5866_ = lean_array_uget(v_bs_5864_, v_i_5863_);
v___x_5867_ = lean_unsigned_to_nat(0u);
v_bs_x27_5868_ = lean_array_uset(v_bs_5864_, v_i_5863_, v___x_5867_);
if (lean_obj_tag(v_v_5866_) == 0)
{
v___y_5870_ = v_v_5866_;
goto v___jp_5869_;
}
else
{
lean_object* v_val_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; 
v_val_5875_ = lean_ctor_get(v_v_5866_, 0);
lean_inc(v_val_5875_);
lean_dec_ref_known(v_v_5866_, 1);
v___x_5876_ = lean_box(0);
v___x_5877_ = lean_array_get_borrowed(v___x_5876_, v___x_5861_, v_val_5875_);
lean_dec(v_val_5875_);
lean_inc(v___x_5877_);
v___y_5870_ = v___x_5877_;
goto v___jp_5869_;
}
v___jp_5869_:
{
size_t v___x_5871_; size_t v___x_5872_; lean_object* v___x_5873_; 
v___x_5871_ = ((size_t)1ULL);
v___x_5872_ = lean_usize_add(v_i_5863_, v___x_5871_);
v___x_5873_ = lean_array_uset(v_bs_x27_5868_, v_i_5863_, v___y_5870_);
v_i_5863_ = v___x_5872_;
v_bs_5864_ = v___x_5873_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5878_, lean_object* v_sz_5879_, lean_object* v_i_5880_, lean_object* v_bs_5881_){
_start:
{
size_t v_sz_boxed_5882_; size_t v_i_boxed_5883_; lean_object* v_res_5884_; 
v_sz_boxed_5882_ = lean_unbox_usize(v_sz_5879_);
lean_dec(v_sz_5879_);
v_i_boxed_5883_ = lean_unbox_usize(v_i_5880_);
lean_dec(v_i_5880_);
v_res_5884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5878_, v_sz_boxed_5882_, v_i_boxed_5883_, v_bs_5881_);
lean_dec_ref(v___x_5878_);
return v_res_5884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5885_, size_t v_sz_5886_, size_t v_i_5887_, lean_object* v_bs_5888_){
_start:
{
uint8_t v___x_5889_; 
v___x_5889_ = lean_usize_dec_lt(v_i_5887_, v_sz_5886_);
if (v___x_5889_ == 0)
{
return v_bs_5888_;
}
else
{
lean_object* v_v_5890_; lean_object* v___x_5891_; lean_object* v_bs_x27_5892_; size_t v_sz_5893_; size_t v___x_5894_; lean_object* v___x_5895_; size_t v___x_5896_; size_t v___x_5897_; lean_object* v___x_5898_; 
v_v_5890_ = lean_array_uget(v_bs_5888_, v_i_5887_);
v___x_5891_ = lean_unsigned_to_nat(0u);
v_bs_x27_5892_ = lean_array_uset(v_bs_5888_, v_i_5887_, v___x_5891_);
v_sz_5893_ = lean_array_size(v_v_5890_);
v___x_5894_ = ((size_t)0ULL);
v___x_5895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5885_, v_sz_5893_, v___x_5894_, v_v_5890_);
v___x_5896_ = ((size_t)1ULL);
v___x_5897_ = lean_usize_add(v_i_5887_, v___x_5896_);
v___x_5898_ = lean_array_uset(v_bs_x27_5892_, v_i_5887_, v___x_5895_);
v_i_5887_ = v___x_5897_;
v_bs_5888_ = v___x_5898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5900_, lean_object* v_sz_5901_, lean_object* v_i_5902_, lean_object* v_bs_5903_){
_start:
{
size_t v_sz_boxed_5904_; size_t v_i_boxed_5905_; lean_object* v_res_5906_; 
v_sz_boxed_5904_ = lean_unbox_usize(v_sz_5901_);
lean_dec(v_sz_5901_);
v_i_boxed_5905_ = lean_unbox_usize(v_i_5902_);
lean_dec(v_i_5902_);
v_res_5906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5900_, v_sz_boxed_5904_, v_i_boxed_5905_, v_bs_5903_);
lean_dec_ref(v___x_5900_);
return v_res_5906_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
v___x_5909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5910_ = lean_unsigned_to_nat(6u);
v___x_5911_ = lean_unsigned_to_nat(463u);
v___x_5912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5913_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5914_ = l_mkPanicMessageWithDecl(v___x_5913_, v___x_5912_, v___x_5911_, v___x_5910_, v___x_5909_);
return v___x_5914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5915_, lean_object* v___x_5916_, lean_object* v___x_5917_, lean_object* v_as_5918_, size_t v_sz_5919_, size_t v_i_5920_, lean_object* v_b_5921_){
_start:
{
lean_object* v_a_5923_; uint8_t v___x_5927_; 
v___x_5927_ = lean_usize_dec_lt(v_i_5920_, v_sz_5919_);
if (v___x_5927_ == 0)
{
return v_b_5921_;
}
else
{
lean_object* v_a_5928_; lean_object* v___x_5929_; uint8_t v___x_5930_; 
v_a_5928_ = lean_array_uget_borrowed(v_as_5918_, v_i_5920_);
v___x_5929_ = lean_array_get_size(v___x_5915_);
v___x_5930_ = lean_nat_dec_lt(v_a_5928_, v___x_5929_);
if (v___x_5930_ == 0)
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
lean_dec_ref(v_b_5921_);
v___x_5931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5932_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5931_);
if (lean_obj_tag(v___x_5932_) == 0)
{
lean_object* v_a_5933_; 
v_a_5933_ = lean_ctor_get(v___x_5932_, 0);
lean_inc(v_a_5933_);
lean_dec_ref_known(v___x_5932_, 1);
return v_a_5933_;
}
else
{
lean_object* v_a_5934_; 
v_a_5934_ = lean_ctor_get(v___x_5932_, 0);
lean_inc(v_a_5934_);
lean_dec_ref_known(v___x_5932_, 1);
v_a_5923_ = v_a_5934_;
goto v___jp_5922_;
}
}
else
{
lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5935_ = lean_box(0);
v___x_5936_ = lean_array_get_borrowed(v___x_5935_, v___x_5915_, v_a_5928_);
if (lean_obj_tag(v___x_5936_) == 1)
{
lean_object* v_val_5937_; uint8_t v_changed_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
v_val_5937_ = lean_ctor_get(v___x_5936_, 0);
v_changed_5938_ = lean_nat_dec_eq(v___x_5916_, v___x_5917_);
v___x_5939_ = lean_box(v_changed_5938_);
v___x_5940_ = lean_array_set(v_b_5921_, v_val_5937_, v___x_5939_);
v_a_5923_ = v___x_5940_;
goto v___jp_5922_;
}
else
{
v_a_5923_ = v_b_5921_;
goto v___jp_5922_;
}
}
}
v___jp_5922_:
{
size_t v___x_5924_; size_t v___x_5925_; 
v___x_5924_ = ((size_t)1ULL);
v___x_5925_ = lean_usize_add(v_i_5920_, v___x_5924_);
v_i_5920_ = v___x_5925_;
v_b_5921_ = v_a_5923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5941_, lean_object* v___x_5942_, lean_object* v___x_5943_, lean_object* v_as_5944_, lean_object* v_sz_5945_, lean_object* v_i_5946_, lean_object* v_b_5947_){
_start:
{
size_t v_sz_boxed_5948_; size_t v_i_boxed_5949_; lean_object* v_res_5950_; 
v_sz_boxed_5948_ = lean_unbox_usize(v_sz_5945_);
lean_dec(v_sz_5945_);
v_i_boxed_5949_ = lean_unbox_usize(v_i_5946_);
lean_dec(v_i_5946_);
v_res_5950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5941_, v___x_5942_, v___x_5943_, v_as_5944_, v_sz_boxed_5948_, v_i_boxed_5949_, v_b_5947_);
lean_dec_ref(v_as_5944_);
lean_dec(v___x_5943_);
lean_dec(v___x_5942_);
lean_dec_ref(v___x_5941_);
return v_res_5950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5951_, lean_object* v___x_5952_, lean_object* v___x_5953_, lean_object* v_a_5954_, lean_object* v_b_5955_){
_start:
{
uint8_t v___x_5956_; 
v___x_5956_ = lean_nat_dec_lt(v_a_5954_, v_upperBound_5951_);
if (v___x_5956_ == 0)
{
lean_dec(v_a_5954_);
return v_b_5955_;
}
else
{
lean_object* v_snd_5957_; lean_object* v_snd_5958_; lean_object* v_fst_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_6025_; 
v_snd_5957_ = lean_ctor_get(v_b_5955_, 1);
lean_inc(v_snd_5957_);
v_snd_5958_ = lean_ctor_get(v_snd_5957_, 1);
lean_inc(v_snd_5958_);
v_fst_5959_ = lean_ctor_get(v_b_5955_, 0);
v_isSharedCheck_6025_ = !lean_is_exclusive(v_b_5955_);
if (v_isSharedCheck_6025_ == 0)
{
lean_object* v_unused_6026_; 
v_unused_6026_ = lean_ctor_get(v_b_5955_, 1);
lean_dec(v_unused_6026_);
v___x_5961_ = v_b_5955_;
v_isShared_5962_ = v_isSharedCheck_6025_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_fst_5959_);
lean_dec(v_b_5955_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_6025_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v_fst_5963_; lean_object* v___x_5965_; uint8_t v_isShared_5966_; uint8_t v_isSharedCheck_6023_; 
v_fst_5963_ = lean_ctor_get(v_snd_5957_, 0);
v_isSharedCheck_6023_ = !lean_is_exclusive(v_snd_5957_);
if (v_isSharedCheck_6023_ == 0)
{
lean_object* v_unused_6024_; 
v_unused_6024_ = lean_ctor_get(v_snd_5957_, 1);
lean_dec(v_unused_6024_);
v___x_5965_ = v_snd_5957_;
v_isShared_5966_ = v_isSharedCheck_6023_;
goto v_resetjp_5964_;
}
else
{
lean_inc(v_fst_5963_);
lean_dec(v_snd_5957_);
v___x_5965_ = lean_box(0);
v_isShared_5966_ = v_isSharedCheck_6023_;
goto v_resetjp_5964_;
}
v_resetjp_5964_:
{
lean_object* v_array_5967_; lean_object* v_start_5968_; lean_object* v_stop_5969_; uint8_t v___x_5970_; 
v_array_5967_ = lean_ctor_get(v_snd_5958_, 0);
v_start_5968_ = lean_ctor_get(v_snd_5958_, 1);
v_stop_5969_ = lean_ctor_get(v_snd_5958_, 2);
v___x_5970_ = lean_nat_dec_lt(v_start_5968_, v_stop_5969_);
if (v___x_5970_ == 0)
{
lean_object* v___x_5972_; 
lean_dec(v_a_5954_);
if (v_isShared_5966_ == 0)
{
v___x_5972_ = v___x_5965_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v_fst_5963_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v_snd_5958_);
v___x_5972_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
lean_object* v___x_5974_; 
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 1, v___x_5972_);
v___x_5974_ = v___x_5961_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_fst_5959_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v___x_5972_);
v___x_5974_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
return v___x_5974_;
}
}
}
else
{
lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_6019_; 
lean_inc(v_stop_5969_);
lean_inc(v_start_5968_);
lean_inc_ref(v_array_5967_);
v_isSharedCheck_6019_ = !lean_is_exclusive(v_snd_5958_);
if (v_isSharedCheck_6019_ == 0)
{
lean_object* v_unused_6020_; lean_object* v_unused_6021_; lean_object* v_unused_6022_; 
v_unused_6020_ = lean_ctor_get(v_snd_5958_, 2);
lean_dec(v_unused_6020_);
v_unused_6021_ = lean_ctor_get(v_snd_5958_, 1);
lean_dec(v_unused_6021_);
v_unused_6022_ = lean_ctor_get(v_snd_5958_, 0);
lean_dec(v_unused_6022_);
v___x_5978_ = v_snd_5958_;
v_isShared_5979_ = v_isSharedCheck_6019_;
goto v_resetjp_5977_;
}
else
{
lean_dec(v_snd_5958_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_6019_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v_array_5980_; lean_object* v_start_5981_; lean_object* v_stop_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; lean_object* v___x_5987_; 
v_array_5980_ = lean_ctor_get(v_fst_5963_, 0);
v_start_5981_ = lean_ctor_get(v_fst_5963_, 1);
v_stop_5982_ = lean_ctor_get(v_fst_5963_, 2);
v___x_5983_ = lean_array_fget(v_array_5967_, v_start_5968_);
v___x_5984_ = lean_unsigned_to_nat(1u);
v___x_5985_ = lean_nat_add(v_start_5968_, v___x_5984_);
lean_dec(v_start_5968_);
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 1, v___x_5985_);
v___x_5987_ = v___x_5978_;
goto v_reusejp_5986_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_array_5967_);
lean_ctor_set(v_reuseFailAlloc_6018_, 1, v___x_5985_);
lean_ctor_set(v_reuseFailAlloc_6018_, 2, v_stop_5969_);
v___x_5987_ = v_reuseFailAlloc_6018_;
goto v_reusejp_5986_;
}
v_reusejp_5986_:
{
uint8_t v___x_5988_; 
v___x_5988_ = lean_nat_dec_lt(v_start_5981_, v_stop_5982_);
if (v___x_5988_ == 0)
{
lean_object* v___x_5990_; 
lean_dec(v___x_5983_);
lean_dec(v_a_5954_);
if (v_isShared_5966_ == 0)
{
lean_ctor_set(v___x_5965_, 1, v___x_5987_);
v___x_5990_ = v___x_5965_;
goto v_reusejp_5989_;
}
else
{
lean_object* v_reuseFailAlloc_5994_; 
v_reuseFailAlloc_5994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5994_, 0, v_fst_5963_);
lean_ctor_set(v_reuseFailAlloc_5994_, 1, v___x_5987_);
v___x_5990_ = v_reuseFailAlloc_5994_;
goto v_reusejp_5989_;
}
v_reusejp_5989_:
{
lean_object* v___x_5992_; 
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 1, v___x_5990_);
v___x_5992_ = v___x_5961_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v_fst_5959_);
lean_ctor_set(v_reuseFailAlloc_5993_, 1, v___x_5990_);
v___x_5992_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5991_;
}
v_reusejp_5991_:
{
return v___x_5992_;
}
}
}
else
{
lean_object* v___x_5996_; uint8_t v_isShared_5997_; uint8_t v_isSharedCheck_6014_; 
lean_inc(v_stop_5982_);
lean_inc(v_start_5981_);
lean_inc_ref(v_array_5980_);
v_isSharedCheck_6014_ = !lean_is_exclusive(v_fst_5963_);
if (v_isSharedCheck_6014_ == 0)
{
lean_object* v_unused_6015_; lean_object* v_unused_6016_; lean_object* v_unused_6017_; 
v_unused_6015_ = lean_ctor_get(v_fst_5963_, 2);
lean_dec(v_unused_6015_);
v_unused_6016_ = lean_ctor_get(v_fst_5963_, 1);
lean_dec(v_unused_6016_);
v_unused_6017_ = lean_ctor_get(v_fst_5963_, 0);
lean_dec(v_unused_6017_);
v___x_5996_ = v_fst_5963_;
v_isShared_5997_ = v_isSharedCheck_6014_;
goto v_resetjp_5995_;
}
else
{
lean_dec(v_fst_5963_);
v___x_5996_ = lean_box(0);
v_isShared_5997_ = v_isSharedCheck_6014_;
goto v_resetjp_5995_;
}
v_resetjp_5995_:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6001_; 
v___x_5998_ = lean_array_fget(v_array_5980_, v_start_5981_);
v___x_5999_ = lean_nat_add(v_start_5981_, v___x_5984_);
lean_dec(v_start_5981_);
if (v_isShared_5997_ == 0)
{
lean_ctor_set(v___x_5996_, 1, v___x_5999_);
v___x_6001_ = v___x_5996_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6013_; 
v_reuseFailAlloc_6013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_array_5980_);
lean_ctor_set(v_reuseFailAlloc_6013_, 1, v___x_5999_);
lean_ctor_set(v_reuseFailAlloc_6013_, 2, v_stop_5982_);
v___x_6001_ = v_reuseFailAlloc_6013_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
size_t v_sz_6002_; size_t v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6006_; 
v_sz_6002_ = lean_array_size(v___x_5998_);
v___x_6003_ = ((size_t)0ULL);
v___x_6004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5983_, v___x_5952_, v___x_5953_, v___x_5998_, v_sz_6002_, v___x_6003_, v_fst_5959_);
lean_dec(v___x_5998_);
lean_dec(v___x_5983_);
if (v_isShared_5966_ == 0)
{
lean_ctor_set(v___x_5965_, 1, v___x_5987_);
lean_ctor_set(v___x_5965_, 0, v___x_6001_);
v___x_6006_ = v___x_5965_;
goto v_reusejp_6005_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_6001_);
lean_ctor_set(v_reuseFailAlloc_6012_, 1, v___x_5987_);
v___x_6006_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6005_;
}
v_reusejp_6005_:
{
lean_object* v___x_6008_; 
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 1, v___x_6006_);
lean_ctor_set(v___x_5961_, 0, v___x_6004_);
v___x_6008_ = v___x_5961_;
goto v_reusejp_6007_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v___x_6004_);
lean_ctor_set(v_reuseFailAlloc_6011_, 1, v___x_6006_);
v___x_6008_ = v_reuseFailAlloc_6011_;
goto v_reusejp_6007_;
}
v_reusejp_6007_:
{
lean_object* v___x_6009_; 
v___x_6009_ = lean_nat_add(v_a_5954_, v___x_5984_);
lean_dec(v_a_5954_);
v_a_5954_ = v___x_6009_;
v_b_5955_ = v___x_6008_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6027_, lean_object* v___x_6028_, lean_object* v___x_6029_, lean_object* v_a_6030_, lean_object* v_b_6031_){
_start:
{
lean_object* v_res_6032_; 
v_res_6032_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6027_, v___x_6028_, v___x_6029_, v_a_6030_, v_b_6031_);
lean_dec(v___x_6029_);
lean_dec(v___x_6028_);
lean_dec(v_upperBound_6027_);
return v_res_6032_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___x_6034_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6035_ = lean_unsigned_to_nat(2u);
v___x_6036_ = lean_unsigned_to_nat(457u);
v___x_6037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6038_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6039_ = l_mkPanicMessageWithDecl(v___x_6038_, v___x_6037_, v___x_6036_, v___x_6035_, v___x_6034_);
return v___x_6039_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v___x_6041_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6042_ = lean_unsigned_to_nat(2u);
v___x_6043_ = lean_unsigned_to_nat(458u);
v___x_6044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6045_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6046_ = l_mkPanicMessageWithDecl(v___x_6045_, v___x_6044_, v___x_6043_, v___x_6042_, v___x_6041_);
return v___x_6046_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6048_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6049_ = lean_unsigned_to_nat(2u);
v___x_6050_ = lean_unsigned_to_nat(456u);
v___x_6051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6052_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6053_ = l_mkPanicMessageWithDecl(v___x_6052_, v___x_6051_, v___x_6050_, v___x_6049_, v___x_6048_);
return v___x_6053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6054_, lean_object* v_xs_6055_, lean_object* v_toErase_6056_){
_start:
{
lean_object* v___x_6057_; lean_object* v___x_6058_; uint8_t v___x_6142_; 
v___x_6057_ = lean_unsigned_to_nat(0u);
v___x_6058_ = lean_array_get_size(v_xs_6055_);
v___x_6142_ = lean_nat_dec_lt(v___x_6057_, v___x_6058_);
if (v___x_6142_ == 0)
{
goto v___jp_6059_;
}
else
{
if (v___x_6142_ == 0)
{
goto v___jp_6059_;
}
else
{
size_t v___x_6143_; size_t v___x_6144_; uint8_t v___x_6145_; 
v___x_6143_ = ((size_t)0ULL);
v___x_6144_ = lean_usize_of_nat(v___x_6058_);
v___x_6145_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6055_, v___x_6143_, v___x_6144_);
if (v___x_6145_ == 0)
{
goto v___jp_6059_;
}
else
{
lean_object* v___x_6146_; lean_object* v___x_6147_; 
lean_dec_ref(v_toErase_6056_);
lean_dec_ref(v_xs_6055_);
lean_dec_ref(v_fixedParamPerms_6054_);
v___x_6146_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6147_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6146_);
return v___x_6147_;
}
}
}
v___jp_6059_:
{
lean_object* v_numFixed_6060_; lean_object* v_perms_6061_; lean_object* v_revDeps_6062_; uint8_t v___x_6063_; 
v_numFixed_6060_ = lean_ctor_get(v_fixedParamPerms_6054_, 0);
v_perms_6061_ = lean_ctor_get(v_fixedParamPerms_6054_, 1);
lean_inc_ref(v_perms_6061_);
v_revDeps_6062_ = lean_ctor_get(v_fixedParamPerms_6054_, 2);
lean_inc_ref(v_revDeps_6062_);
v___x_6063_ = lean_nat_dec_eq(v_numFixed_6060_, v___x_6058_);
if (v___x_6063_ == 0)
{
lean_object* v___x_6064_; lean_object* v___x_6065_; 
lean_dec_ref(v_revDeps_6062_);
lean_dec_ref(v_perms_6061_);
lean_dec_ref(v_toErase_6056_);
lean_dec_ref(v_xs_6055_);
lean_dec_ref(v_fixedParamPerms_6054_);
v___x_6064_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6065_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6064_);
return v___x_6065_;
}
else
{
lean_object* v___x_6066_; lean_object* v___x_6067_; uint8_t v_changed_6068_; 
v___x_6066_ = lean_array_get_size(v_toErase_6056_);
v___x_6067_ = lean_array_get_size(v_perms_6061_);
v_changed_6068_ = lean_nat_dec_eq(v___x_6066_, v___x_6067_);
if (v_changed_6068_ == 0)
{
lean_object* v___x_6069_; lean_object* v___x_6070_; 
lean_dec_ref(v_revDeps_6062_);
lean_dec_ref(v_perms_6061_);
lean_dec_ref(v_toErase_6056_);
lean_dec_ref(v_xs_6055_);
lean_dec_ref(v_fixedParamPerms_6054_);
v___x_6069_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6070_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6069_);
return v___x_6070_;
}
else
{
uint8_t v_changed_6071_; lean_object* v___x_6072_; lean_object* v_mask_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v_fst_6079_; lean_object* v___x_6081_; uint8_t v_isShared_6082_; uint8_t v_isSharedCheck_6140_; 
v_changed_6071_ = 0;
v___x_6072_ = lean_box(v_changed_6071_);
lean_inc(v_numFixed_6060_);
v_mask_6073_ = lean_mk_array(v_numFixed_6060_, v___x_6072_);
v___x_6074_ = l_Array_toSubarray___redArg(v_toErase_6056_, v___x_6057_, v___x_6066_);
lean_inc_ref(v_perms_6061_);
v___x_6075_ = l_Array_toSubarray___redArg(v_perms_6061_, v___x_6057_, v___x_6067_);
v___x_6076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6074_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___x_6077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6077_, 0, v_mask_6073_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6066_, v___x_6066_, v___x_6067_, v___x_6057_, v___x_6077_);
v_fst_6079_ = lean_ctor_get(v___x_6078_, 0);
v_isSharedCheck_6140_ = !lean_is_exclusive(v___x_6078_);
if (v_isSharedCheck_6140_ == 0)
{
lean_object* v_unused_6141_; 
v_unused_6141_ = lean_ctor_get(v___x_6078_, 1);
lean_dec(v_unused_6141_);
v___x_6081_ = v___x_6078_;
v_isShared_6082_ = v_isSharedCheck_6140_;
goto v_resetjp_6080_;
}
else
{
lean_inc(v_fst_6079_);
lean_dec(v___x_6078_);
v___x_6081_ = lean_box(0);
v_isShared_6082_ = v_isSharedCheck_6140_;
goto v_resetjp_6080_;
}
v_resetjp_6080_:
{
lean_object* v___x_6083_; lean_object* v___x_6085_; 
v___x_6083_ = lean_box(v_changed_6068_);
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 1, v___x_6083_);
v___x_6085_ = v___x_6081_;
goto v_reusejp_6084_;
}
else
{
lean_object* v_reuseFailAlloc_6139_; 
v_reuseFailAlloc_6139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6139_, 0, v_fst_6079_);
lean_ctor_set(v_reuseFailAlloc_6139_, 1, v___x_6083_);
v___x_6085_ = v_reuseFailAlloc_6139_;
goto v_reusejp_6084_;
}
v_reusejp_6084_:
{
lean_object* v___x_6086_; lean_object* v___x_6088_; uint8_t v_isShared_6089_; uint8_t v_isSharedCheck_6135_; 
v___x_6086_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6067_, v_perms_6061_, v___x_6066_, v_fixedParamPerms_6054_, v___x_6085_);
v_isSharedCheck_6135_ = !lean_is_exclusive(v_fixedParamPerms_6054_);
if (v_isSharedCheck_6135_ == 0)
{
lean_object* v_unused_6136_; lean_object* v_unused_6137_; lean_object* v_unused_6138_; 
v_unused_6136_ = lean_ctor_get(v_fixedParamPerms_6054_, 2);
lean_dec(v_unused_6136_);
v_unused_6137_ = lean_ctor_get(v_fixedParamPerms_6054_, 1);
lean_dec(v_unused_6137_);
v_unused_6138_ = lean_ctor_get(v_fixedParamPerms_6054_, 0);
lean_dec(v_unused_6138_);
v___x_6088_ = v_fixedParamPerms_6054_;
v_isShared_6089_ = v_isSharedCheck_6135_;
goto v_resetjp_6087_;
}
else
{
lean_dec(v_fixedParamPerms_6054_);
v___x_6088_ = lean_box(0);
v_isShared_6089_ = v_isSharedCheck_6135_;
goto v_resetjp_6087_;
}
v_resetjp_6087_:
{
lean_object* v_fst_6090_; lean_object* v___x_6092_; uint8_t v_isShared_6093_; uint8_t v_isSharedCheck_6133_; 
v_fst_6090_ = lean_ctor_get(v___x_6086_, 0);
v_isSharedCheck_6133_ = !lean_is_exclusive(v___x_6086_);
if (v_isSharedCheck_6133_ == 0)
{
lean_object* v_unused_6134_; 
v_unused_6134_ = lean_ctor_get(v___x_6086_, 1);
lean_dec(v_unused_6134_);
v___x_6092_ = v___x_6086_;
v_isShared_6093_ = v_isSharedCheck_6133_;
goto v_resetjp_6091_;
}
else
{
lean_inc(v_fst_6090_);
lean_dec(v___x_6086_);
v___x_6092_ = lean_box(0);
v_isShared_6093_ = v_isSharedCheck_6133_;
goto v_resetjp_6091_;
}
v_resetjp_6091_:
{
lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6099_; 
v___x_6094_ = lean_array_get_size(v_fst_6090_);
v___x_6095_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6096_ = l_Array_toSubarray___redArg(v_fst_6090_, v___x_6057_, v___x_6094_);
v___x_6097_ = l_Array_toSubarray___redArg(v_xs_6055_, v___x_6057_, v___x_6058_);
if (v_isShared_6093_ == 0)
{
lean_ctor_set(v___x_6092_, 1, v___x_6097_);
lean_ctor_set(v___x_6092_, 0, v___x_6096_);
v___x_6099_ = v___x_6092_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v___x_6096_);
lean_ctor_set(v_reuseFailAlloc_6132_, 1, v___x_6097_);
v___x_6099_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v_snd_6104_; lean_object* v_snd_6105_; lean_object* v_fst_6106_; lean_object* v_fst_6107_; lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6130_; 
v___x_6100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6095_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
v___x_6101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6095_);
lean_ctor_set(v___x_6101_, 1, v___x_6100_);
v___x_6102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6095_);
lean_ctor_set(v___x_6102_, 1, v___x_6101_);
v___x_6103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6094_, v___x_6057_, v___x_6102_);
v_snd_6104_ = lean_ctor_get(v___x_6103_, 1);
lean_inc(v_snd_6104_);
v_snd_6105_ = lean_ctor_get(v_snd_6104_, 1);
lean_inc(v_snd_6105_);
v_fst_6106_ = lean_ctor_get(v___x_6103_, 0);
lean_inc(v_fst_6106_);
lean_dec_ref(v___x_6103_);
v_fst_6107_ = lean_ctor_get(v_snd_6104_, 0);
v_isSharedCheck_6130_ = !lean_is_exclusive(v_snd_6104_);
if (v_isSharedCheck_6130_ == 0)
{
lean_object* v_unused_6131_; 
v_unused_6131_ = lean_ctor_get(v_snd_6104_, 1);
lean_dec(v_unused_6131_);
v___x_6109_ = v_snd_6104_;
v_isShared_6110_ = v_isSharedCheck_6130_;
goto v_resetjp_6108_;
}
else
{
lean_inc(v_fst_6107_);
lean_dec(v_snd_6104_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6130_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v_fst_6111_; lean_object* v___x_6113_; uint8_t v_isShared_6114_; uint8_t v_isSharedCheck_6128_; 
v_fst_6111_ = lean_ctor_get(v_snd_6105_, 0);
v_isSharedCheck_6128_ = !lean_is_exclusive(v_snd_6105_);
if (v_isSharedCheck_6128_ == 0)
{
lean_object* v_unused_6129_; 
v_unused_6129_ = lean_ctor_get(v_snd_6105_, 1);
lean_dec(v_unused_6129_);
v___x_6113_ = v_snd_6105_;
v_isShared_6114_ = v_isSharedCheck_6128_;
goto v_resetjp_6112_;
}
else
{
lean_inc(v_fst_6111_);
lean_dec(v_snd_6105_);
v___x_6113_ = lean_box(0);
v_isShared_6114_ = v_isSharedCheck_6128_;
goto v_resetjp_6112_;
}
v_resetjp_6112_:
{
lean_object* v___x_6115_; size_t v_sz_6116_; size_t v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6120_; 
v___x_6115_ = lean_array_get_size(v_fst_6111_);
v_sz_6116_ = lean_array_size(v_perms_6061_);
v___x_6117_ = ((size_t)0ULL);
v___x_6118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6106_, v_sz_6116_, v___x_6117_, v_perms_6061_);
lean_dec(v_fst_6106_);
if (v_isShared_6089_ == 0)
{
lean_ctor_set(v___x_6088_, 1, v___x_6118_);
lean_ctor_set(v___x_6088_, 0, v___x_6115_);
v___x_6120_ = v___x_6088_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v___x_6115_);
lean_ctor_set(v_reuseFailAlloc_6127_, 1, v___x_6118_);
lean_ctor_set(v_reuseFailAlloc_6127_, 2, v_revDeps_6062_);
v___x_6120_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
lean_object* v___x_6122_; 
if (v_isShared_6114_ == 0)
{
lean_ctor_set(v___x_6113_, 1, v_fst_6107_);
v___x_6122_ = v___x_6113_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6126_; 
v_reuseFailAlloc_6126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6126_, 0, v_fst_6111_);
lean_ctor_set(v_reuseFailAlloc_6126_, 1, v_fst_6107_);
v___x_6122_ = v_reuseFailAlloc_6126_;
goto v_reusejp_6121_;
}
v_reusejp_6121_:
{
lean_object* v___x_6124_; 
if (v_isShared_6110_ == 0)
{
lean_ctor_set(v___x_6109_, 1, v___x_6122_);
lean_ctor_set(v___x_6109_, 0, v___x_6120_);
v___x_6124_ = v___x_6109_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v___x_6120_);
lean_ctor_set(v_reuseFailAlloc_6125_, 1, v___x_6122_);
v___x_6124_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
return v___x_6124_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6148_, lean_object* v___x_6149_, lean_object* v___x_6150_, lean_object* v___x_6151_, lean_object* v_fixedParamPerms_6152_, lean_object* v_next_6153_, lean_object* v_inst_6154_, lean_object* v_R_6155_, lean_object* v_a_6156_, lean_object* v_b_6157_, lean_object* v_c_6158_){
_start:
{
lean_object* v___x_6159_; 
v___x_6159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6148_, v___x_6149_, v___x_6150_, v___x_6151_, v_fixedParamPerms_6152_, v_next_6153_, v_a_6156_, v_b_6157_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6160_, lean_object* v___x_6161_, lean_object* v___x_6162_, lean_object* v___x_6163_, lean_object* v_fixedParamPerms_6164_, lean_object* v_next_6165_, lean_object* v_inst_6166_, lean_object* v_R_6167_, lean_object* v_a_6168_, lean_object* v_b_6169_, lean_object* v_c_6170_){
_start:
{
lean_object* v_res_6171_; 
v_res_6171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6160_, v___x_6161_, v___x_6162_, v___x_6163_, v_fixedParamPerms_6164_, v_next_6165_, v_inst_6166_, v_R_6167_, v_a_6168_, v_b_6169_, v_c_6170_);
lean_dec(v_a_6168_);
lean_dec(v_next_6165_);
lean_dec_ref(v_fixedParamPerms_6164_);
lean_dec(v___x_6163_);
lean_dec(v___x_6162_);
lean_dec_ref(v___x_6161_);
lean_dec(v_upperBound_6160_);
return v_res_6171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6172_, lean_object* v___x_6173_, lean_object* v___x_6174_, lean_object* v___x_6175_, lean_object* v_fixedParamPerms_6176_, lean_object* v_inst_6177_, lean_object* v_R_6178_, lean_object* v_a_6179_, lean_object* v_b_6180_, lean_object* v_c_6181_){
_start:
{
lean_object* v___x_6182_; 
v___x_6182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6172_, v___x_6173_, v___x_6174_, v___x_6175_, v_fixedParamPerms_6176_, v_a_6179_, v_b_6180_);
return v___x_6182_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6183_, lean_object* v___x_6184_, lean_object* v___x_6185_, lean_object* v___x_6186_, lean_object* v_fixedParamPerms_6187_, lean_object* v_inst_6188_, lean_object* v_R_6189_, lean_object* v_a_6190_, lean_object* v_b_6191_, lean_object* v_c_6192_){
_start:
{
lean_object* v_res_6193_; 
v_res_6193_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6183_, v___x_6184_, v___x_6185_, v___x_6186_, v_fixedParamPerms_6187_, v_inst_6188_, v_R_6189_, v_a_6190_, v_b_6191_, v_c_6192_);
lean_dec_ref(v_fixedParamPerms_6187_);
lean_dec(v___x_6186_);
lean_dec(v___x_6185_);
lean_dec_ref(v___x_6184_);
lean_dec(v_upperBound_6183_);
return v_res_6193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6194_, lean_object* v___x_6195_, lean_object* v___x_6196_, lean_object* v_fixedParamPerms_6197_, lean_object* v_inst_6198_, lean_object* v_a_6199_){
_start:
{
lean_object* v___x_6200_; 
v___x_6200_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6194_, v___x_6195_, v___x_6196_, v_fixedParamPerms_6197_, v_a_6199_);
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6201_, lean_object* v___x_6202_, lean_object* v___x_6203_, lean_object* v_fixedParamPerms_6204_, lean_object* v_inst_6205_, lean_object* v_a_6206_){
_start:
{
lean_object* v_res_6207_; 
v_res_6207_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6201_, v___x_6202_, v___x_6203_, v_fixedParamPerms_6204_, v_inst_6205_, v_a_6206_);
lean_dec_ref(v_fixedParamPerms_6204_);
lean_dec(v___x_6203_);
lean_dec_ref(v___x_6202_);
lean_dec(v___x_6201_);
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6208_, lean_object* v_inst_6209_, lean_object* v_R_6210_, lean_object* v_a_6211_, lean_object* v_b_6212_, lean_object* v_c_6213_){
_start:
{
lean_object* v___x_6214_; 
v___x_6214_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6208_, v_a_6211_, v_b_6212_);
return v___x_6214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6215_, lean_object* v_inst_6216_, lean_object* v_R_6217_, lean_object* v_a_6218_, lean_object* v_b_6219_, lean_object* v_c_6220_){
_start:
{
lean_object* v_res_6221_; 
v_res_6221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6215_, v_inst_6216_, v_R_6217_, v_a_6218_, v_b_6219_, v_c_6220_);
lean_dec(v_upperBound_6215_);
return v_res_6221_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6222_, lean_object* v___x_6223_, lean_object* v___x_6224_, lean_object* v_inst_6225_, lean_object* v_R_6226_, lean_object* v_a_6227_, lean_object* v_b_6228_, lean_object* v_c_6229_){
_start:
{
lean_object* v___x_6230_; 
v___x_6230_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6222_, v___x_6223_, v___x_6224_, v_a_6227_, v_b_6228_);
return v___x_6230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6231_, lean_object* v___x_6232_, lean_object* v___x_6233_, lean_object* v_inst_6234_, lean_object* v_R_6235_, lean_object* v_a_6236_, lean_object* v_b_6237_, lean_object* v_c_6238_){
_start:
{
lean_object* v_res_6239_; 
v_res_6239_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6231_, v___x_6232_, v___x_6233_, v_inst_6234_, v_R_6235_, v_a_6236_, v_b_6237_, v_c_6238_);
lean_dec(v___x_6233_);
lean_dec(v___x_6232_);
lean_dec(v_upperBound_6231_);
return v_res_6239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object* v_upperBound_6240_, lean_object* v___x_6241_, lean_object* v_fixedParamPerms_6242_, lean_object* v_next_6243_, lean_object* v___x_6244_, lean_object* v___x_6245_, lean_object* v_inst_6246_, lean_object* v_R_6247_, lean_object* v_a_6248_, lean_object* v_b_6249_, lean_object* v_c_6250_){
_start:
{
lean_object* v___x_6251_; 
v___x_6251_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_6240_, v___x_6241_, v_fixedParamPerms_6242_, v_next_6243_, v___x_6244_, v___x_6245_, v_a_6248_, v_b_6249_);
return v___x_6251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object* v_upperBound_6252_, lean_object* v___x_6253_, lean_object* v_fixedParamPerms_6254_, lean_object* v_next_6255_, lean_object* v___x_6256_, lean_object* v___x_6257_, lean_object* v_inst_6258_, lean_object* v_R_6259_, lean_object* v_a_6260_, lean_object* v_b_6261_, lean_object* v_c_6262_){
_start:
{
lean_object* v_res_6263_; 
v_res_6263_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(v_upperBound_6252_, v___x_6253_, v_fixedParamPerms_6254_, v_next_6255_, v___x_6256_, v___x_6257_, v_inst_6258_, v_R_6259_, v_a_6260_, v_b_6261_, v_c_6262_);
lean_dec(v___x_6257_);
lean_dec(v___x_6256_);
lean_dec(v_next_6255_);
lean_dec_ref(v_fixedParamPerms_6254_);
lean_dec_ref(v___x_6253_);
lean_dec(v_upperBound_6252_);
return v_res_6263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6321_; uint8_t v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; 
v___x_6321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6322_ = 0;
v___x_6323_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6324_ = l_Lean_registerTraceClass(v___x_6321_, v___x_6322_, v___x_6323_);
return v___x_6324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6325_){
_start:
{
lean_object* v_res_6326_; 
v_res_6326_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6326_;
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
