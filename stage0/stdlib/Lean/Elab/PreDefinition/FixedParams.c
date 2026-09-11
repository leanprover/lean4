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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_nbuckets_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1224_ = lean_array_get_size(v_data_1223_);
v___x_1225_ = lean_unsigned_to_nat(2u);
v_nbuckets_1226_ = lean_nat_mul(v___x_1224_, v___x_1225_);
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_mk_array(v_nbuckets_1226_, v___x_1228_);
v___x_1230_ = lean_array_propagate_mark(v_data_1223_, v___x_1229_);
v___x_1231_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1227_, v_data_1223_, v___x_1230_);
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
v___x_1315_ = lean_st_ref_put(v_a_1309_, v___x_1314_);
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
lean_object* v___y_1471_; lean_object* v_toCold_1480_; lean_object* v_currRecDepth_1481_; lean_object* v_ref_1482_; uint8_t v_diag_1483_; uint8_t v_suppressElabErrors_1484_; lean_object* v_maxRecDepth_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v_toCold_1480_ = lean_ctor_get(v___y_1467_, 0);
v_currRecDepth_1481_ = lean_ctor_get(v___y_1467_, 1);
v_ref_1482_ = lean_ctor_get(v___y_1467_, 2);
v_diag_1483_ = lean_ctor_get_uint8(v___y_1467_, sizeof(void*)*3);
v_suppressElabErrors_1484_ = lean_ctor_get_uint8(v___y_1467_, sizeof(void*)*3 + 1);
v_maxRecDepth_1490_ = lean_ctor_get(v_toCold_1480_, 3);
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_nat_dec_eq(v_maxRecDepth_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_nat_dec_eq(v_currRecDepth_1481_, v_maxRecDepth_1490_);
if (v___x_1493_ == 0)
{
goto v___jp_1485_;
}
else
{
lean_object* v___x_1494_; 
lean_dec_ref(v_x_1463_);
lean_inc(v_ref_1482_);
v___x_1494_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1482_);
v___y_1471_ = v___x_1494_;
goto v___jp_1470_;
}
}
else
{
goto v___jp_1485_;
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
v___jp_1485_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_add(v_currRecDepth_1481_, v___x_1486_);
lean_inc(v_ref_1482_);
lean_inc_ref(v_toCold_1480_);
v___x_1488_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1488_, 0, v_toCold_1480_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
lean_ctor_set(v___x_1488_, 2, v_ref_1482_);
lean_ctor_set_uint8(v___x_1488_, sizeof(void*)*3, v_diag_1483_);
lean_ctor_set_uint8(v___x_1488_, sizeof(void*)*3 + 1, v_suppressElabErrors_1484_);
lean_inc(v___y_1468_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
v___x_1489_ = lean_apply_6(v_x_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___x_1488_, v___y_1468_, lean_box(0));
v___y_1471_ = v___x_1489_;
goto v___jp_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1503_, lean_object* v_x_1504_){
_start:
{
if (lean_obj_tag(v_x_1504_) == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
else
{
lean_object* v_key_1506_; lean_object* v_value_1507_; lean_object* v_tail_1508_; uint8_t v___x_1509_; 
v_key_1506_ = lean_ctor_get(v_x_1504_, 0);
v_value_1507_ = lean_ctor_get(v_x_1504_, 1);
v_tail_1508_ = lean_ctor_get(v_x_1504_, 2);
v___x_1509_ = l_Lean_ExprStructEq_beq(v_key_1506_, v_a_1503_);
if (v___x_1509_ == 0)
{
v_x_1504_ = v_tail_1508_;
goto _start;
}
else
{
lean_object* v___x_1511_; 
lean_inc(v_value_1507_);
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_value_1507_);
return v___x_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1512_, v_x_1513_);
lean_dec(v_x_1513_);
lean_dec_ref(v_a_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_buckets_1517_; lean_object* v___x_1518_; uint64_t v___x_1519_; uint64_t v___x_1520_; uint64_t v___x_1521_; uint64_t v_fold_1522_; uint64_t v___x_1523_; uint64_t v___x_1524_; uint64_t v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_buckets_1517_ = lean_ctor_get(v_m_1515_, 1);
v___x_1518_ = lean_array_get_size(v_buckets_1517_);
v___x_1519_ = l_Lean_ExprStructEq_hash(v_a_1516_);
v___x_1520_ = 32ULL;
v___x_1521_ = lean_uint64_shift_right(v___x_1519_, v___x_1520_);
v_fold_1522_ = lean_uint64_xor(v___x_1519_, v___x_1521_);
v___x_1523_ = 16ULL;
v___x_1524_ = lean_uint64_shift_right(v_fold_1522_, v___x_1523_);
v___x_1525_ = lean_uint64_xor(v_fold_1522_, v___x_1524_);
v___x_1526_ = lean_uint64_to_usize(v___x_1525_);
v___x_1527_ = lean_usize_of_nat(v___x_1518_);
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_sub(v___x_1527_, v___x_1528_);
v___x_1530_ = lean_usize_land(v___x_1526_, v___x_1529_);
v___x_1531_ = lean_array_uget_borrowed(v_buckets_1517_, v___x_1530_);
v___x_1532_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1516_, v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1533_, v_a_1534_);
lean_dec_ref(v_a_1534_);
lean_dec_ref(v_m_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1539_, lean_object* v_pre_1540_, lean_object* v_post_1541_, uint8_t v_usedLetOnly_1542_, uint8_t v_skipConstInApp_1543_, uint8_t v_skipInstances_1544_, lean_object* v_body_1545_, lean_object* v_x_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_array_push(v_fvars_1539_, v_x_1546_);
v___x_1554_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1540_, v_post_1541_, v_usedLetOnly_1542_, v_skipConstInApp_1543_, v_skipInstances_1544_, v___x_1553_, v_body_1545_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1555_, lean_object* v_pre_1556_, lean_object* v_post_1557_, lean_object* v_usedLetOnly_1558_, lean_object* v_skipConstInApp_1559_, lean_object* v_skipInstances_1560_, lean_object* v_body_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
uint8_t v_usedLetOnly_boxed_1569_; uint8_t v_skipConstInApp_boxed_1570_; uint8_t v_skipInstances_boxed_1571_; lean_object* v_res_1572_; 
v_usedLetOnly_boxed_1569_ = lean_unbox(v_usedLetOnly_1558_);
v_skipConstInApp_boxed_1570_ = lean_unbox(v_skipConstInApp_1559_);
v_skipInstances_boxed_1571_ = lean_unbox(v_skipInstances_1560_);
v_res_1572_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1555_, v_pre_1556_, v_post_1557_, v_usedLetOnly_boxed_1569_, v_skipConstInApp_boxed_1570_, v_skipInstances_boxed_1571_, v_body_1561_, v_x_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1573_, lean_object* v_post_1574_, uint8_t v_usedLetOnly_1575_, uint8_t v_skipConstInApp_1576_, uint8_t v_skipInstances_1577_, lean_object* v_e_1578_, lean_object* v_a_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
lean_inc_ref(v_post_1574_);
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
lean_inc_ref(v_e_1578_);
v___x_1585_ = lean_apply_6(v_post_1574_, v_e_1578_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, lean_box(0));
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1604_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1604_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1604_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
switch(lean_obj_tag(v_a_1586_))
{
case 0:
{
lean_object* v_e_1590_; lean_object* v___x_1592_; 
lean_dec_ref(v_e_1578_);
lean_dec_ref(v_post_1574_);
lean_dec_ref(v_pre_1573_);
v_e_1590_ = lean_ctor_get(v_a_1586_, 0);
lean_inc_ref(v_e_1590_);
lean_dec_ref_known(v_a_1586_, 1);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v_e_1590_);
v___x_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_e_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
case 1:
{
lean_object* v_e_1594_; lean_object* v___x_1595_; 
lean_del_object(v___x_1588_);
lean_dec_ref(v_e_1578_);
v_e_1594_ = lean_ctor_get(v_a_1586_, 0);
lean_inc_ref(v_e_1594_);
lean_dec_ref_known(v_a_1586_, 1);
v___x_1595_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1573_, v_post_1574_, v_usedLetOnly_1575_, v_skipConstInApp_1576_, v_skipInstances_1577_, v_e_1594_, v_a_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
return v___x_1595_;
}
default: 
{
lean_object* v_e_x3f_1596_; 
lean_dec_ref(v_post_1574_);
lean_dec_ref(v_pre_1573_);
v_e_x3f_1596_ = lean_ctor_get(v_a_1586_, 0);
lean_inc(v_e_x3f_1596_);
lean_dec_ref_known(v_a_1586_, 1);
if (lean_obj_tag(v_e_x3f_1596_) == 0)
{
lean_object* v___x_1598_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v_e_1578_);
v___x_1598_ = v___x_1588_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_e_1578_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; 
lean_dec_ref(v_e_1578_);
v_val_1600_ = lean_ctor_get(v_e_x3f_1596_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_e_x3f_1596_, 1);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v_val_1600_);
v___x_1602_ = v___x_1588_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
}
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref(v_e_1578_);
lean_dec_ref(v_post_1574_);
lean_dec_ref(v_pre_1573_);
v_a_1605_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1585_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1585_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1613_, lean_object* v_post_1614_, uint8_t v_usedLetOnly_1615_, uint8_t v_skipConstInApp_1616_, uint8_t v_skipInstances_1617_, lean_object* v_fvars_1618_, lean_object* v_e_1619_, lean_object* v_a_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
if (lean_obj_tag(v_e_1619_) == 6)
{
lean_object* v_binderName_1626_; lean_object* v_binderType_1627_; lean_object* v_body_1628_; uint8_t v_binderInfo_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v_binderName_1626_ = lean_ctor_get(v_e_1619_, 0);
lean_inc(v_binderName_1626_);
v_binderType_1627_ = lean_ctor_get(v_e_1619_, 1);
lean_inc_ref(v_binderType_1627_);
v_body_1628_ = lean_ctor_get(v_e_1619_, 2);
lean_inc_ref(v_body_1628_);
v_binderInfo_1629_ = lean_ctor_get_uint8(v_e_1619_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1619_, 3);
v___x_1630_ = lean_expr_instantiate_rev(v_binderType_1627_, v_fvars_1618_);
lean_dec_ref(v_binderType_1627_);
lean_inc_ref(v_post_1614_);
lean_inc_ref(v_pre_1613_);
v___x_1631_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1613_, v_post_1614_, v_usedLetOnly_1615_, v_skipConstInApp_1616_, v_skipInstances_1617_, v___x_1630_, v_a_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___f_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = lean_box(v_usedLetOnly_1615_);
v___x_1634_ = lean_box(v_skipConstInApp_1616_);
v___x_1635_ = lean_box(v_skipInstances_1617_);
v___f_1636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1636_, 0, v_fvars_1618_);
lean_closure_set(v___f_1636_, 1, v_pre_1613_);
lean_closure_set(v___f_1636_, 2, v_post_1614_);
lean_closure_set(v___f_1636_, 3, v___x_1633_);
lean_closure_set(v___f_1636_, 4, v___x_1634_);
lean_closure_set(v___f_1636_, 5, v___x_1635_);
lean_closure_set(v___f_1636_, 6, v_body_1628_);
v___x_1637_ = 0;
v___x_1638_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1626_, v_binderInfo_1629_, v_a_1632_, v___f_1636_, v___x_1637_, v_a_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
return v___x_1638_;
}
else
{
lean_dec_ref(v_body_1628_);
lean_dec(v_binderName_1626_);
lean_dec_ref(v_fvars_1618_);
lean_dec_ref(v_post_1614_);
lean_dec_ref(v_pre_1613_);
return v___x_1631_;
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_expr_instantiate_rev(v_e_1619_, v_fvars_1618_);
lean_dec_ref(v_e_1619_);
lean_inc_ref(v_post_1614_);
lean_inc_ref(v_pre_1613_);
v___x_1640_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1613_, v_post_1614_, v_usedLetOnly_1615_, v_skipConstInApp_1616_, v_skipInstances_1617_, v___x_1639_, v_a_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; uint8_t v___x_1642_; uint8_t v___x_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = 0;
v___x_1643_ = 1;
v___x_1644_ = 1;
v___x_1645_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1618_, v_a_1641_, v___x_1642_, v_usedLetOnly_1615_, v___x_1642_, v___x_1643_, v___x_1644_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec_ref(v_fvars_1618_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1613_, v_post_1614_, v_usedLetOnly_1615_, v_skipConstInApp_1616_, v_skipInstances_1617_, v_a_1646_, v_a_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
return v___x_1647_;
}
else
{
lean_dec_ref(v_post_1614_);
lean_dec_ref(v_pre_1613_);
return v___x_1645_;
}
}
else
{
lean_dec_ref(v_fvars_1618_);
lean_dec_ref(v_post_1614_);
lean_dec_ref(v_pre_1613_);
return v___x_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1648_, lean_object* v_pre_1649_, lean_object* v_post_1650_, uint8_t v_usedLetOnly_1651_, uint8_t v_skipConstInApp_1652_, uint8_t v_skipInstances_1653_, lean_object* v_body_1654_, lean_object* v_x_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_array_push(v_fvars_1648_, v_x_1655_);
v___x_1663_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1649_, v_post_1650_, v_usedLetOnly_1651_, v_skipConstInApp_1652_, v_skipInstances_1653_, v___x_1662_, v_body_1654_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1664_, lean_object* v_pre_1665_, lean_object* v_post_1666_, lean_object* v_usedLetOnly_1667_, lean_object* v_skipConstInApp_1668_, lean_object* v_skipInstances_1669_, lean_object* v_body_1670_, lean_object* v_x_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v_usedLetOnly_boxed_1678_; uint8_t v_skipConstInApp_boxed_1679_; uint8_t v_skipInstances_boxed_1680_; lean_object* v_res_1681_; 
v_usedLetOnly_boxed_1678_ = lean_unbox(v_usedLetOnly_1667_);
v_skipConstInApp_boxed_1679_ = lean_unbox(v_skipConstInApp_1668_);
v_skipInstances_boxed_1680_ = lean_unbox(v_skipInstances_1669_);
v_res_1681_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1664_, v_pre_1665_, v_post_1666_, v_usedLetOnly_boxed_1678_, v_skipConstInApp_boxed_1679_, v_skipInstances_boxed_1680_, v_body_1670_, v_x_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1682_, lean_object* v_post_1683_, uint8_t v_usedLetOnly_1684_, uint8_t v_skipConstInApp_1685_, uint8_t v_skipInstances_1686_, lean_object* v_fvars_1687_, lean_object* v_e_1688_, lean_object* v_a_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
if (lean_obj_tag(v_e_1688_) == 8)
{
lean_object* v_declName_1695_; lean_object* v_type_1696_; lean_object* v_value_1697_; lean_object* v_body_1698_; uint8_t v_nondep_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_declName_1695_ = lean_ctor_get(v_e_1688_, 0);
lean_inc(v_declName_1695_);
v_type_1696_ = lean_ctor_get(v_e_1688_, 1);
lean_inc_ref(v_type_1696_);
v_value_1697_ = lean_ctor_get(v_e_1688_, 2);
lean_inc_ref(v_value_1697_);
v_body_1698_ = lean_ctor_get(v_e_1688_, 3);
lean_inc_ref(v_body_1698_);
v_nondep_1699_ = lean_ctor_get_uint8(v_e_1688_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1688_, 4);
v___x_1700_ = lean_expr_instantiate_rev(v_type_1696_, v_fvars_1687_);
lean_dec_ref(v_type_1696_);
lean_inc_ref(v_post_1683_);
lean_inc_ref(v_pre_1682_);
v___x_1701_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1682_, v_post_1683_, v_usedLetOnly_1684_, v_skipConstInApp_1685_, v_skipInstances_1686_, v___x_1700_, v_a_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = lean_expr_instantiate_rev(v_value_1697_, v_fvars_1687_);
lean_dec_ref(v_value_1697_);
lean_inc_ref(v_post_1683_);
lean_inc_ref(v_pre_1682_);
v___x_1704_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1682_, v_post_1683_, v_usedLetOnly_1684_, v_skipConstInApp_1685_, v_skipInstances_1686_, v___x_1703_, v_a_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; uint8_t v___x_1710_; lean_object* v___x_1711_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v___x_1706_ = lean_box(v_usedLetOnly_1684_);
v___x_1707_ = lean_box(v_skipConstInApp_1685_);
v___x_1708_ = lean_box(v_skipInstances_1686_);
v___f_1709_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1709_, 0, v_fvars_1687_);
lean_closure_set(v___f_1709_, 1, v_pre_1682_);
lean_closure_set(v___f_1709_, 2, v_post_1683_);
lean_closure_set(v___f_1709_, 3, v___x_1706_);
lean_closure_set(v___f_1709_, 4, v___x_1707_);
lean_closure_set(v___f_1709_, 5, v___x_1708_);
lean_closure_set(v___f_1709_, 6, v_body_1698_);
v___x_1710_ = 0;
v___x_1711_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1695_, v_a_1702_, v_a_1705_, v___f_1709_, v_nondep_1699_, v___x_1710_, v_a_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1711_;
}
else
{
lean_dec(v_a_1702_);
lean_dec_ref(v_body_1698_);
lean_dec(v_declName_1695_);
lean_dec_ref(v_fvars_1687_);
lean_dec_ref(v_post_1683_);
lean_dec_ref(v_pre_1682_);
return v___x_1704_;
}
}
else
{
lean_dec_ref(v_body_1698_);
lean_dec_ref(v_value_1697_);
lean_dec(v_declName_1695_);
lean_dec_ref(v_fvars_1687_);
lean_dec_ref(v_post_1683_);
lean_dec_ref(v_pre_1682_);
return v___x_1701_;
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_expr_instantiate_rev(v_e_1688_, v_fvars_1687_);
lean_dec_ref(v_e_1688_);
lean_inc_ref(v_post_1683_);
lean_inc_ref(v_pre_1682_);
v___x_1713_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1682_, v_post_1683_, v_usedLetOnly_1684_, v_skipConstInApp_1685_, v_skipInstances_1686_, v___x_1712_, v_a_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; uint8_t v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = 0;
v___x_1716_ = 1;
v___x_1717_ = l_Lean_Meta_mkLetFVars(v_fvars_1687_, v_a_1714_, v_usedLetOnly_1684_, v___x_1715_, v___x_1716_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec_ref(v_fvars_1687_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1682_, v_post_1683_, v_usedLetOnly_1684_, v_skipConstInApp_1685_, v_skipInstances_1686_, v_a_1718_, v_a_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1719_;
}
else
{
lean_dec_ref(v_post_1683_);
lean_dec_ref(v_pre_1682_);
return v___x_1717_;
}
}
else
{
lean_dec_ref(v_fvars_1687_);
lean_dec_ref(v_post_1683_);
lean_dec_ref(v_pre_1682_);
return v___x_1713_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1720_; lean_object* v_dummy_1721_; 
v___x_1720_ = lean_box(0);
v_dummy_1721_ = l_Lean_Expr_sort___override(v___x_1720_);
return v_dummy_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1722_, lean_object* v_post_1723_, uint8_t v_usedLetOnly_1724_, uint8_t v_skipConstInApp_1725_, uint8_t v_skipInstances_1726_, size_t v_sz_1727_, size_t v_i_1728_, lean_object* v_bs_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_lt(v_i_1728_, v_sz_1727_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_dec_ref(v_post_1723_);
lean_dec_ref(v_pre_1722_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_bs_1729_);
return v___x_1737_;
}
else
{
lean_object* v_v_1738_; lean_object* v___x_1739_; 
v_v_1738_ = lean_array_uget_borrowed(v_bs_1729_, v_i_1728_);
lean_inc(v_v_1738_);
lean_inc_ref(v_post_1723_);
lean_inc_ref(v_pre_1722_);
v___x_1739_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1722_, v_post_1723_, v_usedLetOnly_1724_, v_skipConstInApp_1725_, v_skipInstances_1726_, v_v_1738_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v_bs_x27_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = lean_unsigned_to_nat(0u);
v_bs_x27_1742_ = lean_array_uset(v_bs_1729_, v_i_1728_, v___x_1741_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1728_, v___x_1743_);
v___x_1745_ = lean_array_uset(v_bs_x27_1742_, v_i_1728_, v_a_1740_);
v_i_1728_ = v___x_1744_;
v_bs_1729_ = v___x_1745_;
goto _start;
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v_bs_1729_);
lean_dec_ref(v_post_1723_);
lean_dec_ref(v_pre_1722_);
v_a_1747_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1739_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1739_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1755_, lean_object* v_post_1756_, uint8_t v_usedLetOnly_1757_, uint8_t v_skipConstInApp_1758_, uint8_t v_skipInstances_1759_, lean_object* v___x_1760_, lean_object* v___y_1761_, lean_object* v_b_1762_, lean_object* v_a_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1755_, v_post_1756_, v_usedLetOnly_1757_, v_skipConstInApp_1758_, v_skipInstances_1759_, v___x_1760_, v___y_1761_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1779_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1779_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1774_ = lean_array_fset(v_b_1762_, v_a_1763_, v_a_1770_);
v___x_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1777_ = v___x_1772_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v_b_1762_);
v_a_1780_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1769_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1769_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1788_, lean_object* v_post_1789_, lean_object* v_usedLetOnly_1790_, lean_object* v_skipConstInApp_1791_, lean_object* v_skipInstances_1792_, lean_object* v___x_1793_, lean_object* v___y_1794_, lean_object* v_b_1795_, lean_object* v_a_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v_usedLetOnly_boxed_1802_; uint8_t v_skipConstInApp_boxed_1803_; uint8_t v_skipInstances_boxed_1804_; lean_object* v_res_1805_; 
v_usedLetOnly_boxed_1802_ = lean_unbox(v_usedLetOnly_1790_);
v_skipConstInApp_boxed_1803_ = lean_unbox(v_skipConstInApp_1791_);
v_skipInstances_boxed_1804_ = lean_unbox(v_skipInstances_1792_);
v_res_1805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1788_, v_post_1789_, v_usedLetOnly_boxed_1802_, v_skipConstInApp_boxed_1803_, v_skipInstances_boxed_1804_, v___x_1793_, v___y_1794_, v_b_1795_, v_a_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v_a_1796_);
lean_dec(v___y_1794_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1806_, lean_object* v___x_1807_, lean_object* v_pre_1808_, lean_object* v_post_1809_, uint8_t v_usedLetOnly_1810_, uint8_t v_skipConstInApp_1811_, uint8_t v_skipInstances_1812_, lean_object* v_a_1813_, lean_object* v_b_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___y_1822_; uint8_t v___x_1845_; 
v___x_1845_ = lean_nat_dec_lt(v_a_1813_, v_upperBound_1806_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
lean_dec(v_a_1813_);
lean_dec_ref(v_post_1809_);
lean_dec_ref(v_pre_1808_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_b_1814_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1847_ = lean_array_fget_borrowed(v_b_1814_, v_a_1813_);
v___x_1848_ = lean_array_get_size(v___x_1807_);
v___x_1849_ = lean_nat_dec_lt(v_a_1813_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; 
lean_inc(v___x_1847_);
v___x_1850_ = lean_box(v_usedLetOnly_1810_);
v___x_1851_ = lean_box(v_skipConstInApp_1811_);
v___x_1852_ = lean_box(v_skipInstances_1812_);
lean_inc(v_a_1813_);
lean_inc(v___y_1815_);
lean_inc_ref(v_post_1809_);
lean_inc_ref(v_pre_1808_);
v___f_1853_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1853_, 0, v_pre_1808_);
lean_closure_set(v___f_1853_, 1, v_post_1809_);
lean_closure_set(v___f_1853_, 2, v___x_1850_);
lean_closure_set(v___f_1853_, 3, v___x_1851_);
lean_closure_set(v___f_1853_, 4, v___x_1852_);
lean_closure_set(v___f_1853_, 5, v___x_1847_);
lean_closure_set(v___f_1853_, 6, v___y_1815_);
lean_closure_set(v___f_1853_, 7, v_b_1814_);
lean_closure_set(v___f_1853_, 8, v_a_1813_);
v___y_1822_ = v___f_1853_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1854_; uint8_t v_isInstance_1855_; 
v___x_1854_ = lean_array_fget_borrowed(v___x_1807_, v_a_1813_);
v_isInstance_1855_ = lean_ctor_get_uint8(v___x_1854_, sizeof(void*)*1 + 4);
if (v_isInstance_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___f_1859_; 
lean_inc(v___x_1847_);
v___x_1856_ = lean_box(v_usedLetOnly_1810_);
v___x_1857_ = lean_box(v_skipConstInApp_1811_);
v___x_1858_ = lean_box(v_skipInstances_1812_);
lean_inc(v_a_1813_);
lean_inc(v___y_1815_);
lean_inc_ref(v_post_1809_);
lean_inc_ref(v_pre_1808_);
v___f_1859_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1859_, 0, v_pre_1808_);
lean_closure_set(v___f_1859_, 1, v_post_1809_);
lean_closure_set(v___f_1859_, 2, v___x_1856_);
lean_closure_set(v___f_1859_, 3, v___x_1857_);
lean_closure_set(v___f_1859_, 4, v___x_1858_);
lean_closure_set(v___f_1859_, 5, v___x_1847_);
lean_closure_set(v___f_1859_, 6, v___y_1815_);
lean_closure_set(v___f_1859_, 7, v_b_1814_);
lean_closure_set(v___f_1859_, 8, v_a_1813_);
v___y_1822_ = v___f_1859_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1860_; lean_object* v___f_1861_; 
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_b_1814_);
v___f_1861_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1861_, 0, v___x_1860_);
v___y_1822_ = v___f_1861_;
goto v___jp_1821_;
}
}
}
v___jp_1821_:
{
lean_object* v___x_1823_; 
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1818_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
v___x_1823_ = lean_apply_5(v___y_1822_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, lean_box(0));
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1836_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1836_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1836_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
if (lean_obj_tag(v_a_1824_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; 
lean_dec(v_a_1813_);
lean_dec_ref(v_post_1809_);
lean_dec_ref(v_pre_1808_);
v_a_1828_ = lean_ctor_get(v_a_1824_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v_a_1824_, 1);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v_a_1828_);
v___x_1830_ = v___x_1826_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_del_object(v___x_1826_);
v_a_1832_ = lean_ctor_get(v_a_1824_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v_a_1824_, 1);
v___x_1833_ = lean_unsigned_to_nat(1u);
v___x_1834_ = lean_nat_add(v_a_1813_, v___x_1833_);
lean_dec(v_a_1813_);
v_a_1813_ = v___x_1834_;
v_b_1814_ = v_a_1832_;
goto _start;
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec(v_a_1813_);
lean_dec_ref(v_post_1809_);
lean_dec_ref(v_pre_1808_);
v_a_1837_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1823_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1823_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1862_, lean_object* v_pre_1863_, lean_object* v_post_1864_, uint8_t v_usedLetOnly_1865_, uint8_t v_skipConstInApp_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_f_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; 
if (lean_obj_tag(v_x_1867_) == 5)
{
lean_object* v_fn_1925_; lean_object* v_arg_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_fn_1925_ = lean_ctor_get(v_x_1867_, 0);
lean_inc_ref(v_fn_1925_);
v_arg_1926_ = lean_ctor_get(v_x_1867_, 1);
lean_inc_ref(v_arg_1926_);
lean_dec_ref_known(v_x_1867_, 2);
v___x_1927_ = lean_array_set(v_x_1868_, v_x_1869_, v_arg_1926_);
v___x_1928_ = lean_unsigned_to_nat(1u);
v___x_1929_ = lean_nat_sub(v_x_1869_, v___x_1928_);
lean_dec(v_x_1869_);
v_x_1867_ = v_fn_1925_;
v_x_1868_ = v___x_1927_;
v_x_1869_ = v___x_1929_;
goto _start;
}
else
{
lean_dec(v_x_1869_);
if (v_skipConstInApp_1866_ == 0)
{
goto v___jp_1922_;
}
else
{
uint8_t v___x_1931_; 
v___x_1931_ = l_Lean_Expr_isConst(v_x_1867_);
if (v___x_1931_ == 0)
{
goto v___jp_1922_;
}
else
{
v_f_1877_ = v_x_1867_;
v___y_1878_ = v___y_1870_;
v___y_1879_ = v___y_1871_;
v___y_1880_ = v___y_1872_;
v___y_1881_ = v___y_1873_;
v___y_1882_ = v___y_1874_;
goto v___jp_1876_;
}
}
}
v___jp_1876_:
{
if (v_skipInstances_1862_ == 0)
{
size_t v_sz_1883_; size_t v___x_1884_; lean_object* v___x_1885_; 
v_sz_1883_ = lean_array_size(v_x_1868_);
v___x_1884_ = ((size_t)0ULL);
lean_inc_ref(v_post_1864_);
lean_inc_ref(v_pre_1863_);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1863_, v_post_1864_, v_usedLetOnly_1865_, v_skipConstInApp_1866_, v_skipInstances_1862_, v_sz_1883_, v___x_1884_, v_x_1868_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = l_Lean_mkAppN(v_f_1877_, v_a_1886_);
lean_dec(v_a_1886_);
v___x_1888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1863_, v_post_1864_, v_usedLetOnly_1865_, v_skipConstInApp_1866_, v_skipInstances_1862_, v___x_1887_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
return v___x_1888_;
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_post_1864_);
lean_dec_ref(v_pre_1863_);
v_a_1889_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1885_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1885_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_array_get_size(v_x_1868_);
lean_inc_ref(v_f_1877_);
v___x_1898_ = l_Lean_Meta_getFunInfoNArgs(v_f_1877_, v___x_1897_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v_paramInfo_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___x_1898_, 1);
v_paramInfo_1900_ = lean_ctor_get(v_a_1899_, 0);
lean_inc_ref(v_paramInfo_1900_);
lean_dec(v_a_1899_);
v___x_1901_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1864_);
lean_inc_ref(v_pre_1863_);
v___x_1902_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1897_, v_paramInfo_1900_, v_pre_1863_, v_post_1864_, v_usedLetOnly_1865_, v_skipConstInApp_1866_, v_skipInstances_1862_, v___x_1901_, v_x_1868_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec_ref(v_paramInfo_1900_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = l_Lean_mkAppN(v_f_1877_, v_a_1903_);
lean_dec(v_a_1903_);
v___x_1905_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1863_, v_post_1864_, v_usedLetOnly_1865_, v_skipConstInApp_1866_, v_skipInstances_1862_, v___x_1904_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
return v___x_1905_;
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_post_1864_);
lean_dec_ref(v_pre_1863_);
v_a_1906_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1902_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1902_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v_f_1877_);
lean_dec_ref(v_x_1868_);
lean_dec_ref(v_post_1864_);
lean_dec_ref(v_pre_1863_);
v_a_1914_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1898_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1898_);
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
}
v___jp_1922_:
{
lean_object* v___x_1923_; 
lean_inc_ref(v_post_1864_);
lean_inc_ref(v_pre_1863_);
v___x_1923_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1863_, v_post_1864_, v_usedLetOnly_1865_, v_skipConstInApp_1866_, v_skipInstances_1862_, v_x_1867_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v_f_1877_ = v_a_1924_;
v___y_1878_ = v___y_1870_;
v___y_1879_ = v___y_1871_;
v___y_1880_ = v___y_1872_;
v___y_1881_ = v___y_1873_;
v___y_1882_ = v___y_1874_;
goto v___jp_1876_;
}
else
{
lean_dec_ref(v_x_1868_);
lean_dec_ref(v_post_1864_);
lean_dec_ref(v_pre_1863_);
return v___x_1923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1932_, lean_object* v_pre_1933_, lean_object* v_e_1934_, lean_object* v_post_1935_, uint8_t v_usedLetOnly_1936_, uint8_t v_skipConstInApp_1937_, uint8_t v_skipInstances_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_Core_checkSystem(v___x_1932_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v___x_1946_; 
lean_dec_ref_known(v___x_1945_, 1);
lean_inc_ref(v_pre_1933_);
lean_inc(v___y_1943_);
lean_inc_ref(v___y_1942_);
lean_inc(v___y_1941_);
lean_inc_ref(v___y_1940_);
lean_inc_ref(v_e_1934_);
v___x_1946_ = lean_apply_6(v_pre_1933_, v_e_1934_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, lean_box(0));
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1995_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_1995_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1995_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___y_1952_; 
switch(lean_obj_tag(v_a_1947_))
{
case 0:
{
lean_object* v_e_1987_; lean_object* v___x_1989_; 
lean_dec_ref(v_post_1935_);
lean_dec_ref(v_e_1934_);
lean_dec_ref(v_pre_1933_);
v_e_1987_ = lean_ctor_get(v_a_1947_, 0);
lean_inc_ref(v_e_1987_);
lean_dec_ref_known(v_a_1947_, 1);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v_e_1987_);
v___x_1989_ = v___x_1949_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_e_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
case 1:
{
lean_object* v_e_1991_; lean_object* v___x_1992_; 
lean_del_object(v___x_1949_);
lean_dec_ref(v_e_1934_);
v_e_1991_ = lean_ctor_get(v_a_1947_, 0);
lean_inc_ref(v_e_1991_);
lean_dec_ref_known(v_a_1947_, 1);
v___x_1992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v_e_1991_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1992_;
}
default: 
{
lean_object* v_e_x3f_1993_; 
lean_del_object(v___x_1949_);
v_e_x3f_1993_ = lean_ctor_get(v_a_1947_, 0);
lean_inc(v_e_x3f_1993_);
lean_dec_ref_known(v_a_1947_, 1);
if (lean_obj_tag(v_e_x3f_1993_) == 0)
{
v___y_1952_ = v_e_1934_;
goto v___jp_1951_;
}
else
{
lean_object* v_val_1994_; 
lean_dec_ref(v_e_1934_);
v_val_1994_ = lean_ctor_get(v_e_x3f_1993_, 0);
lean_inc(v_val_1994_);
lean_dec_ref_known(v_e_x3f_1993_, 1);
v___y_1952_ = v_val_1994_;
goto v___jp_1951_;
}
}
}
v___jp_1951_:
{
switch(lean_obj_tag(v___y_1952_))
{
case 7:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1954_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v___x_1953_, v___y_1952_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1954_;
}
case 6:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1956_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v___x_1955_, v___y_1952_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1956_;
}
case 8:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v___x_1957_, v___y_1952_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1958_;
}
case 5:
{
lean_object* v_dummy_1959_; lean_object* v_nargs_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_dummy_1959_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1960_ = l_Lean_Expr_getAppNumArgs(v___y_1952_);
lean_inc(v_nargs_1960_);
v___x_1961_ = lean_mk_array(v_nargs_1960_, v_dummy_1959_);
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_sub(v_nargs_1960_, v___x_1962_);
lean_dec(v_nargs_1960_);
v___x_1964_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1938_, v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v___y_1952_, v___x_1961_, v___x_1963_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1964_;
}
case 10:
{
lean_object* v_data_1965_; lean_object* v_expr_1966_; lean_object* v___x_1967_; 
v_data_1965_ = lean_ctor_get(v___y_1952_, 0);
v_expr_1966_ = lean_ctor_get(v___y_1952_, 1);
lean_inc_ref(v_expr_1966_);
lean_inc_ref(v_post_1935_);
lean_inc_ref(v_pre_1933_);
v___x_1967_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v_expr_1966_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; size_t v___x_1969_; size_t v___x_1970_; uint8_t v___x_1971_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = lean_ptr_addr(v_expr_1966_);
v___x_1970_ = lean_ptr_addr(v_a_1968_);
v___x_1971_ = lean_usize_dec_eq(v___x_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_inc(v_data_1965_);
lean_dec_ref_known(v___y_1952_, 2);
v___x_1972_ = l_Lean_Expr_mdata___override(v_data_1965_, v_a_1968_);
v___x_1973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v___x_1972_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; 
lean_dec(v_a_1968_);
v___x_1974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v___y_1952_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1974_;
}
}
else
{
lean_dec_ref_known(v___y_1952_, 2);
lean_dec_ref(v_post_1935_);
lean_dec_ref(v_pre_1933_);
return v___x_1967_;
}
}
case 11:
{
lean_object* v_typeName_1975_; lean_object* v_idx_1976_; lean_object* v_struct_1977_; lean_object* v___x_1978_; 
v_typeName_1975_ = lean_ctor_get(v___y_1952_, 0);
v_idx_1976_ = lean_ctor_get(v___y_1952_, 1);
v_struct_1977_ = lean_ctor_get(v___y_1952_, 2);
lean_inc_ref(v_struct_1977_);
lean_inc_ref(v_post_1935_);
lean_inc_ref(v_pre_1933_);
v___x_1978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v_struct_1977_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; size_t v___x_1980_; size_t v___x_1981_; uint8_t v___x_1982_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = lean_ptr_addr(v_struct_1977_);
v___x_1981_ = lean_ptr_addr(v_a_1979_);
v___x_1982_ = lean_usize_dec_eq(v___x_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_inc(v_idx_1976_);
lean_inc(v_typeName_1975_);
lean_dec_ref_known(v___y_1952_, 3);
v___x_1983_ = l_Lean_Expr_proj___override(v_typeName_1975_, v_idx_1976_, v_a_1979_);
v___x_1984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v___x_1983_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; 
lean_dec(v_a_1979_);
v___x_1985_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v___y_1952_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1985_;
}
}
else
{
lean_dec_ref_known(v___y_1952_, 3);
lean_dec_ref(v_post_1935_);
lean_dec_ref(v_pre_1933_);
return v___x_1978_;
}
}
default: 
{
lean_object* v___x_1986_; 
v___x_1986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1933_, v_post_1935_, v_usedLetOnly_1936_, v_skipConstInApp_1937_, v_skipInstances_1938_, v___y_1952_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1986_;
}
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_post_1935_);
lean_dec_ref(v_e_1934_);
lean_dec_ref(v_pre_1933_);
v_a_1996_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1946_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1946_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_post_1935_);
lean_dec_ref(v_e_1934_);
lean_dec_ref(v_pre_1933_);
v_a_2004_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1945_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1945_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2012_, lean_object* v_pre_2013_, lean_object* v_e_2014_, lean_object* v_post_2015_, lean_object* v_usedLetOnly_2016_, lean_object* v_skipConstInApp_2017_, lean_object* v_skipInstances_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
uint8_t v_usedLetOnly_boxed_2025_; uint8_t v_skipConstInApp_boxed_2026_; uint8_t v_skipInstances_boxed_2027_; lean_object* v_res_2028_; 
v_usedLetOnly_boxed_2025_ = lean_unbox(v_usedLetOnly_2016_);
v_skipConstInApp_boxed_2026_ = lean_unbox(v_skipConstInApp_2017_);
v_skipInstances_boxed_2027_ = lean_unbox(v_skipInstances_2018_);
v_res_2028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2012_, v_pre_2013_, v_e_2014_, v_post_2015_, v_usedLetOnly_boxed_2025_, v_skipConstInApp_boxed_2026_, v_skipInstances_boxed_2027_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2029_, lean_object* v_post_2030_, uint8_t v_usedLetOnly_2031_, uint8_t v_skipConstInApp_2032_, uint8_t v_skipInstances_2033_, lean_object* v_e_2034_, lean_object* v_a_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
lean_inc(v_a_2035_);
v___x_2041_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2041_, 0, lean_box(0));
lean_closure_set(v___x_2041_, 1, lean_box(0));
lean_closure_set(v___x_2041_, 2, v_a_2035_);
v___x_2042_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2041_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2077_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2077_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2077_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2043_, v_e_2034_);
lean_dec(v_a_2043_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___f_2052_; lean_object* v___x_2053_; 
lean_del_object(v___x_2045_);
v___x_2048_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2049_ = lean_box(v_usedLetOnly_2031_);
v___x_2050_ = lean_box(v_skipConstInApp_2032_);
v___x_2051_ = lean_box(v_skipInstances_2033_);
lean_inc_ref(v_e_2034_);
v___f_2052_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2052_, 0, v___x_2048_);
lean_closure_set(v___f_2052_, 1, v_pre_2029_);
lean_closure_set(v___f_2052_, 2, v_e_2034_);
lean_closure_set(v___f_2052_, 3, v_post_2030_);
lean_closure_set(v___f_2052_, 4, v___x_2049_);
lean_closure_set(v___f_2052_, 5, v___x_2050_);
lean_closure_set(v___f_2052_, 6, v___x_2051_);
v___x_2053_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2052_, v_a_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___f_2055_; lean_object* v___x_2056_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_n(v_a_2054_, 2);
lean_dec_ref_known(v___x_2053_, 1);
lean_inc(v_a_2035_);
v___f_2055_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2055_, 0, v_a_2035_);
lean_closure_set(v___f_2055_, 1, v_e_2034_);
lean_closure_set(v___f_2055_, 2, v_a_2054_);
v___x_2056_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2055_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_2056_, 0);
lean_dec(v_unused_2064_);
v___x_2058_ = v___x_2056_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v___x_2056_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_a_2054_);
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2054_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v_a_2054_);
v_a_2065_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2056_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2056_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_dec_ref(v_e_2034_);
return v___x_2053_;
}
}
else
{
lean_object* v_val_2073_; lean_object* v___x_2075_; 
lean_dec_ref(v_e_2034_);
lean_dec_ref(v_post_2030_);
lean_dec_ref(v_pre_2029_);
v_val_2073_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_val_2073_);
lean_dec_ref_known(v___x_2047_, 1);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v_val_2073_);
v___x_2075_ = v___x_2045_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_val_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_e_2034_);
lean_dec_ref(v_post_2030_);
lean_dec_ref(v_pre_2029_);
v_a_2078_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2042_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2042_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_2086_, lean_object* v_pre_2087_, lean_object* v_post_2088_, lean_object* v_usedLetOnly_2089_, lean_object* v_skipConstInApp_2090_, lean_object* v_skipInstances_2091_, lean_object* v_body_2092_, lean_object* v_x_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v_usedLetOnly_boxed_2100_; uint8_t v_skipConstInApp_boxed_2101_; uint8_t v_skipInstances_boxed_2102_; lean_object* v_res_2103_; 
v_usedLetOnly_boxed_2100_ = lean_unbox(v_usedLetOnly_2089_);
v_skipConstInApp_boxed_2101_ = lean_unbox(v_skipConstInApp_2090_);
v_skipInstances_boxed_2102_ = lean_unbox(v_skipInstances_2091_);
v_res_2103_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2086_, v_pre_2087_, v_post_2088_, v_usedLetOnly_boxed_2100_, v_skipConstInApp_boxed_2101_, v_skipInstances_boxed_2102_, v_body_2092_, v_x_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2104_, lean_object* v_post_2105_, uint8_t v_usedLetOnly_2106_, uint8_t v_skipConstInApp_2107_, uint8_t v_skipInstances_2108_, lean_object* v_fvars_2109_, lean_object* v_e_2110_, lean_object* v_a_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
if (lean_obj_tag(v_e_2110_) == 7)
{
lean_object* v_binderName_2117_; lean_object* v_binderType_2118_; lean_object* v_body_2119_; uint8_t v_binderInfo_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_binderName_2117_ = lean_ctor_get(v_e_2110_, 0);
lean_inc(v_binderName_2117_);
v_binderType_2118_ = lean_ctor_get(v_e_2110_, 1);
lean_inc_ref(v_binderType_2118_);
v_body_2119_ = lean_ctor_get(v_e_2110_, 2);
lean_inc_ref(v_body_2119_);
v_binderInfo_2120_ = lean_ctor_get_uint8(v_e_2110_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2110_, 3);
v___x_2121_ = lean_expr_instantiate_rev(v_binderType_2118_, v_fvars_2109_);
lean_dec_ref(v_binderType_2118_);
lean_inc_ref(v_post_2105_);
lean_inc_ref(v_pre_2104_);
v___x_2122_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2104_, v_post_2105_, v_usedLetOnly_2106_, v_skipConstInApp_2107_, v_skipInstances_2108_, v___x_2121_, v_a_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___f_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = lean_box(v_usedLetOnly_2106_);
v___x_2125_ = lean_box(v_skipConstInApp_2107_);
v___x_2126_ = lean_box(v_skipInstances_2108_);
v___f_2127_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2127_, 0, v_fvars_2109_);
lean_closure_set(v___f_2127_, 1, v_pre_2104_);
lean_closure_set(v___f_2127_, 2, v_post_2105_);
lean_closure_set(v___f_2127_, 3, v___x_2124_);
lean_closure_set(v___f_2127_, 4, v___x_2125_);
lean_closure_set(v___f_2127_, 5, v___x_2126_);
lean_closure_set(v___f_2127_, 6, v_body_2119_);
v___x_2128_ = 0;
v___x_2129_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2117_, v_binderInfo_2120_, v_a_2123_, v___f_2127_, v___x_2128_, v_a_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2129_;
}
else
{
lean_dec_ref(v_body_2119_);
lean_dec(v_binderName_2117_);
lean_dec_ref(v_fvars_2109_);
lean_dec_ref(v_post_2105_);
lean_dec_ref(v_pre_2104_);
return v___x_2122_;
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_expr_instantiate_rev(v_e_2110_, v_fvars_2109_);
lean_dec_ref(v_e_2110_);
lean_inc_ref(v_post_2105_);
lean_inc_ref(v_pre_2104_);
v___x_2131_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2104_, v_post_2105_, v_usedLetOnly_2106_, v_skipConstInApp_2107_, v_skipInstances_2108_, v___x_2130_, v_a_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; uint8_t v___x_2133_; uint8_t v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = 0;
v___x_2134_ = 1;
v___x_2135_ = 1;
v___x_2136_ = l_Lean_Meta_mkForallFVars(v_fvars_2109_, v_a_2132_, v___x_2133_, v_usedLetOnly_2106_, v___x_2134_, v___x_2135_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec_ref(v_fvars_2109_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2104_, v_post_2105_, v_usedLetOnly_2106_, v_skipConstInApp_2107_, v_skipInstances_2108_, v_a_2137_, v_a_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2138_;
}
else
{
lean_dec_ref(v_post_2105_);
lean_dec_ref(v_pre_2104_);
return v___x_2136_;
}
}
else
{
lean_dec_ref(v_fvars_2109_);
lean_dec_ref(v_post_2105_);
lean_dec_ref(v_pre_2104_);
return v___x_2131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2139_, lean_object* v_pre_2140_, lean_object* v_post_2141_, uint8_t v_usedLetOnly_2142_, uint8_t v_skipConstInApp_2143_, uint8_t v_skipInstances_2144_, lean_object* v_body_2145_, lean_object* v_x_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_array_push(v_fvars_2139_, v_x_2146_);
v___x_2154_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2140_, v_post_2141_, v_usedLetOnly_2142_, v_skipConstInApp_2143_, v_skipInstances_2144_, v___x_2153_, v_body_2145_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2155_, lean_object* v_post_2156_, lean_object* v_usedLetOnly_2157_, lean_object* v_skipConstInApp_2158_, lean_object* v_skipInstances_2159_, lean_object* v_e_2160_, lean_object* v_a_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_usedLetOnly_boxed_2167_; uint8_t v_skipConstInApp_boxed_2168_; uint8_t v_skipInstances_boxed_2169_; lean_object* v_res_2170_; 
v_usedLetOnly_boxed_2167_ = lean_unbox(v_usedLetOnly_2157_);
v_skipConstInApp_boxed_2168_ = lean_unbox(v_skipConstInApp_2158_);
v_skipInstances_boxed_2169_ = lean_unbox(v_skipInstances_2159_);
v_res_2170_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2155_, v_post_2156_, v_usedLetOnly_boxed_2167_, v_skipConstInApp_boxed_2168_, v_skipInstances_boxed_2169_, v_e_2160_, v_a_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v_a_2161_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2171_, lean_object* v_post_2172_, lean_object* v_usedLetOnly_2173_, lean_object* v_skipConstInApp_2174_, lean_object* v_skipInstances_2175_, lean_object* v_sz_2176_, lean_object* v_i_2177_, lean_object* v_bs_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
uint8_t v_usedLetOnly_boxed_2185_; uint8_t v_skipConstInApp_boxed_2186_; uint8_t v_skipInstances_boxed_2187_; size_t v_sz_boxed_2188_; size_t v_i_boxed_2189_; lean_object* v_res_2190_; 
v_usedLetOnly_boxed_2185_ = lean_unbox(v_usedLetOnly_2173_);
v_skipConstInApp_boxed_2186_ = lean_unbox(v_skipConstInApp_2174_);
v_skipInstances_boxed_2187_ = lean_unbox(v_skipInstances_2175_);
v_sz_boxed_2188_ = lean_unbox_usize(v_sz_2176_);
lean_dec(v_sz_2176_);
v_i_boxed_2189_ = lean_unbox_usize(v_i_2177_);
lean_dec(v_i_2177_);
v_res_2190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2171_, v_post_2172_, v_usedLetOnly_boxed_2185_, v_skipConstInApp_boxed_2186_, v_skipInstances_boxed_2187_, v_sz_boxed_2188_, v_i_boxed_2189_, v_bs_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2191_, lean_object* v_post_2192_, lean_object* v_usedLetOnly_2193_, lean_object* v_skipConstInApp_2194_, lean_object* v_skipInstances_2195_, lean_object* v_e_2196_, lean_object* v_a_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v_usedLetOnly_boxed_2203_; uint8_t v_skipConstInApp_boxed_2204_; uint8_t v_skipInstances_boxed_2205_; lean_object* v_res_2206_; 
v_usedLetOnly_boxed_2203_ = lean_unbox(v_usedLetOnly_2193_);
v_skipConstInApp_boxed_2204_ = lean_unbox(v_skipConstInApp_2194_);
v_skipInstances_boxed_2205_ = lean_unbox(v_skipInstances_2195_);
v_res_2206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2191_, v_post_2192_, v_usedLetOnly_boxed_2203_, v_skipConstInApp_boxed_2204_, v_skipInstances_boxed_2205_, v_e_2196_, v_a_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v_a_2197_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2207_, lean_object* v_post_2208_, lean_object* v_usedLetOnly_2209_, lean_object* v_skipConstInApp_2210_, lean_object* v_skipInstances_2211_, lean_object* v_fvars_2212_, lean_object* v_e_2213_, lean_object* v_a_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
uint8_t v_usedLetOnly_boxed_2220_; uint8_t v_skipConstInApp_boxed_2221_; uint8_t v_skipInstances_boxed_2222_; lean_object* v_res_2223_; 
v_usedLetOnly_boxed_2220_ = lean_unbox(v_usedLetOnly_2209_);
v_skipConstInApp_boxed_2221_ = lean_unbox(v_skipConstInApp_2210_);
v_skipInstances_boxed_2222_ = lean_unbox(v_skipInstances_2211_);
v_res_2223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2207_, v_post_2208_, v_usedLetOnly_boxed_2220_, v_skipConstInApp_boxed_2221_, v_skipInstances_boxed_2222_, v_fvars_2212_, v_e_2213_, v_a_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v_a_2214_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2224_, lean_object* v_post_2225_, lean_object* v_usedLetOnly_2226_, lean_object* v_skipConstInApp_2227_, lean_object* v_skipInstances_2228_, lean_object* v_fvars_2229_, lean_object* v_e_2230_, lean_object* v_a_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
uint8_t v_usedLetOnly_boxed_2237_; uint8_t v_skipConstInApp_boxed_2238_; uint8_t v_skipInstances_boxed_2239_; lean_object* v_res_2240_; 
v_usedLetOnly_boxed_2237_ = lean_unbox(v_usedLetOnly_2226_);
v_skipConstInApp_boxed_2238_ = lean_unbox(v_skipConstInApp_2227_);
v_skipInstances_boxed_2239_ = lean_unbox(v_skipInstances_2228_);
v_res_2240_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2224_, v_post_2225_, v_usedLetOnly_boxed_2237_, v_skipConstInApp_boxed_2238_, v_skipInstances_boxed_2239_, v_fvars_2229_, v_e_2230_, v_a_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v_a_2231_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2241_, lean_object* v_post_2242_, lean_object* v_usedLetOnly_2243_, lean_object* v_skipConstInApp_2244_, lean_object* v_skipInstances_2245_, lean_object* v_fvars_2246_, lean_object* v_e_2247_, lean_object* v_a_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
uint8_t v_usedLetOnly_boxed_2254_; uint8_t v_skipConstInApp_boxed_2255_; uint8_t v_skipInstances_boxed_2256_; lean_object* v_res_2257_; 
v_usedLetOnly_boxed_2254_ = lean_unbox(v_usedLetOnly_2243_);
v_skipConstInApp_boxed_2255_ = lean_unbox(v_skipConstInApp_2244_);
v_skipInstances_boxed_2256_ = lean_unbox(v_skipInstances_2245_);
v_res_2257_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2241_, v_post_2242_, v_usedLetOnly_boxed_2254_, v_skipConstInApp_boxed_2255_, v_skipInstances_boxed_2256_, v_fvars_2246_, v_e_2247_, v_a_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v_a_2248_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2258_, lean_object* v___x_2259_, lean_object* v_pre_2260_, lean_object* v_post_2261_, lean_object* v_usedLetOnly_2262_, lean_object* v_skipConstInApp_2263_, lean_object* v_skipInstances_2264_, lean_object* v_a_2265_, lean_object* v_b_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
uint8_t v_usedLetOnly_boxed_2273_; uint8_t v_skipConstInApp_boxed_2274_; uint8_t v_skipInstances_boxed_2275_; lean_object* v_res_2276_; 
v_usedLetOnly_boxed_2273_ = lean_unbox(v_usedLetOnly_2262_);
v_skipConstInApp_boxed_2274_ = lean_unbox(v_skipConstInApp_2263_);
v_skipInstances_boxed_2275_ = lean_unbox(v_skipInstances_2264_);
v_res_2276_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2258_, v___x_2259_, v_pre_2260_, v_post_2261_, v_usedLetOnly_boxed_2273_, v_skipConstInApp_boxed_2274_, v_skipInstances_boxed_2275_, v_a_2265_, v_b_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___x_2259_);
lean_dec(v_upperBound_2258_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2277_, lean_object* v_pre_2278_, lean_object* v_post_2279_, lean_object* v_usedLetOnly_2280_, lean_object* v_skipConstInApp_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v_skipInstances_boxed_2291_; uint8_t v_usedLetOnly_boxed_2292_; uint8_t v_skipConstInApp_boxed_2293_; lean_object* v_res_2294_; 
v_skipInstances_boxed_2291_ = lean_unbox(v_skipInstances_2277_);
v_usedLetOnly_boxed_2292_ = lean_unbox(v_usedLetOnly_2280_);
v_skipConstInApp_boxed_2293_ = lean_unbox(v_skipConstInApp_2281_);
v_res_2294_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2291_, v_pre_2278_, v_post_2279_, v_usedLetOnly_boxed_2292_, v_skipConstInApp_boxed_2293_, v_x_2282_, v_x_2283_, v_x_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
return v_res_2294_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2296_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2296_, 0, lean_box(0));
lean_closure_set(v___x_2296_, 1, lean_box(0));
lean_closure_set(v___x_2296_, 2, v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2297_, lean_object* v_pre_2298_, lean_object* v_post_2299_, uint8_t v_usedLetOnly_2300_, uint8_t v_skipConstInApp_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_a_2309_; uint8_t v___x_2310_; lean_object* v___x_2311_; 
v___x_2307_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2308_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2307_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = 0;
v___x_2311_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2298_, v_post_2299_, v_usedLetOnly_2300_, v_skipConstInApp_2301_, v___x_2310_, v_input_2297_, v_a_2309_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2313_, 0, lean_box(0));
lean_closure_set(v___x_2313_, 1, lean_box(0));
lean_closure_set(v___x_2313_, 2, v_a_2309_);
v___x_2314_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2313_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v___x_2314_, 0);
lean_dec(v_unused_2322_);
v___x_2316_ = v___x_2314_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_dec(v___x_2314_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v_a_2312_);
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2312_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_dec(v_a_2309_);
return v___x_2311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2323_, lean_object* v_pre_2324_, lean_object* v_post_2325_, lean_object* v_usedLetOnly_2326_, lean_object* v_skipConstInApp_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v_usedLetOnly_boxed_2333_; uint8_t v_skipConstInApp_boxed_2334_; lean_object* v_res_2335_; 
v_usedLetOnly_boxed_2333_ = lean_unbox(v_usedLetOnly_2326_);
v_skipConstInApp_boxed_2334_ = lean_unbox(v_skipConstInApp_2327_);
v_res_2335_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2323_, v_pre_2324_, v_post_2325_, v_usedLetOnly_boxed_2333_, v_skipConstInApp_boxed_2334_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2336_, lean_object* v_as_2337_, lean_object* v_j_2338_){
_start:
{
lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = lean_array_get_size(v_as_2337_);
v___x_2340_ = lean_nat_dec_lt(v_j_2338_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
lean_dec(v_j_2338_);
v___x_2341_ = lean_box(0);
return v___x_2341_;
}
else
{
lean_object* v___x_2342_; lean_object* v_declName_2343_; uint8_t v___x_2344_; 
v___x_2342_ = lean_array_fget_borrowed(v_as_2337_, v_j_2338_);
v_declName_2343_ = lean_ctor_get(v___x_2342_, 3);
v___x_2344_ = lean_name_eq(v_declName_2343_, v___x_2336_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_unsigned_to_nat(1u);
v___x_2346_ = lean_nat_add(v_j_2338_, v___x_2345_);
lean_dec(v_j_2338_);
v_j_2338_ = v___x_2346_;
goto _start;
}
else
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_j_2338_);
return v___x_2348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2349_, lean_object* v_as_2350_, lean_object* v_j_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2349_, v_as_2350_, v_j_2351_);
lean_dec_ref(v_as_2350_);
lean_dec(v___x_2349_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_st_ref_get(v_val_2353_);
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_val_2361_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2368_, lean_object* v_val_2369_, lean_object* v_a_2370_, lean_object* v___x_2371_, lean_object* v_____r_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2378_ = lean_st_ref_take(v_val_2368_);
v___x_2379_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2369_, v_a_2370_, v___x_2378_);
v___x_2380_ = lean_st_ref_put(v_val_2368_, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2371_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2383_, lean_object* v_val_2384_, lean_object* v_a_2385_, lean_object* v___x_2386_, lean_object* v_____r_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2383_, v_val_2384_, v_a_2385_, v___x_2386_, v_____r_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v_val_2384_);
lean_dec(v_val_2383_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2394_, lean_object* v_val_2395_, lean_object* v_next_2396_, lean_object* v_next_2397_, lean_object* v___x_2398_, lean_object* v___x_2399_, lean_object* v_upperBound_2400_, lean_object* v_params_2401_, lean_object* v___x_2402_, lean_object* v_a_2403_, uint8_t v_b_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v_a_2411_; uint8_t v___x_2415_; 
v___x_2415_ = lean_nat_dec_lt(v_a_2403_, v_upperBound_2400_);
if (v___x_2415_ == 0)
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec(v_a_2403_);
lean_dec_ref(v___x_2402_);
lean_dec(v_next_2396_);
v___x_2416_ = lean_box(v_b_2404_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = lean_st_ref_get(v_val_2394_);
v___x_2419_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2397_, v_a_2403_, v___x_2418_);
lean_dec(v___x_2418_);
if (v___x_2419_ == 0)
{
v_a_2411_ = v_b_2404_;
goto v___jp_2410_;
}
else
{
lean_object* v___x_2420_; uint8_t v_foApprox_2421_; uint8_t v_ctxApprox_2422_; uint8_t v_quasiPatternApprox_2423_; uint8_t v_constApprox_2424_; uint8_t v_isDefEqStuckEx_2425_; uint8_t v_unificationHints_2426_; uint8_t v_assignSyntheticOpaque_2427_; uint8_t v_offsetCnstrs_2428_; uint8_t v_transparency_2429_; uint8_t v_etaStruct_2430_; uint8_t v_univApprox_2431_; uint8_t v_iota_2432_; uint8_t v_beta_2433_; uint8_t v_proj_2434_; uint8_t v_zeta_2435_; uint8_t v_zetaDelta_2436_; uint8_t v_zetaUnused_2437_; uint8_t v_zetaHave_2438_; uint8_t v_canUnfoldPredicateConfig_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2485_; 
v___x_2420_ = l_Lean_Meta_Context_config(v___y_2405_);
v_foApprox_2421_ = lean_ctor_get_uint8(v___x_2420_, 0);
v_ctxApprox_2422_ = lean_ctor_get_uint8(v___x_2420_, 1);
v_quasiPatternApprox_2423_ = lean_ctor_get_uint8(v___x_2420_, 2);
v_constApprox_2424_ = lean_ctor_get_uint8(v___x_2420_, 3);
v_isDefEqStuckEx_2425_ = lean_ctor_get_uint8(v___x_2420_, 4);
v_unificationHints_2426_ = lean_ctor_get_uint8(v___x_2420_, 5);
v_assignSyntheticOpaque_2427_ = lean_ctor_get_uint8(v___x_2420_, 7);
v_offsetCnstrs_2428_ = lean_ctor_get_uint8(v___x_2420_, 8);
v_transparency_2429_ = lean_ctor_get_uint8(v___x_2420_, 9);
v_etaStruct_2430_ = lean_ctor_get_uint8(v___x_2420_, 10);
v_univApprox_2431_ = lean_ctor_get_uint8(v___x_2420_, 11);
v_iota_2432_ = lean_ctor_get_uint8(v___x_2420_, 12);
v_beta_2433_ = lean_ctor_get_uint8(v___x_2420_, 13);
v_proj_2434_ = lean_ctor_get_uint8(v___x_2420_, 14);
v_zeta_2435_ = lean_ctor_get_uint8(v___x_2420_, 15);
v_zetaDelta_2436_ = lean_ctor_get_uint8(v___x_2420_, 16);
v_zetaUnused_2437_ = lean_ctor_get_uint8(v___x_2420_, 17);
v_zetaHave_2438_ = lean_ctor_get_uint8(v___x_2420_, 18);
v_canUnfoldPredicateConfig_2439_ = lean_ctor_get_uint8(v___x_2420_, 19);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2441_ = v___x_2420_;
v_isShared_2442_ = v_isSharedCheck_2485_;
goto v_resetjp_2440_;
}
else
{
lean_dec(v___x_2420_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2485_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
uint8_t v_trackZetaDelta_2443_; lean_object* v_zetaDeltaSet_2444_; lean_object* v_lctx_2445_; lean_object* v_localInstances_2446_; lean_object* v_defEqCtx_x3f_2447_; lean_object* v_synthPendingDepth_2448_; lean_object* v_customCanUnfoldPredicate_x3f_2449_; uint8_t v_univApprox_2450_; uint8_t v_inTypeClassResolution_2451_; uint8_t v_cacheInferType_2452_; uint8_t v___x_2453_; lean_object* v___x_2455_; 
v_trackZetaDelta_2443_ = lean_ctor_get_uint8(v___y_2405_, sizeof(void*)*7);
v_zetaDeltaSet_2444_ = lean_ctor_get(v___y_2405_, 1);
v_lctx_2445_ = lean_ctor_get(v___y_2405_, 2);
v_localInstances_2446_ = lean_ctor_get(v___y_2405_, 3);
v_defEqCtx_x3f_2447_ = lean_ctor_get(v___y_2405_, 4);
v_synthPendingDepth_2448_ = lean_ctor_get(v___y_2405_, 5);
v_customCanUnfoldPredicate_x3f_2449_ = lean_ctor_get(v___y_2405_, 6);
v_univApprox_2450_ = lean_ctor_get_uint8(v___y_2405_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2451_ = lean_ctor_get_uint8(v___y_2405_, sizeof(void*)*7 + 2);
v_cacheInferType_2452_ = lean_ctor_get_uint8(v___y_2405_, sizeof(void*)*7 + 3);
v___x_2453_ = 0;
if (v_isShared_2442_ == 0)
{
v___x_2455_ = v___x_2441_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 0, v_foApprox_2421_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 1, v_ctxApprox_2422_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 2, v_quasiPatternApprox_2423_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 3, v_constApprox_2424_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 4, v_isDefEqStuckEx_2425_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 5, v_unificationHints_2426_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 7, v_assignSyntheticOpaque_2427_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 8, v_offsetCnstrs_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 9, v_transparency_2429_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 10, v_etaStruct_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 11, v_univApprox_2431_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 12, v_iota_2432_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 13, v_beta_2433_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 14, v_proj_2434_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 15, v_zeta_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 16, v_zetaDelta_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 17, v_zetaUnused_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 18, v_zetaHave_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, 19, v_canUnfoldPredicateConfig_2439_);
v___x_2455_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
uint64_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v_transparency_2460_; uint8_t v___x_2461_; lean_object* v___y_2463_; lean_object* v___x_2477_; uint8_t v___x_2478_; uint8_t v___x_2479_; 
lean_ctor_set_uint8(v___x_2455_, 6, v___x_2453_);
v___x_2456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2455_);
v___x_2457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set_uint64(v___x_2457_, sizeof(void*)*1, v___x_2456_);
lean_inc(v_customCanUnfoldPredicate_x3f_2449_);
lean_inc(v_synthPendingDepth_2448_);
lean_inc(v_defEqCtx_x3f_2447_);
lean_inc_ref(v_localInstances_2446_);
lean_inc_ref(v_lctx_2445_);
lean_inc(v_zetaDeltaSet_2444_);
lean_inc_ref(v___x_2457_);
v___x_2458_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v_zetaDeltaSet_2444_);
lean_ctor_set(v___x_2458_, 2, v_lctx_2445_);
lean_ctor_set(v___x_2458_, 3, v_localInstances_2446_);
lean_ctor_set(v___x_2458_, 4, v_defEqCtx_x3f_2447_);
lean_ctor_set(v___x_2458_, 5, v_synthPendingDepth_2448_);
lean_ctor_set(v___x_2458_, 6, v_customCanUnfoldPredicate_x3f_2449_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7, v_trackZetaDelta_2443_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 1, v_univApprox_2450_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2451_);
lean_ctor_set_uint8(v___x_2458_, sizeof(void*)*7 + 3, v_cacheInferType_2452_);
v___x_2459_ = l_Lean_Meta_Context_config(v___x_2458_);
v_transparency_2460_ = lean_ctor_get_uint8(v___x_2459_, 9);
lean_dec_ref(v___x_2459_);
v___x_2461_ = lean_nat_dec_eq(v___x_2398_, v___x_2399_);
v___x_2477_ = lean_array_fget_borrowed(v_params_2401_, v_a_2403_);
v___x_2478_ = 2;
v___x_2479_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2460_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec_ref_known(v___x_2458_, 7);
v___x_2480_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2478_, v___x_2457_);
lean_inc(v_customCanUnfoldPredicate_x3f_2449_);
lean_inc(v_synthPendingDepth_2448_);
lean_inc(v_defEqCtx_x3f_2447_);
lean_inc_ref(v_localInstances_2446_);
lean_inc_ref(v_lctx_2445_);
lean_inc(v_zetaDeltaSet_2444_);
v___x_2481_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v_zetaDeltaSet_2444_);
lean_ctor_set(v___x_2481_, 2, v_lctx_2445_);
lean_ctor_set(v___x_2481_, 3, v_localInstances_2446_);
lean_ctor_set(v___x_2481_, 4, v_defEqCtx_x3f_2447_);
lean_ctor_set(v___x_2481_, 5, v_synthPendingDepth_2448_);
lean_ctor_set(v___x_2481_, 6, v_customCanUnfoldPredicate_x3f_2449_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*7, v_trackZetaDelta_2443_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*7 + 1, v_univApprox_2450_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2451_);
lean_ctor_set_uint8(v___x_2481_, sizeof(void*)*7 + 3, v_cacheInferType_2452_);
lean_inc_ref(v___x_2402_);
lean_inc(v___x_2477_);
v___x_2482_ = l_Lean_Meta_isExprDefEq(v___x_2477_, v___x_2402_, v___x_2481_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref_known(v___x_2481_, 7);
v___y_2463_ = v___x_2482_;
goto v___jp_2462_;
}
else
{
lean_object* v___x_2483_; 
lean_dec_ref_known(v___x_2457_, 1);
lean_inc_ref(v___x_2402_);
lean_inc(v___x_2477_);
v___x_2483_ = l_Lean_Meta_isExprDefEq(v___x_2477_, v___x_2402_, v___x_2458_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref_known(v___x_2458_, 7);
v___y_2463_ = v___x_2483_;
goto v___jp_2462_;
}
v___jp_2462_:
{
if (lean_obj_tag(v___y_2463_) == 0)
{
lean_object* v_a_2464_; uint8_t v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___y_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___y_2463_, 1);
v___x_2465_ = lean_unbox(v_a_2464_);
lean_dec(v_a_2464_);
if (v___x_2465_ == 0)
{
v_a_2411_ = v_b_2404_;
goto v___jp_2410_;
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_st_ref_take(v_val_2394_);
lean_inc(v_a_2403_);
lean_inc(v_next_2396_);
v___x_2467_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2395_, v_next_2396_, v_next_2397_, v_a_2403_, v___x_2466_);
v___x_2468_ = lean_st_ref_put(v_val_2394_, v___x_2467_);
v_a_2411_ = v___x_2461_;
goto v___jp_2410_;
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_a_2403_);
lean_dec_ref(v___x_2402_);
lean_dec(v_next_2396_);
v_a_2469_ = lean_ctor_get(v___y_2463_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___y_2463_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___y_2463_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___y_2463_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
}
}
v___jp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_unsigned_to_nat(1u);
v___x_2413_ = lean_nat_add(v_a_2403_, v___x_2412_);
lean_dec(v_a_2403_);
v_a_2403_ = v___x_2413_;
v_b_2404_ = v_a_2411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2486_, lean_object* v_val_2487_, lean_object* v_next_2488_, lean_object* v_next_2489_, lean_object* v___x_2490_, lean_object* v___x_2491_, lean_object* v_upperBound_2492_, lean_object* v_params_2493_, lean_object* v___x_2494_, lean_object* v_a_2495_, lean_object* v_b_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_b_boxed_2502_; lean_object* v_res_2503_; 
v_b_boxed_2502_ = lean_unbox(v_b_2496_);
v_res_2503_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2486_, v_val_2487_, v_next_2488_, v_next_2489_, v___x_2490_, v___x_2491_, v_upperBound_2492_, v_params_2493_, v___x_2494_, v_a_2495_, v_b_boxed_2502_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v_params_2493_);
lean_dec(v_upperBound_2492_);
lean_dec(v___x_2491_);
lean_dec(v___x_2490_);
lean_dec(v_next_2489_);
lean_dec(v_val_2487_);
lean_dec(v_val_2486_);
return v_res_2503_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2515_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2516_ = l_Lean_Name_append(v___x_2515_, v___x_2514_);
return v___x_2516_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2519_ = l_Lean_stringToMessageData(v___x_2518_);
return v___x_2519_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2521_ = l_Lean_stringToMessageData(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2527_ = l_Lean_stringToMessageData(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2530_ = l_Lean_stringToMessageData(v___x_2529_);
return v___x_2530_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2533_ = l_Lean_stringToMessageData(v___x_2532_);
return v___x_2533_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2536_ = l_Lean_stringToMessageData(v___x_2535_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2537_, lean_object* v_val_2538_, lean_object* v_upperBound_2539_, lean_object* v_args_2540_, lean_object* v_e_2541_, lean_object* v_next_2542_, lean_object* v_params_2543_, lean_object* v___x_2544_, lean_object* v___x_2545_, lean_object* v_a_2546_, lean_object* v_b_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_a_2554_; lean_object* v___y_2559_; uint8_t v___x_2578_; 
v___x_2578_ = lean_nat_dec_lt(v_a_2546_, v_upperBound_2539_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_b_2547_);
return v___x_2579_;
}
else
{
lean_object* v___x_2580_; 
v___x_2580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2537_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = lean_box(0);
v___x_2583_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2538_, v_a_2546_, v_a_2581_);
lean_dec(v_a_2581_);
if (v___x_2583_ == 0)
{
v_a_2554_ = v___x_2582_;
goto v___jp_2553_;
}
else
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = lean_array_get_size(v_args_2540_);
v___x_2585_ = lean_nat_dec_lt(v_a_2546_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v_toCold_2586_; lean_object* v_options_2587_; lean_object* v_inheritedTraceOptions_2588_; uint8_t v_hasTrace_2589_; 
v_toCold_2586_ = lean_ctor_get(v___y_2550_, 0);
v_options_2587_ = lean_ctor_get(v_toCold_2586_, 2);
v_inheritedTraceOptions_2588_ = lean_ctor_get(v_toCold_2586_, 11);
v_hasTrace_2589_ = lean_ctor_get_uint8(v_options_2587_, sizeof(void*)*1);
if (v_hasTrace_2589_ == 0)
{
goto v___jp_2590_;
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2593_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2588_, v_options_2587_, v___x_2593_);
if (v___x_2594_ == 0)
{
goto v___jp_2590_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2595_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2538_);
v___x_2596_ = l_Nat_reprFast(v_val_2538_);
v___x_2597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
v___x_2598_ = l_Lean_MessageData_ofFormat(v___x_2597_);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2595_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2599_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
lean_inc(v_a_2546_);
v___x_2602_ = l_Nat_reprFast(v_a_2546_);
v___x_2603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
v___x_2604_ = l_Lean_MessageData_ofFormat(v___x_2603_);
lean_inc_ref(v___x_2604_);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2601_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_inc_ref(v_e_2541_);
v___x_2608_ = l_Lean_MessageData_ofExpr(v_e_2541_);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2604_);
v___x_2613_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2592_, v___x_2612_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2615_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
lean_inc(v_a_2546_);
v___x_2615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2537_, v_val_2538_, v_a_2546_, v___x_2582_, v_a_2614_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
v___y_2559_ = v___x_2615_;
goto v___jp_2558_;
}
else
{
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
return v___x_2613_;
}
}
}
v___jp_2590_:
{
lean_object* v___x_2591_; 
lean_inc(v_a_2546_);
v___x_2591_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2537_, v_val_2538_, v_a_2546_, v___x_2582_, v___x_2582_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
v___y_2559_ = v___x_2591_;
goto v___jp_2558_;
}
}
else
{
lean_object* v___x_2616_; 
v___x_2616_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2537_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = lean_array_fget_borrowed(v_args_2540_, v_a_2546_);
v___x_2619_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2538_, v_a_2546_, v_next_2542_, v_a_2617_);
lean_dec(v_a_2617_);
if (lean_obj_tag(v___x_2619_) == 1)
{
lean_object* v_val_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2724_; 
v_val_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2724_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_val_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2724_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; uint8_t v_foApprox_2625_; uint8_t v_ctxApprox_2626_; uint8_t v_quasiPatternApprox_2627_; uint8_t v_constApprox_2628_; uint8_t v_isDefEqStuckEx_2629_; uint8_t v_unificationHints_2630_; uint8_t v_assignSyntheticOpaque_2631_; uint8_t v_offsetCnstrs_2632_; uint8_t v_transparency_2633_; uint8_t v_etaStruct_2634_; uint8_t v_univApprox_2635_; uint8_t v_iota_2636_; uint8_t v_beta_2637_; uint8_t v_proj_2638_; uint8_t v_zeta_2639_; uint8_t v_zetaDelta_2640_; uint8_t v_zetaUnused_2641_; uint8_t v_zetaHave_2642_; uint8_t v_canUnfoldPredicateConfig_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2723_; 
v___x_2624_ = l_Lean_Meta_Context_config(v___y_2548_);
v_foApprox_2625_ = lean_ctor_get_uint8(v___x_2624_, 0);
v_ctxApprox_2626_ = lean_ctor_get_uint8(v___x_2624_, 1);
v_quasiPatternApprox_2627_ = lean_ctor_get_uint8(v___x_2624_, 2);
v_constApprox_2628_ = lean_ctor_get_uint8(v___x_2624_, 3);
v_isDefEqStuckEx_2629_ = lean_ctor_get_uint8(v___x_2624_, 4);
v_unificationHints_2630_ = lean_ctor_get_uint8(v___x_2624_, 5);
v_assignSyntheticOpaque_2631_ = lean_ctor_get_uint8(v___x_2624_, 7);
v_offsetCnstrs_2632_ = lean_ctor_get_uint8(v___x_2624_, 8);
v_transparency_2633_ = lean_ctor_get_uint8(v___x_2624_, 9);
v_etaStruct_2634_ = lean_ctor_get_uint8(v___x_2624_, 10);
v_univApprox_2635_ = lean_ctor_get_uint8(v___x_2624_, 11);
v_iota_2636_ = lean_ctor_get_uint8(v___x_2624_, 12);
v_beta_2637_ = lean_ctor_get_uint8(v___x_2624_, 13);
v_proj_2638_ = lean_ctor_get_uint8(v___x_2624_, 14);
v_zeta_2639_ = lean_ctor_get_uint8(v___x_2624_, 15);
v_zetaDelta_2640_ = lean_ctor_get_uint8(v___x_2624_, 16);
v_zetaUnused_2641_ = lean_ctor_get_uint8(v___x_2624_, 17);
v_zetaHave_2642_ = lean_ctor_get_uint8(v___x_2624_, 18);
v_canUnfoldPredicateConfig_2643_ = lean_ctor_get_uint8(v___x_2624_, 19);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2645_ = v___x_2624_;
v_isShared_2646_ = v_isSharedCheck_2723_;
goto v_resetjp_2644_;
}
else
{
lean_dec(v___x_2624_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2723_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
uint8_t v_trackZetaDelta_2647_; lean_object* v_zetaDeltaSet_2648_; lean_object* v_lctx_2649_; lean_object* v_localInstances_2650_; lean_object* v_defEqCtx_x3f_2651_; lean_object* v_synthPendingDepth_2652_; lean_object* v_customCanUnfoldPredicate_x3f_2653_; uint8_t v_univApprox_2654_; uint8_t v_inTypeClassResolution_2655_; uint8_t v_cacheInferType_2656_; uint8_t v___x_2657_; lean_object* v___x_2659_; 
v_trackZetaDelta_2647_ = lean_ctor_get_uint8(v___y_2548_, sizeof(void*)*7);
v_zetaDeltaSet_2648_ = lean_ctor_get(v___y_2548_, 1);
v_lctx_2649_ = lean_ctor_get(v___y_2548_, 2);
v_localInstances_2650_ = lean_ctor_get(v___y_2548_, 3);
v_defEqCtx_x3f_2651_ = lean_ctor_get(v___y_2548_, 4);
v_synthPendingDepth_2652_ = lean_ctor_get(v___y_2548_, 5);
v_customCanUnfoldPredicate_x3f_2653_ = lean_ctor_get(v___y_2548_, 6);
v_univApprox_2654_ = lean_ctor_get_uint8(v___y_2548_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2655_ = lean_ctor_get_uint8(v___y_2548_, sizeof(void*)*7 + 2);
v_cacheInferType_2656_ = lean_ctor_get_uint8(v___y_2548_, sizeof(void*)*7 + 3);
v___x_2657_ = 0;
if (v_isShared_2646_ == 0)
{
v___x_2659_ = v___x_2645_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 0, v_foApprox_2625_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 1, v_ctxApprox_2626_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 2, v_quasiPatternApprox_2627_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 3, v_constApprox_2628_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 4, v_isDefEqStuckEx_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 5, v_unificationHints_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 7, v_assignSyntheticOpaque_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 8, v_offsetCnstrs_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 9, v_transparency_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 10, v_etaStruct_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 11, v_univApprox_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 12, v_iota_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 13, v_beta_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 14, v_proj_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 15, v_zeta_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 16, v_zetaDelta_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 17, v_zetaUnused_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 18, v_zetaHave_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2722_, 19, v_canUnfoldPredicateConfig_2643_);
v___x_2659_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
uint64_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v_transparency_2664_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___y_2670_; uint8_t v___x_2716_; uint8_t v___x_2717_; 
lean_ctor_set_uint8(v___x_2659_, 6, v___x_2657_);
v___x_2660_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2659_);
v___x_2661_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set_uint64(v___x_2661_, sizeof(void*)*1, v___x_2660_);
lean_inc(v_customCanUnfoldPredicate_x3f_2653_);
lean_inc(v_synthPendingDepth_2652_);
lean_inc(v_defEqCtx_x3f_2651_);
lean_inc_ref(v_localInstances_2650_);
lean_inc_ref(v_lctx_2649_);
lean_inc(v_zetaDeltaSet_2648_);
lean_inc_ref(v___x_2661_);
v___x_2662_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v_zetaDeltaSet_2648_);
lean_ctor_set(v___x_2662_, 2, v_lctx_2649_);
lean_ctor_set(v___x_2662_, 3, v_localInstances_2650_);
lean_ctor_set(v___x_2662_, 4, v_defEqCtx_x3f_2651_);
lean_ctor_set(v___x_2662_, 5, v_synthPendingDepth_2652_);
lean_ctor_set(v___x_2662_, 6, v_customCanUnfoldPredicate_x3f_2653_);
lean_ctor_set_uint8(v___x_2662_, sizeof(void*)*7, v_trackZetaDelta_2647_);
lean_ctor_set_uint8(v___x_2662_, sizeof(void*)*7 + 1, v_univApprox_2654_);
lean_ctor_set_uint8(v___x_2662_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2655_);
lean_ctor_set_uint8(v___x_2662_, sizeof(void*)*7 + 3, v_cacheInferType_2656_);
v___x_2663_ = l_Lean_Meta_Context_config(v___x_2662_);
v_transparency_2664_ = lean_ctor_get_uint8(v___x_2663_, 9);
lean_dec_ref(v___x_2663_);
v___x_2667_ = l_Lean_instInhabitedExpr;
v___x_2668_ = lean_array_get_borrowed(v___x_2667_, v_params_2543_, v_val_2620_);
lean_dec(v_val_2620_);
v___x_2716_ = 2;
v___x_2717_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2664_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec_ref_known(v___x_2662_, 7);
v___x_2718_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2716_, v___x_2661_);
lean_inc(v_customCanUnfoldPredicate_x3f_2653_);
lean_inc(v_synthPendingDepth_2652_);
lean_inc(v_defEqCtx_x3f_2651_);
lean_inc_ref(v_localInstances_2650_);
lean_inc_ref(v_lctx_2649_);
lean_inc(v_zetaDeltaSet_2648_);
v___x_2719_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_zetaDeltaSet_2648_);
lean_ctor_set(v___x_2719_, 2, v_lctx_2649_);
lean_ctor_set(v___x_2719_, 3, v_localInstances_2650_);
lean_ctor_set(v___x_2719_, 4, v_defEqCtx_x3f_2651_);
lean_ctor_set(v___x_2719_, 5, v_synthPendingDepth_2652_);
lean_ctor_set(v___x_2719_, 6, v_customCanUnfoldPredicate_x3f_2653_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7, v_trackZetaDelta_2647_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 1, v_univApprox_2654_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2655_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*7 + 3, v_cacheInferType_2656_);
lean_inc(v___x_2618_);
lean_inc(v___x_2668_);
v___x_2720_ = l_Lean_Meta_isExprDefEq(v___x_2668_, v___x_2618_, v___x_2719_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec_ref_known(v___x_2719_, 7);
v___y_2670_ = v___x_2720_;
goto v___jp_2669_;
}
else
{
lean_object* v___x_2721_; 
lean_dec_ref_known(v___x_2661_, 1);
lean_inc(v___x_2618_);
lean_inc(v___x_2668_);
v___x_2721_ = l_Lean_Meta_isExprDefEq(v___x_2668_, v___x_2618_, v___x_2662_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec_ref_known(v___x_2662_, 7);
v___y_2670_ = v___x_2721_;
goto v___jp_2669_;
}
v___jp_2665_:
{
lean_object* v___x_2666_; 
lean_inc(v_a_2546_);
v___x_2666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2537_, v_val_2538_, v_a_2546_, v___x_2582_, v___x_2582_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
v___y_2559_ = v___x_2666_;
goto v___jp_2558_;
}
v___jp_2669_:
{
if (lean_obj_tag(v___y_2670_) == 0)
{
lean_object* v_a_2671_; uint8_t v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___y_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___y_2670_, 1);
v___x_2672_ = lean_unbox(v_a_2671_);
lean_dec(v_a_2671_);
if (v___x_2672_ == 0)
{
lean_object* v_toCold_2673_; lean_object* v_options_2674_; uint8_t v_hasTrace_2675_; 
v_toCold_2673_ = lean_ctor_get(v___y_2550_, 0);
v_options_2674_ = lean_ctor_get(v_toCold_2673_, 2);
v_hasTrace_2675_ = lean_ctor_get_uint8(v_options_2674_, sizeof(void*)*1);
if (v_hasTrace_2675_ == 0)
{
lean_del_object(v___x_2622_);
goto v___jp_2665_;
}
else
{
lean_object* v_inheritedTraceOptions_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_inheritedTraceOptions_2676_ = lean_ctor_get(v_toCold_2673_, 11);
v___x_2677_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2678_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2679_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2676_, v_options_2674_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_del_object(v___x_2622_);
goto v___jp_2665_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2680_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2538_);
v___x_2681_ = l_Nat_reprFast(v_val_2538_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 3);
lean_ctor_set(v___x_2622_, 0, v___x_2681_);
v___x_2683_ = v___x_2622_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2684_ = l_Lean_MessageData_ofFormat(v___x_2683_);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2680_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
lean_inc(v_a_2546_);
v___x_2688_ = l_Nat_reprFast(v_a_2546_);
v___x_2689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
v___x_2690_ = l_Lean_MessageData_ofFormat(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2687_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
lean_inc_ref(v_e_2541_);
v___x_2694_ = l_Lean_MessageData_ofExpr(v_e_2541_);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
lean_inc(v___x_2668_);
v___x_2698_ = l_Lean_MessageData_ofExpr(v___x_2668_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
lean_inc(v___x_2618_);
v___x_2702_ = l_Lean_MessageData_ofExpr(v___x_2618_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2677_, v___x_2703_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
lean_inc(v_a_2546_);
v___x_2706_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2537_, v_val_2538_, v_a_2546_, v___x_2582_, v_a_2705_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
v___y_2559_ = v___x_2706_;
goto v___jp_2558_;
}
else
{
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
return v___x_2704_;
}
}
}
}
}
else
{
lean_del_object(v___x_2622_);
v_a_2554_ = v___x_2582_;
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_del_object(v___x_2622_);
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
v_a_2708_ = lean_ctor_get(v___y_2670_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___y_2670_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___y_2670_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___y_2670_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
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
lean_object* v___x_2725_; uint8_t v___x_2726_; lean_object* v___x_2727_; 
lean_dec(v___x_2619_);
v___x_2725_ = lean_unsigned_to_nat(0u);
v___x_2726_ = 0;
lean_inc(v___x_2618_);
lean_inc(v_a_2546_);
v___x_2727_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2537_, v_val_2538_, v_a_2546_, v_next_2542_, v___x_2544_, v___x_2545_, v___x_2544_, v_params_2543_, v___x_2618_, v___x_2725_, v___x_2726_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; uint8_t v___x_2729_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2729_ = lean_unbox(v_a_2728_);
lean_dec(v_a_2728_);
if (v___x_2729_ == 0)
{
lean_object* v_toCold_2730_; lean_object* v_options_2731_; lean_object* v_inheritedTraceOptions_2732_; uint8_t v_hasTrace_2733_; 
v_toCold_2730_ = lean_ctor_get(v___y_2550_, 0);
v_options_2731_ = lean_ctor_get(v_toCold_2730_, 2);
v_inheritedTraceOptions_2732_ = lean_ctor_get(v_toCold_2730_, 11);
v_hasTrace_2733_ = lean_ctor_get_uint8(v_options_2731_, sizeof(void*)*1);
if (v_hasTrace_2733_ == 0)
{
goto v___jp_2734_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2736_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2737_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2732_, v_options_2731_, v___x_2737_);
if (v___x_2738_ == 0)
{
goto v___jp_2734_;
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2739_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2538_);
v___x_2740_ = l_Nat_reprFast(v_val_2538_);
v___x_2741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
v___x_2742_ = l_Lean_MessageData_ofFormat(v___x_2741_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2739_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
lean_inc(v_a_2546_);
v___x_2746_ = l_Nat_reprFast(v_a_2546_);
v___x_2747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
v___x_2748_ = l_Lean_MessageData_ofFormat(v___x_2747_);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2745_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
lean_inc_ref(v_e_2541_);
v___x_2752_ = l_Lean_MessageData_ofExpr(v_e_2541_);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
lean_inc(v___x_2618_);
v___x_2756_ = l_Lean_MessageData_ofExpr(v___x_2618_);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2736_, v___x_2759_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2762_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
lean_inc(v_a_2546_);
v___x_2762_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2537_, v_val_2538_, v_a_2546_, v___x_2582_, v_a_2761_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
v___y_2559_ = v___x_2762_;
goto v___jp_2558_;
}
else
{
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
return v___x_2760_;
}
}
}
v___jp_2734_:
{
lean_object* v___x_2735_; 
lean_inc(v_a_2546_);
v___x_2735_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2537_, v_val_2538_, v_a_2546_, v___x_2582_, v___x_2582_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
v___y_2559_ = v___x_2735_;
goto v___jp_2558_;
}
}
else
{
v_a_2554_ = v___x_2582_;
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
v_a_2763_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2727_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2727_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
v_a_2771_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2616_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2616_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
v_a_2779_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2580_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2580_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
v___jp_2553_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_unsigned_to_nat(1u);
v___x_2556_ = lean_nat_add(v_a_2546_, v___x_2555_);
lean_dec(v_a_2546_);
v_a_2546_ = v___x_2556_;
v_b_2547_ = v_a_2554_;
goto _start;
}
v___jp_2558_:
{
if (lean_obj_tag(v___y_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2569_; 
v_a_2560_ = lean_ctor_get(v___y_2559_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___y_2559_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2562_ = v___y_2559_;
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___y_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
if (lean_obj_tag(v_a_2560_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
v_a_2564_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v_a_2560_, 1);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v_a_2564_);
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
else
{
lean_object* v_a_2568_; 
lean_del_object(v___x_2562_);
v_a_2568_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v_a_2560_, 1);
v_a_2554_ = v_a_2568_;
goto v___jp_2553_;
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v_a_2546_);
lean_dec_ref(v_e_2541_);
lean_dec(v_val_2538_);
v_a_2570_ = lean_ctor_get(v___y_2559_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___y_2559_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___y_2559_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___y_2559_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2787_, lean_object* v_val_2788_, lean_object* v_upperBound_2789_, lean_object* v_args_2790_, lean_object* v_e_2791_, lean_object* v_next_2792_, lean_object* v_params_2793_, lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v_a_2796_, lean_object* v_b_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2787_, v_val_2788_, v_upperBound_2789_, v_args_2790_, v_e_2791_, v_next_2792_, v_params_2793_, v___x_2794_, v___x_2795_, v_a_2796_, v_b_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___x_2795_);
lean_dec(v___x_2794_);
lean_dec_ref(v_params_2793_);
lean_dec(v_next_2792_);
lean_dec_ref(v_args_2790_);
lean_dec(v_upperBound_2789_);
lean_dec(v_val_2787_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2806_, lean_object* v___x_2807_, lean_object* v_val_2808_, lean_object* v_e_2809_, lean_object* v_next_2810_, lean_object* v_params_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
if (lean_obj_tag(v_x_2814_) == 5)
{
lean_object* v_fn_2822_; lean_object* v_arg_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_fn_2822_ = lean_ctor_get(v_x_2814_, 0);
lean_inc_ref(v_fn_2822_);
v_arg_2823_ = lean_ctor_get(v_x_2814_, 1);
lean_inc_ref(v_arg_2823_);
lean_dec_ref_known(v_x_2814_, 2);
v___x_2824_ = lean_array_set(v_x_2815_, v_x_2816_, v_arg_2823_);
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = lean_nat_sub(v_x_2816_, v___x_2825_);
lean_dec(v_x_2816_);
v_x_2814_ = v_fn_2822_;
v_x_2815_ = v___x_2824_;
v_x_2816_ = v___x_2826_;
goto _start;
}
else
{
uint8_t v___x_2828_; 
lean_dec(v_x_2816_);
v___x_2828_ = l_Lean_Expr_isConst(v_x_2814_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec_ref(v_x_2815_);
lean_dec_ref(v_x_2814_);
lean_dec_ref(v_e_2809_);
v___x_2829_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2831_ = l_Lean_Expr_constName_x21(v_x_2814_);
lean_dec_ref(v_x_2814_);
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2831_, v_preDefs_2806_, v___x_2832_);
lean_dec(v___x_2831_);
if (lean_obj_tag(v___x_2833_) == 1)
{
lean_object* v_val_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_val_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_val_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = lean_box(0);
v___x_2836_ = lean_array_get_borrowed(v___x_2832_, v___x_2807_, v_val_2834_);
v___x_2837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2808_, v_val_2834_, v___x_2836_, v_x_2815_, v_e_2809_, v_next_2810_, v_params_2811_, v___x_2812_, v___x_2813_, v___x_2832_, v___x_2835_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec_ref(v_x_2815_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2845_; 
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v___x_2837_, 0);
lean_dec(v_unused_2846_);
v___x_2839_ = v___x_2837_;
v_isShared_2840_ = v_isSharedCheck_2845_;
goto v_resetjp_2838_;
}
else
{
lean_dec(v___x_2837_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2845_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2841_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2841_);
v___x_2843_ = v___x_2839_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
v_a_2847_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2837_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2837_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec(v___x_2833_);
lean_dec_ref(v_x_2815_);
lean_dec_ref(v_e_2809_);
v___x_2855_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2857_, lean_object* v___x_2858_, lean_object* v_val_2859_, lean_object* v_e_2860_, lean_object* v_next_2861_, lean_object* v_params_2862_, lean_object* v___x_2863_, lean_object* v___x_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_, lean_object* v_x_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2857_, v___x_2858_, v_val_2859_, v_e_2860_, v_next_2861_, v_params_2862_, v___x_2863_, v___x_2864_, v_x_2865_, v_x_2866_, v_x_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___x_2864_);
lean_dec(v___x_2863_);
lean_dec_ref(v_params_2862_);
lean_dec(v_next_2861_);
lean_dec(v_val_2859_);
lean_dec_ref(v___x_2858_);
lean_dec_ref(v_preDefs_2857_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2874_, lean_object* v___x_2875_, lean_object* v_val_2876_, lean_object* v_a_2877_, lean_object* v_params_2878_, lean_object* v___x_2879_, lean_object* v___x_2880_, lean_object* v_e_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_dummy_2887_; lean_object* v_nargs_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_dummy_2887_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2888_ = l_Lean_Expr_getAppNumArgs(v_e_2881_);
lean_inc(v_nargs_2888_);
v___x_2889_ = lean_mk_array(v_nargs_2888_, v_dummy_2887_);
v___x_2890_ = lean_unsigned_to_nat(1u);
v___x_2891_ = lean_nat_sub(v_nargs_2888_, v___x_2890_);
lean_dec(v_nargs_2888_);
lean_inc_ref(v_e_2881_);
v___x_2892_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2874_, v___x_2875_, v_val_2876_, v_e_2881_, v_a_2877_, v_params_2878_, v___x_2879_, v___x_2880_, v_e_2881_, v___x_2889_, v___x_2891_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2893_, lean_object* v___x_2894_, lean_object* v_val_2895_, lean_object* v_a_2896_, lean_object* v_params_2897_, lean_object* v___x_2898_, lean_object* v___x_2899_, lean_object* v_e_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2893_, v___x_2894_, v_val_2895_, v_a_2896_, v_params_2897_, v___x_2898_, v___x_2899_, v_e_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec(v___x_2899_);
lean_dec(v___x_2898_);
lean_dec_ref(v_params_2897_);
lean_dec(v_a_2896_);
lean_dec(v_val_2895_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v_preDefs_2893_);
return v_res_2906_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2910_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2911_ = lean_unsigned_to_nat(6u);
v___x_2912_ = lean_unsigned_to_nat(201u);
v___x_2913_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2914_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2915_ = l_mkPanicMessageWithDecl(v___x_2914_, v___x_2913_, v___x_2912_, v___x_2911_, v___x_2910_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2916_, lean_object* v___x_2917_, lean_object* v_a_2918_, lean_object* v_preDefs_2919_, lean_object* v_val_2920_, lean_object* v___f_2921_, lean_object* v___x_2922_, lean_object* v_params_2923_, lean_object* v_body_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2930_ = lean_array_get_size(v_params_2923_);
v___x_2931_ = lean_array_get(v___x_2916_, v___x_2917_, v_a_2918_);
v___x_2932_ = lean_nat_dec_eq(v___x_2930_, v___x_2931_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v___x_2931_);
lean_dec_ref(v_body_2924_);
lean_dec_ref(v_params_2923_);
lean_dec_ref(v___f_2921_);
lean_dec(v_val_2920_);
lean_dec_ref(v_preDefs_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2917_);
v___x_2933_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2934_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2933_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
return v___x_2934_;
}
else
{
lean_object* v___f_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; 
v___f_2935_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2935_, 0, v_preDefs_2919_);
lean_closure_set(v___f_2935_, 1, v___x_2917_);
lean_closure_set(v___f_2935_, 2, v_val_2920_);
lean_closure_set(v___f_2935_, 3, v_a_2918_);
lean_closure_set(v___f_2935_, 4, v_params_2923_);
lean_closure_set(v___f_2935_, 5, v___x_2930_);
lean_closure_set(v___f_2935_, 6, v___x_2931_);
v___x_2936_ = 0;
v___x_2937_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2924_, v___f_2935_, v___f_2921_, v___x_2936_, v___x_2932_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v___x_2937_, 0);
lean_dec(v_unused_2945_);
v___x_2939_ = v___x_2937_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_dec(v___x_2937_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2922_);
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2922_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
v_a_2946_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2937_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2937_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2954_, lean_object* v___x_2955_, lean_object* v_a_2956_, lean_object* v_preDefs_2957_, lean_object* v_val_2958_, lean_object* v___f_2959_, lean_object* v___x_2960_, lean_object* v_params_2961_, lean_object* v_body_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2954_, v___x_2955_, v_a_2956_, v_preDefs_2957_, v_val_2958_, v___f_2959_, v___x_2960_, v_params_2961_, v_body_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___x_2954_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_e_2969_);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v___x_2985_, lean_object* v_preDefs_2986_, lean_object* v_val_2987_, lean_object* v_upperBound_2988_, lean_object* v_a_2989_, lean_object* v_b_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = lean_nat_dec_lt(v_a_2989_, v_upperBound_2988_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; 
lean_dec(v_a_2989_);
lean_dec(v_val_2987_);
lean_dec_ref(v_preDefs_2986_);
lean_dec_ref(v___x_2985_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_b_2990_);
return v___x_2997_;
}
else
{
lean_object* v___x_2998_; lean_object* v_value_2999_; lean_object* v___f_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___f_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; 
v___x_2998_ = lean_array_fget_borrowed(v_preDefs_2986_, v_a_2989_);
v_value_2999_ = lean_ctor_get(v___x_2998_, 7);
v___f_3000_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = lean_box(0);
lean_inc(v_val_2987_);
lean_inc_ref(v_preDefs_2986_);
lean_inc(v_a_2989_);
lean_inc_ref(v___x_2985_);
v___f_3003_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3003_, 0, v___x_3001_);
lean_closure_set(v___f_3003_, 1, v___x_2985_);
lean_closure_set(v___f_3003_, 2, v_a_2989_);
lean_closure_set(v___f_3003_, 3, v_preDefs_2986_);
lean_closure_set(v___f_3003_, 4, v_val_2987_);
lean_closure_set(v___f_3003_, 5, v___f_3000_);
lean_closure_set(v___f_3003_, 6, v___x_3002_);
v___x_3004_ = 0;
lean_inc_ref(v_value_2999_);
v___x_3005_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_2999_, v___f_3003_, v___x_3004_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec_ref_known(v___x_3005_, 1);
v___x_3006_ = lean_unsigned_to_nat(1u);
v___x_3007_ = lean_nat_add(v_a_2989_, v___x_3006_);
lean_dec(v_a_2989_);
v_a_2989_ = v___x_3007_;
v_b_2990_ = v___x_3002_;
goto _start;
}
else
{
lean_dec(v_a_2989_);
lean_dec(v_val_2987_);
lean_dec_ref(v_preDefs_2986_);
lean_dec_ref(v___x_2985_);
return v___x_3005_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v___x_3009_, lean_object* v_preDefs_3010_, lean_object* v_val_3011_, lean_object* v_upperBound_3012_, lean_object* v_a_3013_, lean_object* v_b_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3009_, v_preDefs_3010_, v_val_3011_, v_upperBound_3012_, v_a_3013_, v_b_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v_upperBound_3012_);
return v_res_3020_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3023_ = l_Lean_stringToMessageData(v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
size_t v_sz_3030_; size_t v___x_3031_; lean_object* v___x_3032_; 
v_sz_3030_ = lean_array_size(v_preDefs_3024_);
v___x_3031_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3024_);
v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3030_, v___x_3031_, v_preDefs_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; size_t v_sz_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc_n(v_a_3033_, 2);
lean_dec_ref_known(v___x_3032_, 1);
v_sz_3034_ = lean_array_size(v_a_3033_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3034_, v___x_3031_, v_a_3033_);
v___x_3036_ = l_Lean_Elab_FixedParams_Info_init(v_a_3033_);
v___x_3037_ = lean_st_mk_ref(v___x_3036_);
v___x_3038_ = lean_st_ref_take(v___x_3037_);
v___x_3039_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3038_);
v___x_3040_ = lean_st_ref_put(v___x_3037_, v___x_3039_);
v___x_3041_ = lean_array_get_size(v_preDefs_3024_);
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = lean_box(0);
lean_inc(v___x_3037_);
v___x_3044_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3035_, v_preDefs_3024_, v___x_3037_, v___x_3041_, v___x_3042_, v___x_3043_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3084_; 
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; 
v_unused_3085_ = lean_ctor_get(v___x_3044_, 0);
lean_dec(v_unused_3085_);
v___x_3046_ = v___x_3044_;
v_isShared_3047_ = v_isSharedCheck_3084_;
goto v_resetjp_3045_;
}
else
{
lean_dec(v___x_3044_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3084_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v_toCold_3049_; lean_object* v_options_3050_; uint8_t v_hasTrace_3051_; 
v___x_3048_ = lean_st_ref_get(v___x_3037_);
lean_dec(v___x_3037_);
v_toCold_3049_ = lean_ctor_get(v_a_3027_, 0);
v_options_3050_ = lean_ctor_get(v_toCold_3049_, 2);
v_hasTrace_3051_ = lean_ctor_get_uint8(v_options_3050_, sizeof(void*)*1);
if (v_hasTrace_3051_ == 0)
{
lean_object* v___x_3053_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3053_ = v___x_3046_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v_inheritedTraceOptions_3055_ = lean_ctor_get(v_toCold_3049_, 11);
v___x_3056_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3057_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3058_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3055_, v_options_3050_, v___x_3057_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3060_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3060_ = v___x_3046_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3048_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_del_object(v___x_3046_);
v___x_3062_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3048_);
v___x_3063_ = l_Lean_Elab_FixedParams_Info_format(v___x_3048_);
v___x_3064_ = l_Std_Format_indentD(v___x_3063_);
v___x_3065_ = l_Lean_MessageData_ofFormat(v___x_3064_);
v___x_3066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3062_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3056_, v___x_3066_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v___x_3067_, 0);
lean_dec(v_unused_3075_);
v___x_3069_ = v___x_3067_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v___x_3067_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3048_);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3048_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v___x_3048_);
v_a_3076_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3067_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3067_);
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
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v___x_3037_);
v_a_3086_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3044_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3044_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v_preDefs_3024_);
v_a_3094_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3032_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3032_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
lean_dec(v_a_3106_);
lean_dec_ref(v_a_3105_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3109_, lean_object* v_val_3110_, lean_object* v_next_3111_, lean_object* v_next_3112_, lean_object* v___x_3113_, lean_object* v___x_3114_, lean_object* v_upperBound_3115_, lean_object* v_params_3116_, lean_object* v___x_3117_, lean_object* v_inst_3118_, lean_object* v_R_3119_, lean_object* v_a_3120_, uint8_t v_b_3121_, lean_object* v_c_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3109_, v_val_3110_, v_next_3111_, v_next_3112_, v___x_3113_, v___x_3114_, v_upperBound_3115_, v_params_3116_, v___x_3117_, v_a_3120_, v_b_3121_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3129_ = _args[0];
lean_object* v_val_3130_ = _args[1];
lean_object* v_next_3131_ = _args[2];
lean_object* v_next_3132_ = _args[3];
lean_object* v___x_3133_ = _args[4];
lean_object* v___x_3134_ = _args[5];
lean_object* v_upperBound_3135_ = _args[6];
lean_object* v_params_3136_ = _args[7];
lean_object* v___x_3137_ = _args[8];
lean_object* v_inst_3138_ = _args[9];
lean_object* v_R_3139_ = _args[10];
lean_object* v_a_3140_ = _args[11];
lean_object* v_b_3141_ = _args[12];
lean_object* v_c_3142_ = _args[13];
lean_object* v___y_3143_ = _args[14];
lean_object* v___y_3144_ = _args[15];
lean_object* v___y_3145_ = _args[16];
lean_object* v___y_3146_ = _args[17];
lean_object* v___y_3147_ = _args[18];
_start:
{
uint8_t v_b_boxed_3148_; lean_object* v_res_3149_; 
v_b_boxed_3148_ = lean_unbox(v_b_3141_);
v_res_3149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3129_, v_val_3130_, v_next_3131_, v_next_3132_, v___x_3133_, v___x_3134_, v_upperBound_3135_, v_params_3136_, v___x_3137_, v_inst_3138_, v_R_3139_, v_a_3140_, v_b_boxed_3148_, v_c_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_params_3136_);
lean_dec(v_upperBound_3135_);
lean_dec(v___x_3134_);
lean_dec(v___x_3133_);
lean_dec(v_next_3132_);
lean_dec(v_val_3130_);
lean_dec(v_val_3129_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3150_, lean_object* v_val_3151_, lean_object* v_upperBound_3152_, lean_object* v_args_3153_, lean_object* v_e_3154_, lean_object* v_next_3155_, lean_object* v_params_3156_, lean_object* v___x_3157_, lean_object* v___x_3158_, lean_object* v_inst_3159_, lean_object* v_R_3160_, lean_object* v_a_3161_, lean_object* v_b_3162_, lean_object* v_c_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3150_, v_val_3151_, v_upperBound_3152_, v_args_3153_, v_e_3154_, v_next_3155_, v_params_3156_, v___x_3157_, v___x_3158_, v_a_3161_, v_b_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3170_ = _args[0];
lean_object* v_val_3171_ = _args[1];
lean_object* v_upperBound_3172_ = _args[2];
lean_object* v_args_3173_ = _args[3];
lean_object* v_e_3174_ = _args[4];
lean_object* v_next_3175_ = _args[5];
lean_object* v_params_3176_ = _args[6];
lean_object* v___x_3177_ = _args[7];
lean_object* v___x_3178_ = _args[8];
lean_object* v_inst_3179_ = _args[9];
lean_object* v_R_3180_ = _args[10];
lean_object* v_a_3181_ = _args[11];
lean_object* v_b_3182_ = _args[12];
lean_object* v_c_3183_ = _args[13];
lean_object* v___y_3184_ = _args[14];
lean_object* v___y_3185_ = _args[15];
lean_object* v___y_3186_ = _args[16];
lean_object* v___y_3187_ = _args[17];
lean_object* v___y_3188_ = _args[18];
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3170_, v_val_3171_, v_upperBound_3172_, v_args_3173_, v_e_3174_, v_next_3175_, v_params_3176_, v___x_3177_, v___x_3178_, v_inst_3179_, v_R_3180_, v_a_3181_, v_b_3182_, v_c_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___x_3178_);
lean_dec(v___x_3177_);
lean_dec_ref(v_params_3176_);
lean_dec(v_next_3175_);
lean_dec_ref(v_args_3173_);
lean_dec(v_upperBound_3172_);
lean_dec(v_val_3170_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v___x_3190_, lean_object* v_preDefs_3191_, lean_object* v_val_3192_, lean_object* v_upperBound_3193_, lean_object* v_inst_3194_, lean_object* v_R_3195_, lean_object* v_a_3196_, lean_object* v_b_3197_, lean_object* v_c_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3190_, v_preDefs_3191_, v_val_3192_, v_upperBound_3193_, v_a_3196_, v_b_3197_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v___x_3205_, lean_object* v_preDefs_3206_, lean_object* v_val_3207_, lean_object* v_upperBound_3208_, lean_object* v_inst_3209_, lean_object* v_R_3210_, lean_object* v_a_3211_, lean_object* v_b_3212_, lean_object* v_c_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3205_, v_preDefs_3206_, v_val_3207_, v_upperBound_3208_, v_inst_3209_, v_R_3210_, v_a_3211_, v_b_3212_, v_c_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v_upperBound_3208_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3220_, lean_object* v___x_3221_, lean_object* v_pre_3222_, lean_object* v_post_3223_, uint8_t v_usedLetOnly_3224_, uint8_t v_skipConstInApp_3225_, uint8_t v_skipInstances_3226_, lean_object* v___x_3227_, lean_object* v_inst_3228_, lean_object* v_R_3229_, lean_object* v_a_3230_, lean_object* v_b_3231_, lean_object* v_c_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3220_, v___x_3221_, v_pre_3222_, v_post_3223_, v_usedLetOnly_3224_, v_skipConstInApp_3225_, v_skipInstances_3226_, v_a_3230_, v_b_3231_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3240_ = _args[0];
lean_object* v___x_3241_ = _args[1];
lean_object* v_pre_3242_ = _args[2];
lean_object* v_post_3243_ = _args[3];
lean_object* v_usedLetOnly_3244_ = _args[4];
lean_object* v_skipConstInApp_3245_ = _args[5];
lean_object* v_skipInstances_3246_ = _args[6];
lean_object* v___x_3247_ = _args[7];
lean_object* v_inst_3248_ = _args[8];
lean_object* v_R_3249_ = _args[9];
lean_object* v_a_3250_ = _args[10];
lean_object* v_b_3251_ = _args[11];
lean_object* v_c_3252_ = _args[12];
lean_object* v___y_3253_ = _args[13];
lean_object* v___y_3254_ = _args[14];
lean_object* v___y_3255_ = _args[15];
lean_object* v___y_3256_ = _args[16];
lean_object* v___y_3257_ = _args[17];
lean_object* v___y_3258_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3259_; uint8_t v_skipConstInApp_boxed_3260_; uint8_t v_skipInstances_boxed_3261_; lean_object* v_res_3262_; 
v_usedLetOnly_boxed_3259_ = lean_unbox(v_usedLetOnly_3244_);
v_skipConstInApp_boxed_3260_ = lean_unbox(v_skipConstInApp_3245_);
v_skipInstances_boxed_3261_ = lean_unbox(v_skipInstances_3246_);
v_res_3262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3240_, v___x_3241_, v_pre_3242_, v_post_3243_, v_usedLetOnly_boxed_3259_, v_skipConstInApp_boxed_3260_, v_skipInstances_boxed_3261_, v___x_3247_, v_inst_3248_, v_R_3249_, v_a_3250_, v_b_3251_, v_c_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec(v___x_3247_);
lean_dec_ref(v___x_3241_);
lean_dec(v_upperBound_3240_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3263_, lean_object* v_m_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3264_, v_a_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3267_, lean_object* v_m_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3267_, v_m_3268_, v_a_3269_);
lean_dec_ref(v_a_3269_);
lean_dec_ref(v_m_3268_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3271_, lean_object* v_name_3272_, uint8_t v_bi_3273_, lean_object* v_type_3274_, lean_object* v_k_3275_, uint8_t v_kind_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3272_, v_bi_3273_, v_type_3274_, v_k_3275_, v_kind_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3284_, lean_object* v_name_3285_, lean_object* v_bi_3286_, lean_object* v_type_3287_, lean_object* v_k_3288_, lean_object* v_kind_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
uint8_t v_bi_boxed_3296_; uint8_t v_kind_boxed_3297_; lean_object* v_res_3298_; 
v_bi_boxed_3296_ = lean_unbox(v_bi_3286_);
v_kind_boxed_3297_ = lean_unbox(v_kind_3289_);
v_res_3298_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3284_, v_name_3285_, v_bi_boxed_3296_, v_type_3287_, v_k_3288_, v_kind_boxed_3297_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3299_, lean_object* v_name_3300_, lean_object* v_type_3301_, lean_object* v_val_3302_, lean_object* v_k_3303_, uint8_t v_nondep_3304_, uint8_t v_kind_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3300_, v_type_3301_, v_val_3302_, v_k_3303_, v_nondep_3304_, v_kind_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3313_, lean_object* v_name_3314_, lean_object* v_type_3315_, lean_object* v_val_3316_, lean_object* v_k_3317_, lean_object* v_nondep_3318_, lean_object* v_kind_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
uint8_t v_nondep_boxed_3326_; uint8_t v_kind_boxed_3327_; lean_object* v_res_3328_; 
v_nondep_boxed_3326_ = lean_unbox(v_nondep_3318_);
v_kind_boxed_3327_ = lean_unbox(v_kind_3319_);
v_res_3328_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3313_, v_name_3314_, v_type_3315_, v_val_3316_, v_k_3317_, v_nondep_boxed_3326_, v_kind_boxed_3327_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3329_, lean_object* v_ref_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3330_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3337_, lean_object* v_ref_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3337_, v_ref_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3345_, lean_object* v_x_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3354_, lean_object* v_x_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3354_, v_x_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3363_, lean_object* v_m_3364_, lean_object* v_a_3365_, lean_object* v_b_3366_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3364_, v_a_3365_, v_b_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3368_, lean_object* v_a_3369_, lean_object* v_x_3370_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3369_, v_x_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3372_, lean_object* v_a_3373_, lean_object* v_x_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3372_, v_a_3373_, v_x_3374_);
lean_dec(v_x_3374_);
lean_dec_ref(v_a_3373_);
return v_res_3375_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3376_, lean_object* v_a_3377_, lean_object* v_x_3378_){
_start:
{
uint8_t v___x_3379_; 
v___x_3379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3377_, v_x_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3380_, lean_object* v_a_3381_, lean_object* v_x_3382_){
_start:
{
uint8_t v_res_3383_; lean_object* v_r_3384_; 
v_res_3383_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3380_, v_a_3381_, v_x_3382_);
lean_dec(v_x_3382_);
lean_dec_ref(v_a_3381_);
v_r_3384_ = lean_box(v_res_3383_);
return v_r_3384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3385_, lean_object* v_data_3386_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3388_, lean_object* v_a_3389_, lean_object* v_b_3390_, lean_object* v_x_3391_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3389_, v_b_3390_, v_x_3391_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3393_, lean_object* v_i_3394_, lean_object* v_source_3395_, lean_object* v_target_3396_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3394_, v_source_3395_, v_target_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3398_, lean_object* v_x_3399_, lean_object* v_x_3400_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3399_, v_x_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3415_, lean_object* v_x_3416_){
_start:
{
if (lean_obj_tag(v_x_3415_) == 0)
{
lean_object* v___x_3417_; 
v___x_3417_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3417_;
}
else
{
lean_object* v_val_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3429_; 
v_val_3418_ = lean_ctor_get(v_x_3415_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_x_3415_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3420_ = v_x_3415_;
v_isShared_3421_ = v_isSharedCheck_3429_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_val_3418_);
lean_dec(v_x_3415_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3429_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3422_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3423_ = l_Nat_reprFast(v_val_3418_);
if (v_isShared_3421_ == 0)
{
lean_ctor_set_tag(v___x_3420_, 3);
lean_ctor_set(v___x_3420_, 0, v___x_3423_);
v___x_3425_ = v___x_3420_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3422_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Repr_addAppParen(v___x_3426_, v_x_3416_);
return v___x_3427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3430_, v_x_3431_);
lean_dec(v_x_3431_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3433_, lean_object* v_x_3434_, lean_object* v_x_3435_){
_start:
{
if (lean_obj_tag(v_x_3435_) == 0)
{
lean_dec(v_x_3433_);
return v_x_3434_;
}
else
{
lean_object* v_head_3436_; lean_object* v_tail_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3448_; 
v_head_3436_ = lean_ctor_get(v_x_3435_, 0);
v_tail_3437_ = lean_ctor_get(v_x_3435_, 1);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_x_3435_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3439_ = v_x_3435_;
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_tail_3437_);
lean_inc(v_head_3436_);
lean_dec(v_x_3435_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
lean_inc(v_x_3433_);
if (v_isShared_3440_ == 0)
{
lean_ctor_set_tag(v___x_3439_, 5);
lean_ctor_set(v___x_3439_, 1, v_x_3433_);
lean_ctor_set(v___x_3439_, 0, v_x_3434_);
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_x_3434_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_x_3433_);
v___x_3442_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3443_ = lean_unsigned_to_nat(0u);
v___x_3444_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3436_, v___x_3443_);
v___x_3445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3442_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v_x_3434_ = v___x_3445_;
v_x_3435_ = v_tail_3437_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3449_, lean_object* v_x_3450_, lean_object* v_x_3451_){
_start:
{
if (lean_obj_tag(v_x_3451_) == 0)
{
lean_dec(v_x_3449_);
return v_x_3450_;
}
else
{
lean_object* v_head_3452_; lean_object* v_tail_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3464_; 
v_head_3452_ = lean_ctor_get(v_x_3451_, 0);
v_tail_3453_ = lean_ctor_get(v_x_3451_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_x_3451_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3455_ = v_x_3451_;
v_isShared_3456_ = v_isSharedCheck_3464_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_tail_3453_);
lean_inc(v_head_3452_);
lean_dec(v_x_3451_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3464_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
lean_inc(v_x_3449_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 5);
lean_ctor_set(v___x_3455_, 1, v_x_3449_);
lean_ctor_set(v___x_3455_, 0, v_x_3450_);
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_x_3450_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_x_3449_);
v___x_3458_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3459_ = lean_unsigned_to_nat(0u);
v___x_3460_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3452_, v___x_3459_);
v___x_3461_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3458_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3449_, v___x_3461_, v_tail_3453_);
return v___x_3462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3465_){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3465_, v___x_3466_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3468_, lean_object* v_x_3469_){
_start:
{
if (lean_obj_tag(v_x_3468_) == 0)
{
lean_object* v___x_3470_; 
lean_dec(v_x_3469_);
v___x_3470_ = lean_box(0);
return v___x_3470_;
}
else
{
lean_object* v_tail_3471_; 
v_tail_3471_ = lean_ctor_get(v_x_3468_, 1);
if (lean_obj_tag(v_tail_3471_) == 0)
{
lean_object* v_head_3472_; lean_object* v___x_3473_; 
lean_dec(v_x_3469_);
v_head_3472_ = lean_ctor_get(v_x_3468_, 0);
lean_inc(v_head_3472_);
lean_dec_ref_known(v_x_3468_, 2);
v___x_3473_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3472_);
return v___x_3473_;
}
else
{
lean_object* v_head_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
lean_inc(v_tail_3471_);
v_head_3474_ = lean_ctor_get(v_x_3468_, 0);
lean_inc(v_head_3474_);
lean_dec_ref_known(v_x_3468_, 2);
v___x_3475_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3474_);
v___x_3476_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3469_, v___x_3475_, v_tail_3471_);
return v___x_3476_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3485_ = lean_string_length(v___x_3484_);
return v___x_3485_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3487_ = lean_nat_to_int(v___x_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3493_){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; uint8_t v___x_3496_; 
v___x_3494_ = lean_array_get_size(v_xs_3493_);
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3496_ = lean_nat_dec_eq(v___x_3494_, v___x_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3497_ = lean_array_to_list(v_xs_3493_);
v___x_3498_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3499_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3497_, v___x_3498_);
v___x_3500_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3501_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___x_3499_);
v___x_3503_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3502_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3500_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = l_Std_Format_fill(v___x_3505_);
return v___x_3506_;
}
else
{
lean_object* v___x_3507_; 
lean_dec_ref(v_xs_3493_);
v___x_3507_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3507_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3508_, lean_object* v_x_3509_, lean_object* v_x_3510_){
_start:
{
if (lean_obj_tag(v_x_3510_) == 0)
{
lean_dec(v_x_3508_);
return v_x_3509_;
}
else
{
lean_object* v_head_3511_; lean_object* v_tail_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3522_; 
v_head_3511_ = lean_ctor_get(v_x_3510_, 0);
v_tail_3512_ = lean_ctor_get(v_x_3510_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_x_3510_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3514_ = v_x_3510_;
v_isShared_3515_ = v_isSharedCheck_3522_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_tail_3512_);
lean_inc(v_head_3511_);
lean_dec(v_x_3510_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3522_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
lean_inc(v_x_3508_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set_tag(v___x_3514_, 5);
lean_ctor_set(v___x_3514_, 1, v_x_3508_);
lean_ctor_set(v___x_3514_, 0, v_x_3509_);
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_x_3509_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_x_3508_);
v___x_3517_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3511_);
v___x_3519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v_x_3509_ = v___x_3519_;
v_x_3510_ = v_tail_3512_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3523_, lean_object* v_x_3524_){
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
lean_dec_ref_known(v_x_3523_, 2);
v___x_3528_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3527_);
return v___x_3528_;
}
else
{
lean_object* v_head_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_inc(v_tail_3526_);
v_head_3529_ = lean_ctor_get(v_x_3523_, 0);
lean_inc(v_head_3529_);
lean_dec_ref_known(v_x_3523_, 2);
v___x_3530_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3529_);
v___x_3531_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3524_, v___x_3530_, v_tail_3526_);
return v___x_3531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3532_){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v___x_3533_ = lean_array_get_size(v_xs_3532_);
v___x_3534_ = lean_unsigned_to_nat(0u);
v___x_3535_ = lean_nat_dec_eq(v___x_3533_, v___x_3534_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3536_ = lean_array_to_list(v_xs_3532_);
v___x_3537_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3538_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3536_, v___x_3537_);
v___x_3539_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3540_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v___x_3538_);
v___x_3542_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3541_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3539_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = l_Std_Format_fill(v___x_3544_);
return v___x_3545_;
}
else
{
lean_object* v___x_3546_; 
lean_dec_ref(v_xs_3532_);
v___x_3546_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3546_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3547_, lean_object* v_x_3548_, lean_object* v_x_3549_){
_start:
{
if (lean_obj_tag(v_x_3549_) == 0)
{
lean_dec(v_x_3547_);
return v_x_3548_;
}
else
{
lean_object* v_head_3550_; lean_object* v_tail_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3562_; 
v_head_3550_ = lean_ctor_get(v_x_3549_, 0);
v_tail_3551_ = lean_ctor_get(v_x_3549_, 1);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_x_3549_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3553_ = v_x_3549_;
v_isShared_3554_ = v_isSharedCheck_3562_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_tail_3551_);
lean_inc(v_head_3550_);
lean_dec(v_x_3549_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3562_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
lean_inc(v_x_3547_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set_tag(v___x_3553_, 5);
lean_ctor_set(v___x_3553_, 1, v_x_3547_);
lean_ctor_set(v___x_3553_, 0, v_x_3548_);
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_x_3548_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_x_3547_);
v___x_3556_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = l_Nat_reprFast(v_head_3550_);
v___x_3558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
v___x_3559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3556_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v_x_3548_ = v___x_3559_;
v_x_3549_ = v_tail_3551_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v_x_3565_){
_start:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_dec(v_x_3563_);
return v_x_3564_;
}
else
{
lean_object* v_head_3566_; lean_object* v_tail_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3578_; 
v_head_3566_ = lean_ctor_get(v_x_3565_, 0);
v_tail_3567_ = lean_ctor_get(v_x_3565_, 1);
v_isSharedCheck_3578_ = !lean_is_exclusive(v_x_3565_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3569_ = v_x_3565_;
v_isShared_3570_ = v_isSharedCheck_3578_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_tail_3567_);
lean_inc(v_head_3566_);
lean_dec(v_x_3565_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3578_;
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
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_x_3564_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_x_3563_);
v___x_3572_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3573_ = l_Nat_reprFast(v_head_3566_);
v___x_3574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
v___x_3575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3572_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3563_, v___x_3575_, v_tail_3567_);
return v___x_3576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = l_Nat_reprFast(v___y_3579_);
v___x_3581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3582_, lean_object* v_x_3583_){
_start:
{
if (lean_obj_tag(v_x_3582_) == 0)
{
lean_object* v___x_3584_; 
lean_dec(v_x_3583_);
v___x_3584_ = lean_box(0);
return v___x_3584_;
}
else
{
lean_object* v_tail_3585_; 
v_tail_3585_ = lean_ctor_get(v_x_3582_, 1);
if (lean_obj_tag(v_tail_3585_) == 0)
{
lean_object* v_head_3586_; lean_object* v___x_3587_; 
lean_dec(v_x_3583_);
v_head_3586_ = lean_ctor_get(v_x_3582_, 0);
lean_inc(v_head_3586_);
lean_dec_ref_known(v_x_3582_, 2);
v___x_3587_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3586_);
return v___x_3587_;
}
else
{
lean_object* v_head_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_inc(v_tail_3585_);
v_head_3588_ = lean_ctor_get(v_x_3582_, 0);
lean_inc(v_head_3588_);
lean_dec_ref_known(v_x_3582_, 2);
v___x_3589_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3588_);
v___x_3590_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3583_, v___x_3589_, v_tail_3585_);
return v___x_3590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3591_){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3592_ = lean_array_get_size(v_xs_3591_);
v___x_3593_ = lean_unsigned_to_nat(0u);
v___x_3594_ = lean_nat_dec_eq(v___x_3592_, v___x_3593_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3595_ = lean_array_to_list(v_xs_3591_);
v___x_3596_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3597_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3595_, v___x_3596_);
v___x_3598_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3599_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___x_3597_);
v___x_3601_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3598_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = l_Std_Format_fill(v___x_3603_);
return v___x_3604_;
}
else
{
lean_object* v___x_3605_; 
lean_dec_ref(v_xs_3591_);
v___x_3605_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3605_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3606_, lean_object* v_x_3607_, lean_object* v_x_3608_){
_start:
{
if (lean_obj_tag(v_x_3608_) == 0)
{
lean_dec(v_x_3606_);
return v_x_3607_;
}
else
{
lean_object* v_head_3609_; lean_object* v_tail_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3620_; 
v_head_3609_ = lean_ctor_get(v_x_3608_, 0);
v_tail_3610_ = lean_ctor_get(v_x_3608_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_x_3608_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3612_ = v_x_3608_;
v_isShared_3613_ = v_isSharedCheck_3620_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_tail_3610_);
lean_inc(v_head_3609_);
lean_dec(v_x_3608_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3620_;
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
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_x_3607_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_x_3606_);
v___x_3615_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3609_);
v___x_3617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3615_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v_x_3607_ = v___x_3617_;
v_x_3608_ = v_tail_3610_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3621_, lean_object* v_x_3622_){
_start:
{
if (lean_obj_tag(v_x_3621_) == 0)
{
lean_object* v___x_3623_; 
lean_dec(v_x_3622_);
v___x_3623_ = lean_box(0);
return v___x_3623_;
}
else
{
lean_object* v_tail_3624_; 
v_tail_3624_ = lean_ctor_get(v_x_3621_, 1);
if (lean_obj_tag(v_tail_3624_) == 0)
{
lean_object* v_head_3625_; lean_object* v___x_3626_; 
lean_dec(v_x_3622_);
v_head_3625_ = lean_ctor_get(v_x_3621_, 0);
lean_inc(v_head_3625_);
lean_dec_ref_known(v_x_3621_, 2);
v___x_3626_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3625_);
return v___x_3626_;
}
else
{
lean_object* v_head_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
lean_inc(v_tail_3624_);
v_head_3627_ = lean_ctor_get(v_x_3621_, 0);
lean_inc(v_head_3627_);
lean_dec_ref_known(v_x_3621_, 2);
v___x_3628_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3627_);
v___x_3629_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3622_, v___x_3628_, v_tail_3624_);
return v___x_3629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3630_){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3631_ = lean_array_get_size(v_xs_3630_);
v___x_3632_ = lean_unsigned_to_nat(0u);
v___x_3633_ = lean_nat_dec_eq(v___x_3631_, v___x_3632_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3634_ = lean_array_to_list(v_xs_3630_);
v___x_3635_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3636_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3634_, v___x_3635_);
v___x_3637_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3638_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
lean_ctor_set(v___x_3639_, 1, v___x_3636_);
v___x_3640_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3639_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
v___x_3642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3637_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = l_Std_Format_fill(v___x_3642_);
return v___x_3643_;
}
else
{
lean_object* v___x_3644_; 
lean_dec_ref(v_xs_3630_);
v___x_3644_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3644_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3645_, lean_object* v_x_3646_, lean_object* v_x_3647_){
_start:
{
if (lean_obj_tag(v_x_3647_) == 0)
{
lean_dec(v_x_3645_);
return v_x_3646_;
}
else
{
lean_object* v_head_3648_; lean_object* v_tail_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3659_; 
v_head_3648_ = lean_ctor_get(v_x_3647_, 0);
v_tail_3649_ = lean_ctor_get(v_x_3647_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_x_3647_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3651_ = v_x_3647_;
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_tail_3649_);
lean_inc(v_head_3648_);
lean_dec(v_x_3647_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3659_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
lean_inc(v_x_3645_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set_tag(v___x_3651_, 5);
lean_ctor_set(v___x_3651_, 1, v_x_3645_);
lean_ctor_set(v___x_3651_, 0, v_x_3646_);
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_x_3646_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_x_3645_);
v___x_3654_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3648_);
v___x_3656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v_x_3646_ = v___x_3656_;
v_x_3647_ = v_tail_3649_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3660_, lean_object* v_x_3661_){
_start:
{
if (lean_obj_tag(v_x_3660_) == 0)
{
lean_object* v___x_3662_; 
lean_dec(v_x_3661_);
v___x_3662_ = lean_box(0);
return v___x_3662_;
}
else
{
lean_object* v_tail_3663_; 
v_tail_3663_ = lean_ctor_get(v_x_3660_, 1);
if (lean_obj_tag(v_tail_3663_) == 0)
{
lean_object* v_head_3664_; lean_object* v___x_3665_; 
lean_dec(v_x_3661_);
v_head_3664_ = lean_ctor_get(v_x_3660_, 0);
lean_inc(v_head_3664_);
lean_dec_ref_known(v_x_3660_, 2);
v___x_3665_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3664_);
return v___x_3665_;
}
else
{
lean_object* v_head_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
lean_inc(v_tail_3663_);
v_head_3666_ = lean_ctor_get(v_x_3660_, 0);
lean_inc(v_head_3666_);
lean_dec_ref_known(v_x_3660_, 2);
v___x_3667_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3666_);
v___x_3668_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3661_, v___x_3667_, v_tail_3663_);
return v___x_3668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3669_){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___x_3670_ = lean_array_get_size(v_xs_3669_);
v___x_3671_ = lean_unsigned_to_nat(0u);
v___x_3672_ = lean_nat_dec_eq(v___x_3670_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3673_ = lean_array_to_list(v_xs_3669_);
v___x_3674_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3675_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3673_, v___x_3674_);
v___x_3676_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3677_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
lean_ctor_set(v___x_3678_, 1, v___x_3675_);
v___x_3679_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3676_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = l_Std_Format_fill(v___x_3681_);
return v___x_3682_;
}
else
{
lean_object* v___x_3683_; 
lean_dec_ref(v_xs_3669_);
v___x_3683_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3683_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = lean_unsigned_to_nat(12u);
v___x_3698_ = lean_nat_to_int(v___x_3697_);
return v___x_3698_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = lean_unsigned_to_nat(9u);
v___x_3703_ = lean_nat_to_int(v___x_3702_);
return v___x_3703_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_unsigned_to_nat(11u);
v___x_3708_ = lean_nat_to_int(v___x_3707_);
return v___x_3708_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3711_ = lean_string_length(v___x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3713_ = lean_nat_to_int(v___x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3718_){
_start:
{
lean_object* v_numFixed_3719_; lean_object* v_perms_3720_; lean_object* v_revDeps_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v_numFixed_3719_ = lean_ctor_get(v_x_3718_, 0);
lean_inc(v_numFixed_3719_);
v_perms_3720_ = lean_ctor_get(v_x_3718_, 1);
lean_inc_ref(v_perms_3720_);
v_revDeps_3721_ = lean_ctor_get(v_x_3718_, 2);
lean_inc_ref(v_revDeps_3721_);
lean_dec_ref(v_x_3718_);
v___x_3722_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3723_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3724_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3725_ = l_Nat_reprFast(v_numFixed_3719_);
v___x_3726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3724_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = 0;
v___x_3729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set_uint8(v___x_3729_, sizeof(void*)*1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3723_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_box(1);
v___x_3734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3722_);
v___x_3738_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3739_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3720_);
v___x_3740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3738_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
lean_ctor_set_uint8(v___x_3741_, sizeof(void*)*1, v___x_3728_);
v___x_3742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3737_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
lean_ctor_set(v___x_3743_, 1, v___x_3731_);
v___x_3744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set(v___x_3744_, 1, v___x_3733_);
v___x_3745_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set(v___x_3747_, 1, v___x_3722_);
v___x_3748_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3749_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3721_);
v___x_3750_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set_uint8(v___x_3751_, sizeof(void*)*1, v___x_3728_);
v___x_3752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3747_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3754_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
lean_ctor_set(v___x_3755_, 1, v___x_3752_);
v___x_3756_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3755_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3753_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set_uint8(v___x_3759_, sizeof(void*)*1, v___x_3728_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3760_, lean_object* v_prec_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3760_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3763_, lean_object* v_prec_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3763_, v_prec_3764_);
lean_dec(v_prec_3764_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___f_3774_; lean_object* v___x_5728__overap_3775_; lean_object* v___x_3776_; 
v___f_3774_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5728__overap_3775_ = lean_panic_fn_borrowed(v___f_3774_, v_msg_3768_);
lean_inc(v___y_3772_);
lean_inc_ref(v___y_3771_);
lean_inc(v___y_3770_);
lean_inc_ref(v___y_3769_);
v___x_3776_ = lean_apply_5(v___x_5728__overap_3775_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, lean_box(0));
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___f_3790_; lean_object* v___x_5738__overap_3791_; lean_object* v___x_3792_; 
v___f_3790_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5738__overap_3791_ = lean_panic_fn_borrowed(v___f_3790_, v_msg_3784_);
lean_inc(v___y_3788_);
lean_inc_ref(v___y_3787_);
lean_inc(v___y_3786_);
lean_inc_ref(v___y_3785_);
v___x_3792_ = lean_apply_5(v___x_5738__overap_3791_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, lean_box(0));
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___f_3806_; lean_object* v___x_5748__overap_3807_; lean_object* v___x_3808_; 
v___f_3806_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5748__overap_3807_ = lean_panic_fn_borrowed(v___f_3806_, v_msg_3800_);
lean_inc(v___y_3804_);
lean_inc_ref(v___y_3803_);
lean_inc(v___y_3802_);
lean_inc_ref(v___y_3801_);
v___x_3808_ = lean_apply_5(v___x_5748__overap_3807_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, lean_box(0));
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
return v_res_3815_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3819_ = lean_unsigned_to_nat(12u);
v___x_3820_ = lean_unsigned_to_nat(294u);
v___x_3821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3822_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3823_ = l_mkPanicMessageWithDecl(v___x_3822_, v___x_3821_, v___x_3820_, v___x_3819_, v___x_3818_);
return v___x_3823_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3826_ = lean_unsigned_to_nat(12u);
v___x_3827_ = lean_unsigned_to_nat(297u);
v___x_3828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3829_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3830_ = l_mkPanicMessageWithDecl(v___x_3829_, v___x_3828_, v___x_3827_, v___x_3826_, v___x_3825_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3831_, lean_object* v_as_3832_, size_t v_sz_3833_, size_t v_i_3834_, lean_object* v_b_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_a_3842_; uint8_t v___x_3846_; 
v___x_3846_ = lean_usize_dec_lt(v_i_3834_, v_sz_3833_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_b_3835_);
return v___x_3847_;
}
else
{
lean_object* v_a_3848_; 
v_a_3848_ = lean_array_uget_borrowed(v_as_3832_, v_i_3834_);
if (lean_obj_tag(v_a_3848_) == 1)
{
lean_object* v_val_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v_val_3849_ = lean_ctor_get(v_a_3848_, 0);
v___x_3850_ = lean_box(0);
v___x_3851_ = lean_unsigned_to_nat(0u);
v___x_3852_ = lean_array_get_borrowed(v___x_3850_, v_val_3849_, v___x_3851_);
if (lean_obj_tag(v___x_3852_) == 1)
{
lean_object* v_val_3853_; lean_object* v___x_3854_; 
v_val_3853_ = lean_ctor_get(v___x_3852_, 0);
v___x_3854_ = lean_array_get_borrowed(v___x_3850_, v___x_3831_, v_val_3853_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec_ref(v_b_3835_);
v___x_3855_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3856_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3855_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3866_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3859_ = v___x_3856_;
v_isShared_3860_ = v_isSharedCheck_3866_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3866_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
if (lean_obj_tag(v_a_3857_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; 
v_a_3861_ = lean_ctor_get(v_a_3857_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v_a_3857_, 1);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v_a_3861_);
v___x_3863_ = v___x_3859_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
else
{
lean_object* v_a_3865_; 
lean_del_object(v___x_3859_);
v_a_3865_ = lean_ctor_get(v_a_3857_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v_a_3857_, 1);
v_a_3842_ = v_a_3865_;
goto v___jp_3841_;
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
v_a_3867_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3856_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3856_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_object* v___x_3875_; 
lean_inc_ref(v___x_3854_);
v___x_3875_ = lean_array_push(v_b_3835_, v___x_3854_);
v_a_3842_ = v___x_3875_;
goto v___jp_3841_;
}
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3877_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3876_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_dec_ref_known(v___x_3877_, 1);
v_a_3842_ = v_b_3835_;
goto v___jp_3841_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_b_3835_);
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_box(0);
v___x_3887_ = lean_array_push(v_b_3835_, v___x_3886_);
v_a_3842_ = v___x_3887_;
goto v___jp_3841_;
}
}
v___jp_3841_:
{
size_t v___x_3843_; size_t v___x_3844_; 
v___x_3843_ = ((size_t)1ULL);
v___x_3844_ = lean_usize_add(v_i_3834_, v___x_3843_);
v_i_3834_ = v___x_3844_;
v_b_3835_ = v_a_3842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3888_, lean_object* v_as_3889_, lean_object* v_sz_3890_, lean_object* v_i_3891_, lean_object* v_b_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
size_t v_sz_boxed_3898_; size_t v_i_boxed_3899_; lean_object* v_res_3900_; 
v_sz_boxed_3898_ = lean_unbox_usize(v_sz_3890_);
lean_dec(v_sz_3890_);
v_i_boxed_3899_ = lean_unbox_usize(v_i_3891_);
lean_dec(v_i_3891_);
v_res_3900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3888_, v_as_3889_, v_sz_boxed_3898_, v_i_boxed_3899_, v_b_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec_ref(v_as_3889_);
lean_dec_ref(v___x_3888_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3903_, lean_object* v___x_3904_, lean_object* v___x_3905_, lean_object* v_a_3906_, lean_object* v_b_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
uint8_t v___x_3913_; 
v___x_3913_ = lean_nat_dec_lt(v_a_3906_, v_upperBound_3903_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; 
lean_dec(v_a_3906_);
v___x_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3914_, 0, v_b_3907_);
return v___x_3914_;
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; size_t v_sz_3917_; size_t v___x_3918_; lean_object* v___x_3919_; 
v___x_3915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3916_ = lean_array_fget_borrowed(v___x_3904_, v_a_3906_);
v_sz_3917_ = lean_array_size(v___x_3916_);
v___x_3918_ = ((size_t)0ULL);
v___x_3919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3905_, v___x_3916_, v_sz_3917_, v___x_3918_, v___x_3915_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v___x_3921_ = lean_array_push(v_b_3907_, v_a_3920_);
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_add(v_a_3906_, v___x_3922_);
lean_dec(v_a_3906_);
v_a_3906_ = v___x_3923_;
v_b_3907_ = v___x_3921_;
goto _start;
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v_b_3907_);
lean_dec(v_a_3906_);
v_a_3925_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3919_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3919_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3933_, lean_object* v___x_3934_, lean_object* v___x_3935_, lean_object* v_a_3936_, lean_object* v_b_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3933_, v___x_3934_, v___x_3935_, v_a_3936_, v_b_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec_ref(v___x_3935_);
lean_dec_ref(v___x_3934_);
lean_dec(v_upperBound_3933_);
return v_res_3943_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3945_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3946_ = lean_unsigned_to_nat(8u);
v___x_3947_ = lean_unsigned_to_nat(281u);
v___x_3948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3949_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3950_ = l_mkPanicMessageWithDecl(v___x_3949_, v___x_3948_, v___x_3947_, v___x_3946_, v___x_3945_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3951_, lean_object* v_a_3952_, lean_object* v_b_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_a_3960_; uint8_t v___x_3964_; 
v___x_3964_ = lean_nat_dec_lt(v_a_3952_, v_upperBound_3951_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; 
lean_dec(v_a_3952_);
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v_b_3953_);
return v___x_3965_;
}
else
{
lean_object* v_snd_3966_; lean_object* v_snd_3967_; lean_object* v_snd_3968_; lean_object* v_fst_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_4093_; 
v_snd_3966_ = lean_ctor_get(v_b_3953_, 1);
lean_inc(v_snd_3966_);
v_snd_3967_ = lean_ctor_get(v_snd_3966_, 1);
lean_inc(v_snd_3967_);
v_snd_3968_ = lean_ctor_get(v_snd_3967_, 1);
lean_inc(v_snd_3968_);
v_fst_3969_ = lean_ctor_get(v_b_3953_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_b_3953_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v_b_3953_, 1);
lean_dec(v_unused_4094_);
v___x_3971_ = v_b_3953_;
v_isShared_3972_ = v_isSharedCheck_4093_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_fst_3969_);
lean_dec(v_b_3953_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_4093_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v_fst_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_4091_; 
v_fst_3973_ = lean_ctor_get(v_snd_3966_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v_snd_3966_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; 
v_unused_4092_ = lean_ctor_get(v_snd_3966_, 1);
lean_dec(v_unused_4092_);
v___x_3975_ = v_snd_3966_;
v_isShared_3976_ = v_isSharedCheck_4091_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_fst_3973_);
lean_dec(v_snd_3966_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_4091_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v_fst_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4089_; 
v_fst_3977_ = lean_ctor_get(v_snd_3967_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_snd_3967_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v_snd_3967_, 1);
lean_dec(v_unused_4090_);
v___x_3979_ = v_snd_3967_;
v_isShared_3980_ = v_isSharedCheck_4089_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_fst_3977_);
lean_dec(v_snd_3967_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4089_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v_array_3981_; lean_object* v_start_3982_; lean_object* v_stop_3983_; uint8_t v___x_3984_; 
v_array_3981_ = lean_ctor_get(v_snd_3968_, 0);
v_start_3982_ = lean_ctor_get(v_snd_3968_, 1);
v_stop_3983_ = lean_ctor_get(v_snd_3968_, 2);
v___x_3984_ = lean_nat_dec_lt(v_start_3982_, v_stop_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3986_; 
lean_dec(v_a_3952_);
if (v_isShared_3980_ == 0)
{
v___x_3986_ = v___x_3979_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_fst_3977_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v_snd_3968_);
v___x_3986_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3988_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 1, v___x_3986_);
v___x_3988_ = v___x_3975_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_fst_3973_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3990_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 1, v___x_3988_);
v___x_3990_ = v___x_3971_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_fst_3969_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; 
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
return v___x_3991_;
}
}
}
}
else
{
lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4085_; 
lean_inc(v_stop_3983_);
lean_inc(v_start_3982_);
lean_inc_ref(v_array_3981_);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_snd_3968_);
if (v_isSharedCheck_4085_ == 0)
{
lean_object* v_unused_4086_; lean_object* v_unused_4087_; lean_object* v_unused_4088_; 
v_unused_4086_ = lean_ctor_get(v_snd_3968_, 2);
lean_dec(v_unused_4086_);
v_unused_4087_ = lean_ctor_get(v_snd_3968_, 1);
lean_dec(v_unused_4087_);
v_unused_4088_ = lean_ctor_get(v_snd_3968_, 0);
lean_dec(v_unused_4088_);
v___x_3996_ = v_snd_3968_;
v_isShared_3997_ = v_isSharedCheck_4085_;
goto v_resetjp_3995_;
}
else
{
lean_dec(v_snd_3968_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4085_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v_array_3998_; lean_object* v_start_3999_; lean_object* v_stop_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4005_; 
v_array_3998_ = lean_ctor_get(v_fst_3977_, 0);
v_start_3999_ = lean_ctor_get(v_fst_3977_, 1);
v_stop_4000_ = lean_ctor_get(v_fst_3977_, 2);
v___x_4001_ = lean_array_fget(v_array_3981_, v_start_3982_);
v___x_4002_ = lean_unsigned_to_nat(1u);
v___x_4003_ = lean_nat_add(v_start_3982_, v___x_4002_);
lean_dec(v_start_3982_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 1, v___x_4003_);
v___x_4005_ = v___x_3996_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_array_3981_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v___x_4003_);
lean_ctor_set(v_reuseFailAlloc_4084_, 2, v_stop_3983_);
v___x_4005_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
uint8_t v___x_4006_; 
v___x_4006_ = lean_nat_dec_lt(v_start_3999_, v_stop_4000_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4008_; 
lean_dec(v___x_4001_);
lean_dec(v_a_3952_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 1, v___x_4005_);
v___x_4008_ = v___x_3979_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_fst_3977_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v___x_4005_);
v___x_4008_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4010_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 1, v___x_4008_);
v___x_4010_ = v___x_3975_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_fst_3973_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v___x_4008_);
v___x_4010_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
lean_object* v___x_4012_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 1, v___x_4010_);
v___x_4012_ = v___x_3971_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_fst_3969_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4010_);
v___x_4012_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
return v___x_4013_;
}
}
}
}
else
{
lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4080_; 
lean_inc(v_stop_4000_);
lean_inc(v_start_3999_);
lean_inc_ref(v_array_3998_);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_fst_3977_);
if (v_isSharedCheck_4080_ == 0)
{
lean_object* v_unused_4081_; lean_object* v_unused_4082_; lean_object* v_unused_4083_; 
v_unused_4081_ = lean_ctor_get(v_fst_3977_, 2);
lean_dec(v_unused_4081_);
v_unused_4082_ = lean_ctor_get(v_fst_3977_, 1);
lean_dec(v_unused_4082_);
v_unused_4083_ = lean_ctor_get(v_fst_3977_, 0);
lean_dec(v_unused_4083_);
v___x_4018_ = v_fst_3977_;
v_isShared_4019_ = v_isSharedCheck_4080_;
goto v_resetjp_4017_;
}
else
{
lean_dec(v_fst_3977_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4080_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4020_; lean_object* v___x_4022_; 
v___x_4020_ = lean_nat_add(v_start_3999_, v___x_4002_);
lean_dec(v_start_3999_);
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 1, v___x_4020_);
v___x_4022_ = v___x_4018_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_array_3998_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v___x_4020_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_stop_4000_);
v___x_4022_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
if (lean_obj_tag(v___x_4001_) == 1)
{
lean_object* v_val_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4067_; 
v_val_4023_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4025_ = v___x_4001_;
v_isShared_4026_ = v_isSharedCheck_4067_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_val_4023_);
lean_dec(v___x_4001_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4067_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4032_; 
v___x_4027_ = lean_box(0);
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4030_ = lean_array_get(v___x_4027_, v_val_4023_, v___x_4028_);
lean_dec(v_val_4023_);
lean_inc(v_a_3952_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v_a_3952_);
v___x_4032_ = v___x_4025_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_3952_);
v___x_4032_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
uint8_t v___x_4033_; 
v___x_4033_ = l_Option_instDecidableEq___redArg(v___x_4029_, v___x_4030_, v___x_4032_);
if (v___x_4033_ == 0)
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_dec_ref(v___x_4022_);
lean_dec_ref(v___x_4005_);
lean_del_object(v___x_3979_);
lean_del_object(v___x_3975_);
lean_dec(v_fst_3973_);
lean_del_object(v___x_3971_);
lean_dec(v_fst_3969_);
v___x_4034_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4035_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4034_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4045_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4045_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4045_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
if (lean_obj_tag(v_a_4036_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; 
lean_dec(v_a_3952_);
v_a_4040_ = lean_ctor_get(v_a_4036_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v_a_4036_, 1);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v_a_4040_);
v___x_4042_ = v___x_4038_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
else
{
lean_object* v_a_4044_; 
lean_del_object(v___x_4038_);
v_a_4044_ = lean_ctor_get(v_a_4036_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v_a_4036_, 1);
v_a_3960_ = v_a_4044_;
goto v___jp_3959_;
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec(v_a_3952_);
v_a_4046_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4035_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4035_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
lean_inc(v_fst_3973_);
v___x_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4054_, 0, v_fst_3973_);
v___x_4055_ = lean_array_push(v_fst_3969_, v___x_4054_);
v___x_4056_ = lean_nat_add(v_fst_3973_, v___x_4002_);
lean_dec(v_fst_3973_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 1, v___x_4005_);
lean_ctor_set(v___x_3979_, 0, v___x_4022_);
v___x_4058_ = v___x_3979_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v___x_4005_);
v___x_4058_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4060_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 1, v___x_4058_);
lean_ctor_set(v___x_3975_, 0, v___x_4056_);
v___x_4060_ = v___x_3975_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4062_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 1, v___x_4060_);
lean_ctor_set(v___x_3971_, 0, v___x_4055_);
v___x_4062_ = v___x_3971_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4055_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
v_a_3960_ = v___x_4062_;
goto v___jp_3959_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4071_; 
lean_dec(v___x_4001_);
v___x_4068_ = lean_box(0);
v___x_4069_ = lean_array_push(v_fst_3969_, v___x_4068_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 1, v___x_4005_);
lean_ctor_set(v___x_3979_, 0, v___x_4022_);
v___x_4071_ = v___x_3979_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v___x_4005_);
v___x_4071_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4073_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 1, v___x_4071_);
v___x_4073_ = v___x_3975_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_fst_3973_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4071_);
v___x_4073_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4075_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 1, v___x_4073_);
lean_ctor_set(v___x_3971_, 0, v___x_4069_);
v___x_4075_ = v___x_3971_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
v_a_3960_ = v___x_4075_;
goto v___jp_3959_;
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
v___jp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_unsigned_to_nat(1u);
v___x_3962_ = lean_nat_add(v_a_3952_, v___x_3961_);
lean_dec(v_a_3952_);
v_a_3952_ = v___x_3962_;
v_b_3953_ = v_a_3960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4095_, lean_object* v_a_4096_, lean_object* v_b_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4095_, v_a_4096_, v_b_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v_upperBound_4095_);
return v_res_4103_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4105_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4106_ = lean_unsigned_to_nat(4u);
v___x_4107_ = lean_unsigned_to_nat(275u);
v___x_4108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4109_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4110_ = l_mkPanicMessageWithDecl(v___x_4109_, v___x_4108_, v___x_4107_, v___x_4106_, v___x_4105_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4111_, lean_object* v___x_4112_, lean_object* v___x_4113_, lean_object* v_xs_4114_, lean_object* v_x_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_graph_4121_; lean_object* v_revDeps_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4175_; 
v_graph_4121_ = lean_ctor_get(v_a_4111_, 0);
v_revDeps_4122_ = lean_ctor_get(v_a_4111_, 1);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_a_4111_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4124_ = v_a_4111_;
v_isShared_4125_ = v_isSharedCheck_4175_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_revDeps_4122_);
lean_inc(v_graph_4121_);
lean_dec(v_a_4111_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4175_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
v___x_4126_ = lean_array_get_borrowed(v___x_4112_, v_graph_4121_, v___x_4113_);
v___x_4127_ = lean_array_get_size(v_xs_4114_);
v___x_4128_ = lean_array_get_size(v___x_4126_);
v___x_4129_ = lean_nat_dec_eq(v___x_4127_, v___x_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_del_object(v___x_4124_);
lean_dec_ref(v_revDeps_4122_);
lean_dec_ref(v_graph_4121_);
lean_dec_ref(v_xs_4114_);
lean_dec(v___x_4113_);
v___x_4130_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4131_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4130_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
return v___x_4131_;
}
else
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4132_ = lean_mk_empty_array_with_capacity(v___x_4113_);
lean_inc_n(v___x_4113_, 2);
v___x_4133_ = l_Array_toSubarray___redArg(v_xs_4114_, v___x_4113_, v___x_4127_);
lean_inc(v___x_4126_);
v___x_4134_ = l_Array_toSubarray___redArg(v___x_4126_, v___x_4113_, v___x_4128_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 1, v___x_4134_);
lean_ctor_set(v___x_4124_, 0, v___x_4133_);
v___x_4136_ = v___x_4124_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4133_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
lean_inc(v___x_4113_);
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4113_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4132_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4127_, v___x_4113_, v___x_4138_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v_snd_4141_; lean_object* v_fst_4142_; lean_object* v_fst_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v_snd_4141_ = lean_ctor_get(v_a_4140_, 1);
lean_inc(v_snd_4141_);
v_fst_4142_ = lean_ctor_get(v_a_4140_, 0);
lean_inc_n(v_fst_4142_, 2);
lean_dec(v_a_4140_);
v_fst_4143_ = lean_ctor_get(v_snd_4141_, 0);
lean_inc(v_fst_4143_);
lean_dec(v_snd_4141_);
v___x_4144_ = lean_unsigned_to_nat(1u);
v___x_4145_ = lean_array_get_size(v_graph_4121_);
v___x_4146_ = lean_mk_empty_array_with_capacity(v___x_4144_);
v___x_4147_ = lean_array_push(v___x_4146_, v_fst_4142_);
v___x_4148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4145_, v_graph_4121_, v_fst_4142_, v___x_4144_, v___x_4147_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v_fst_4142_);
lean_dec_ref(v_graph_4121_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4157_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4151_ = v___x_4148_;
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4153_, 0, v_fst_4143_);
lean_ctor_set(v___x_4153_, 1, v_a_4149_);
lean_ctor_set(v___x_4153_, 2, v_revDeps_4122_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4153_);
v___x_4155_ = v___x_4151_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec(v_fst_4143_);
lean_dec_ref(v_revDeps_4122_);
v_a_4158_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4148_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4148_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v_revDeps_4122_);
lean_dec_ref(v_graph_4121_);
v_a_4166_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4139_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4139_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4176_, lean_object* v___x_4177_, lean_object* v___x_4178_, lean_object* v_xs_4179_, lean_object* v_x_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4176_, v___x_4177_, v___x_4178_, v_xs_4179_, v_x_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec_ref(v_x_4180_);
lean_dec_ref(v___x_4177_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v___x_4193_; 
lean_inc_ref(v_preDefs_4187_);
v___x_4193_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v_value_4198_; lean_object* v___x_4199_; lean_object* v___f_4200_; uint8_t v___x_4201_; lean_object* v___x_4202_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref_known(v___x_4193_, 1);
v___x_4195_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = lean_array_get(v___x_4195_, v_preDefs_4187_, v___x_4196_);
lean_dec_ref(v_preDefs_4187_);
v_value_4198_ = lean_ctor_get(v___x_4197_, 7);
lean_inc_ref(v_value_4198_);
lean_dec(v___x_4197_);
v___x_4199_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4200_, 0, v_a_4194_);
lean_closure_set(v___f_4200_, 1, v___x_4199_);
lean_closure_set(v___f_4200_, 2, v___x_4196_);
v___x_4201_ = 0;
v___x_4202_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4198_, v___f_4200_, v___x_4201_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
return v___x_4202_;
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec_ref(v_preDefs_4187_);
v_a_4203_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4193_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4193_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4218_, lean_object* v___x_4219_, lean_object* v___x_4220_, lean_object* v_inst_4221_, lean_object* v_R_4222_, lean_object* v_a_4223_, lean_object* v_b_4224_, lean_object* v_c_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4218_, v___x_4219_, v___x_4220_, v_a_4223_, v_b_4224_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4232_, lean_object* v___x_4233_, lean_object* v___x_4234_, lean_object* v_inst_4235_, lean_object* v_R_4236_, lean_object* v_a_4237_, lean_object* v_b_4238_, lean_object* v_c_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4232_, v___x_4233_, v___x_4234_, v_inst_4235_, v_R_4236_, v_a_4237_, v_b_4238_, v_c_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec_ref(v___x_4234_);
lean_dec_ref(v___x_4233_);
lean_dec(v_upperBound_4232_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4246_, lean_object* v_inst_4247_, lean_object* v_R_4248_, lean_object* v_a_4249_, lean_object* v_b_4250_, lean_object* v_c_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4246_, v_a_4249_, v_b_4250_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4258_, lean_object* v_inst_4259_, lean_object* v_R_4260_, lean_object* v_a_4261_, lean_object* v_b_4262_, lean_object* v_c_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4258_, v_inst_4259_, v_R_4260_, v_a_4261_, v_b_4262_, v_c_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v_upperBound_4258_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4270_, size_t v_i_4271_, size_t v_stop_4272_, lean_object* v_b_4273_){
_start:
{
uint8_t v___x_4274_; 
v___x_4274_ = lean_usize_dec_eq(v_i_4271_, v_stop_4272_);
if (v___x_4274_ == 0)
{
size_t v___x_4275_; size_t v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = ((size_t)1ULL);
v___x_4276_ = lean_usize_sub(v_i_4271_, v___x_4275_);
v___x_4277_ = lean_array_uget_borrowed(v_as_4270_, v___x_4276_);
if (lean_obj_tag(v___x_4277_) == 0)
{
v_i_4271_ = v___x_4276_;
goto _start;
}
else
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = lean_unsigned_to_nat(1u);
v___x_4280_ = lean_nat_add(v_b_4273_, v___x_4279_);
lean_dec(v_b_4273_);
v_i_4271_ = v___x_4276_;
v_b_4273_ = v___x_4280_;
goto _start;
}
}
else
{
return v_b_4273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4282_, lean_object* v_i_4283_, lean_object* v_stop_4284_, lean_object* v_b_4285_){
_start:
{
size_t v_i_boxed_4286_; size_t v_stop_boxed_4287_; lean_object* v_res_4288_; 
v_i_boxed_4286_ = lean_unbox_usize(v_i_4283_);
lean_dec(v_i_4283_);
v_stop_boxed_4287_ = lean_unbox_usize(v_stop_4284_);
lean_dec(v_stop_4284_);
v_res_4288_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4282_, v_i_boxed_4286_, v_stop_boxed_4287_, v_b_4285_);
lean_dec_ref(v_as_4282_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4289_){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4290_ = lean_unsigned_to_nat(0u);
v___x_4291_ = lean_array_get_size(v_perm_4289_);
v___x_4292_ = lean_nat_dec_lt(v___x_4290_, v___x_4291_);
if (v___x_4292_ == 0)
{
return v___x_4290_;
}
else
{
size_t v___x_4293_; size_t v___x_4294_; lean_object* v___x_4295_; 
v___x_4293_ = lean_usize_of_nat(v___x_4291_);
v___x_4294_ = ((size_t)0ULL);
v___x_4295_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4289_, v___x_4293_, v___x_4294_, v___x_4290_);
return v___x_4295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4296_);
lean_dec_ref(v_perm_4296_);
return v_res_4297_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4298_, lean_object* v_i_4299_){
_start:
{
lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4300_ = lean_array_get_size(v_perm_4298_);
v___x_4301_ = lean_nat_dec_lt(v_i_4299_, v___x_4300_);
if (v___x_4301_ == 0)
{
return v___x_4301_;
}
else
{
lean_object* v___x_4302_; 
v___x_4302_ = lean_array_fget_borrowed(v_perm_4298_, v_i_4299_);
if (lean_obj_tag(v___x_4302_) == 0)
{
uint8_t v___x_4303_; 
v___x_4303_ = 0;
return v___x_4303_;
}
else
{
return v___x_4301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4304_, lean_object* v_i_4305_){
_start:
{
uint8_t v_res_4306_; lean_object* v_r_4307_; 
v_res_4306_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4304_, v_i_4305_);
lean_dec(v_i_4305_);
lean_dec_ref(v_perm_4304_);
v_r_4307_ = lean_box(v_res_4306_);
return v_r_4307_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___f_4314_; lean_object* v___x_907__overap_4315_; lean_object* v___x_4316_; 
v___f_4314_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_907__overap_4315_ = lean_panic_fn_borrowed(v___f_4314_, v_msg_4308_);
lean_inc(v___y_4312_);
lean_inc_ref(v___y_4311_);
lean_inc(v___y_4310_);
lean_inc_ref(v___y_4309_);
v___x_4316_ = lean_apply_5(v___x_907__overap_4315_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, lean_box(0));
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4324_, lean_object* v_msg_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4332_, lean_object* v_msg_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4332_, v_msg_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4340_, lean_object* v_maxFVars_x3f_4341_, lean_object* v_k_4342_, uint8_t v_cleanupAnnotations_4343_, uint8_t v_whnfType_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v___f_4350_; lean_object* v___x_4351_; 
v___f_4350_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4350_, 0, v_k_4342_);
v___x_4351_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4340_, v_maxFVars_x3f_4341_, v___f_4350_, v_cleanupAnnotations_4343_, v_whnfType_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
v_a_4360_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4351_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4351_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4368_, lean_object* v_maxFVars_x3f_4369_, lean_object* v_k_4370_, lean_object* v_cleanupAnnotations_4371_, lean_object* v_whnfType_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4378_; uint8_t v_whnfType_boxed_4379_; lean_object* v_res_4380_; 
v_cleanupAnnotations_boxed_4378_ = lean_unbox(v_cleanupAnnotations_4371_);
v_whnfType_boxed_4379_ = lean_unbox(v_whnfType_4372_);
v_res_4380_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4368_, v_maxFVars_x3f_4369_, v_k_4370_, v_cleanupAnnotations_boxed_4378_, v_whnfType_boxed_4379_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4381_, lean_object* v_type_4382_, lean_object* v_maxFVars_x3f_4383_, lean_object* v_k_4384_, uint8_t v_cleanupAnnotations_4385_, uint8_t v_whnfType_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4382_, v_maxFVars_x3f_4383_, v_k_4384_, v_cleanupAnnotations_4385_, v_whnfType_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4393_, lean_object* v_type_4394_, lean_object* v_maxFVars_x3f_4395_, lean_object* v_k_4396_, lean_object* v_cleanupAnnotations_4397_, lean_object* v_whnfType_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4404_; uint8_t v_whnfType_boxed_4405_; lean_object* v_res_4406_; 
v_cleanupAnnotations_boxed_4404_ = lean_unbox(v_cleanupAnnotations_4397_);
v_whnfType_boxed_4405_ = lean_unbox(v_whnfType_4398_);
v_res_4406_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4393_, v_type_4394_, v_maxFVars_x3f_4395_, v_k_4396_, v_cleanupAnnotations_boxed_4404_, v_whnfType_boxed_4405_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
return v_res_4406_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4409_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4410_ = lean_unsigned_to_nat(6u);
v___x_4411_ = lean_unsigned_to_nat(329u);
v___x_4412_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4413_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4414_ = l_mkPanicMessageWithDecl(v___x_4413_, v___x_4412_, v___x_4411_, v___x_4410_, v___x_4409_);
return v___x_4414_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4418_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4419_ = lean_unsigned_to_nat(8u);
v___x_4420_ = lean_unsigned_to_nat(322u);
v___x_4421_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4422_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4423_ = l_mkPanicMessageWithDecl(v___x_4422_, v___x_4421_, v___x_4420_, v___x_4419_, v___x_4418_);
return v___x_4423_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4425_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4426_ = lean_unsigned_to_nat(8u);
v___x_4427_ = lean_unsigned_to_nat(325u);
v___x_4428_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4429_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4430_ = l_mkPanicMessageWithDecl(v___x_4429_, v___x_4428_, v___x_4427_, v___x_4426_, v___x_4425_);
return v___x_4430_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4432_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4433_ = lean_unsigned_to_nat(8u);
v___x_4434_ = lean_unsigned_to_nat(324u);
v___x_4435_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4436_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4437_ = l_mkPanicMessageWithDecl(v___x_4436_, v___x_4435_, v___x_4434_, v___x_4433_, v___x_4432_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4438_, lean_object* v___x_4439_, lean_object* v_xs_4440_, lean_object* v_val_4441_, lean_object* v_i_4442_, lean_object* v_perm_4443_, lean_object* v_k_4444_, lean_object* v_xs_x27_4445_, lean_object* v_type_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; uint8_t v___x_4453_; 
v___x_4452_ = lean_array_get_size(v_xs_x27_4445_);
v___x_4453_ = lean_nat_dec_eq(v___x_4452_, v___x_4438_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4454_; lean_object* v___x_4455_; 
lean_dec_ref(v_type_4446_);
lean_dec_ref(v_k_4444_);
lean_dec_ref(v_perm_4443_);
lean_dec_ref(v_xs_4440_);
v___x_4454_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4455_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4454_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
return v___x_4455_;
}
else
{
lean_object* v___x_4456_; lean_object* v_x_4457_; lean_object* v___x_4458_; 
v___x_4456_ = lean_unsigned_to_nat(0u);
v_x_4457_ = lean_array_get_borrowed(v___x_4439_, v_xs_x27_4445_, v___x_4456_);
lean_inc(v___y_4450_);
lean_inc_ref(v___y_4449_);
lean_inc(v___y_4448_);
lean_inc_ref(v___y_4447_);
lean_inc(v_x_4457_);
v___x_4458_ = lean_infer_type(v_x_4457_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; uint8_t v___x_4460_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4458_, 1);
v___x_4460_ = l_Lean_Expr_hasLooseBVars(v_a_4459_);
lean_dec(v_a_4459_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4461_ = lean_array_get_size(v_xs_4440_);
v___x_4462_ = lean_nat_dec_lt(v_val_4441_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
lean_dec_ref(v_type_4446_);
lean_dec_ref(v_k_4444_);
lean_dec_ref(v_perm_4443_);
lean_dec_ref(v_xs_4440_);
v___x_4463_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4464_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4463_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
return v___x_4464_;
}
else
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4465_ = lean_nat_add(v_i_4442_, v___x_4438_);
lean_inc(v_x_4457_);
v___x_4466_ = lean_array_set(v_xs_4440_, v_val_4441_, v_x_4457_);
v___x_4467_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4443_, v_k_4444_, v___x_4465_, v_type_4446_, v___x_4466_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
return v___x_4467_;
}
}
else
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_dec_ref(v_type_4446_);
lean_dec_ref(v_k_4444_);
lean_dec_ref(v_perm_4443_);
lean_dec_ref(v_xs_4440_);
v___x_4468_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4469_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4468_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
return v___x_4469_;
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec_ref(v_type_4446_);
lean_dec_ref(v_k_4444_);
lean_dec_ref(v_perm_4443_);
lean_dec_ref(v_xs_4440_);
v_a_4470_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4458_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4458_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4478_, lean_object* v___x_4479_, lean_object* v_xs_4480_, lean_object* v_val_4481_, lean_object* v_i_4482_, lean_object* v_perm_4483_, lean_object* v_k_4484_, lean_object* v_xs_x27_4485_, lean_object* v_type_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4478_, v___x_4479_, v_xs_4480_, v_val_4481_, v_i_4482_, v_perm_4483_, v_k_4484_, v_xs_x27_4485_, v_type_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec_ref(v_xs_x27_4485_);
lean_dec(v_i_4482_);
lean_dec(v_val_4481_);
lean_dec_ref(v___x_4479_);
lean_dec(v___x_4478_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4493_, lean_object* v_k_4494_, lean_object* v_i_4495_, lean_object* v_type_4496_, lean_object* v_xs_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v___x_4503_; uint8_t v___x_4504_; 
v___x_4503_ = lean_array_get_size(v_perm_4493_);
v___x_4504_ = lean_nat_dec_lt(v_i_4495_, v___x_4503_);
if (v___x_4504_ == 0)
{
lean_object* v___x_4505_; 
lean_dec_ref(v_type_4496_);
lean_dec(v_i_4495_);
lean_dec_ref(v_perm_4493_);
lean_inc(v_a_4501_);
lean_inc_ref(v_a_4500_);
lean_inc(v_a_4499_);
lean_inc_ref(v_a_4498_);
v___x_4505_ = lean_apply_6(v_k_4494_, v_xs_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, lean_box(0));
return v___x_4505_;
}
else
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_array_fget_borrowed(v_perm_4493_, v_i_4495_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v___x_4507_; 
lean_inc(v_a_4501_);
lean_inc_ref(v_a_4500_);
lean_inc(v_a_4499_);
lean_inc_ref(v_a_4498_);
v___x_4507_ = lean_whnf(v_type_4496_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; uint8_t v___x_4509_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref_known(v___x_4507_, 1);
v___x_4509_ = l_Lean_Expr_isForall(v_a_4508_);
if (v___x_4509_ == 0)
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec(v_a_4508_);
lean_dec_ref(v_xs_4497_);
lean_dec(v_i_4495_);
lean_dec_ref(v_k_4494_);
lean_dec_ref(v_perm_4493_);
v___x_4510_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4511_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4510_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4511_;
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4512_ = lean_unsigned_to_nat(1u);
v___x_4513_ = lean_nat_add(v_i_4495_, v___x_4512_);
lean_dec(v_i_4495_);
v___x_4514_ = l_Lean_Expr_bindingBody_x21(v_a_4508_);
lean_dec(v_a_4508_);
v_i_4495_ = v___x_4513_;
v_type_4496_ = v___x_4514_;
goto _start;
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec_ref(v_xs_4497_);
lean_dec(v_i_4495_);
lean_dec_ref(v_k_4494_);
lean_dec_ref(v_perm_4493_);
v_a_4516_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4507_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4507_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
else
{
lean_object* v_val_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___f_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; 
v_val_4524_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_val_4524_);
v___x_4525_ = l_Lean_instInhabitedExpr;
v___x_4526_ = lean_unsigned_to_nat(1u);
v___f_4527_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4527_, 0, v___x_4526_);
lean_closure_set(v___f_4527_, 1, v___x_4525_);
lean_closure_set(v___f_4527_, 2, v_xs_4497_);
lean_closure_set(v___f_4527_, 3, v_val_4524_);
lean_closure_set(v___f_4527_, 4, v_i_4495_);
lean_closure_set(v___f_4527_, 5, v_perm_4493_);
lean_closure_set(v___f_4527_, 6, v_k_4494_);
v___x_4528_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4529_ = 0;
v___x_4530_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4496_, v___x_4528_, v___f_4527_, v___x_4504_, v___x_4529_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4531_, lean_object* v_k_4532_, lean_object* v_i_4533_, lean_object* v_type_4534_, lean_object* v_xs_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4531_, v_k_4532_, v_i_4533_, v_type_4534_, v_xs_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
lean_dec_ref(v_a_4536_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4542_, lean_object* v_perm_4543_, lean_object* v_k_4544_, lean_object* v_i_4545_, lean_object* v_type_4546_, lean_object* v_xs_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_){
_start:
{
lean_object* v___x_4553_; 
v___x_4553_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4543_, v_k_4544_, v_i_4545_, v_type_4546_, v_xs_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4554_, lean_object* v_perm_4555_, lean_object* v_k_4556_, lean_object* v_i_4557_, lean_object* v_type_4558_, lean_object* v_xs_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4554_, v_perm_4555_, v_k_4556_, v_i_4557_, v_type_4558_, v_xs_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
return v_res_4565_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = lean_unsigned_to_nat(0u);
v___x_4567_ = l_Lean_Level_ofNat(v___x_4566_);
return v___x_4567_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4568_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4569_ = l_Lean_mkSort(v___x_4568_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4570_, lean_object* v_type_4571_, lean_object* v_k_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4578_ = lean_unsigned_to_nat(0u);
v___x_4579_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4570_);
v___x_4580_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4581_ = lean_mk_array(v___x_4579_, v___x_4580_);
v___x_4582_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4570_, v_k_4572_, v___x_4578_, v_type_4571_, v___x_4581_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4583_, lean_object* v_type_4584_, lean_object* v_k_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4583_, v_type_4584_, v_k_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4592_, lean_object* v_perm_4593_, lean_object* v_type_4594_, lean_object* v_k_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4593_, v_type_4594_, v_k_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4602_, lean_object* v_perm_4603_, lean_object* v_type_4604_, lean_object* v_k_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4602_, v_perm_4603_, v_type_4604_, v_k_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
lean_dec(v_a_4609_);
lean_dec_ref(v_a_4608_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4612_, lean_object* v_runInBase_4613_, lean_object* v_b_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_apply_1(v_k_4612_, v_b_4614_);
lean_inc(v___y_4618_);
lean_inc_ref(v___y_4617_);
lean_inc(v___y_4616_);
lean_inc_ref(v___y_4615_);
v___x_4621_ = lean_apply_7(v_runInBase_4613_, lean_box(0), v___x_4620_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, lean_box(0));
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4622_, lean_object* v_runInBase_4623_, lean_object* v_b_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4622_, v_runInBase_4623_, v_b_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4631_, lean_object* v_perm_4632_, lean_object* v_type_4633_, lean_object* v_runInBase_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v___f_4640_; lean_object* v___x_4641_; 
v___f_4640_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4640_, 0, v_k_4631_);
lean_closure_set(v___f_4640_, 1, v_runInBase_4634_);
v___x_4641_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4632_, v_type_4633_, v___f_4640_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4642_, lean_object* v_perm_4643_, lean_object* v_type_4644_, lean_object* v_runInBase_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4642_, v_perm_4643_, v_type_4644_, v_runInBase_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4652_, lean_object* v_inst_4653_, lean_object* v_perm_4654_, lean_object* v_type_4655_, lean_object* v_k_4656_){
_start:
{
lean_object* v_toBind_4657_; lean_object* v_liftWith_4658_; lean_object* v_restoreM_4659_; lean_object* v___f_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v_toBind_4657_ = lean_ctor_get(v_inst_4653_, 1);
lean_inc(v_toBind_4657_);
lean_dec_ref(v_inst_4653_);
v_liftWith_4658_ = lean_ctor_get(v_inst_4652_, 0);
lean_inc(v_liftWith_4658_);
v_restoreM_4659_ = lean_ctor_get(v_inst_4652_, 1);
lean_inc(v_restoreM_4659_);
lean_dec_ref(v_inst_4652_);
v___f_4660_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4660_, 0, v_k_4656_);
lean_closure_set(v___f_4660_, 1, v_perm_4654_);
lean_closure_set(v___f_4660_, 2, v_type_4655_);
v___x_4661_ = lean_apply_2(v_liftWith_4658_, lean_box(0), v___f_4660_);
v___x_4662_ = lean_apply_1(v_restoreM_4659_, lean_box(0));
v___x_4663_ = lean_apply_4(v_toBind_4657_, lean_box(0), lean_box(0), v___x_4661_, v___x_4662_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4664_, lean_object* v_00_u03b1_4665_, lean_object* v_inst_4666_, lean_object* v_inst_4667_, lean_object* v_perm_4668_, lean_object* v_type_4669_, lean_object* v_k_4670_){
_start:
{
lean_object* v___x_4671_; 
v___x_4671_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4666_, v_inst_4667_, v_perm_4668_, v_type_4669_, v_k_4670_);
return v___x_4671_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v___f_4678_; lean_object* v___x_598__overap_4679_; lean_object* v___x_4680_; 
v___f_4678_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_598__overap_4679_ = lean_panic_fn_borrowed(v___f_4678_, v_msg_4672_);
lean_inc(v___y_4676_);
lean_inc_ref(v___y_4675_);
lean_inc(v___y_4674_);
lean_inc_ref(v___y_4673_);
v___x_4680_ = lean_apply_5(v___x_598__overap_4679_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, lean_box(0));
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
return v_res_4687_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4690_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4691_ = lean_unsigned_to_nat(10u);
v___x_4692_ = lean_unsigned_to_nat(353u);
v___x_4693_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4694_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4695_ = l_mkPanicMessageWithDecl(v___x_4694_, v___x_4693_, v___x_4692_, v___x_4691_, v___x_4690_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4696_, lean_object* v_xs_4697_, lean_object* v_tail_4698_, lean_object* v_ys_4699_, lean_object* v_type_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4696_, v_xs_4697_, v_tail_4698_, v_ys_4699_, v_type_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec_ref(v_ys_4699_);
lean_dec(v___x_4696_);
return v_res_4706_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4707_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4708_ = lean_unsigned_to_nat(8u);
v___x_4709_ = lean_unsigned_to_nat(349u);
v___x_4710_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4711_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4712_ = l_mkPanicMessageWithDecl(v___x_4711_, v___x_4710_, v___x_4709_, v___x_4708_, v___x_4707_);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4713_, lean_object* v_x_4714_, lean_object* v_x_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
if (lean_obj_tag(v_x_4714_) == 0)
{
lean_object* v___x_4721_; 
lean_dec_ref(v_xs_4713_);
v___x_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4721_, 0, v_x_4715_);
return v___x_4721_;
}
else
{
lean_object* v_head_4722_; 
v_head_4722_ = lean_ctor_get(v_x_4714_, 0);
if (lean_obj_tag(v_head_4722_) == 0)
{
lean_object* v_tail_4723_; lean_object* v___x_4724_; lean_object* v___f_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; lean_object* v___x_4728_; 
v_tail_4723_ = lean_ctor_get(v_x_4714_, 1);
lean_inc(v_tail_4723_);
lean_dec_ref_known(v_x_4714_, 2);
v___x_4724_ = lean_unsigned_to_nat(1u);
v___f_4725_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4725_, 0, v___x_4724_);
lean_closure_set(v___f_4725_, 1, v_xs_4713_);
lean_closure_set(v___f_4725_, 2, v_tail_4723_);
v___x_4726_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4727_ = 0;
v___x_4728_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4715_, v___x_4726_, v___f_4725_, v___x_4727_, v___x_4727_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_);
return v___x_4728_;
}
else
{
lean_object* v_tail_4729_; lean_object* v_val_4730_; lean_object* v___x_4731_; uint8_t v___x_4732_; 
lean_inc_ref(v_head_4722_);
v_tail_4729_ = lean_ctor_get(v_x_4714_, 1);
lean_inc(v_tail_4729_);
lean_dec_ref_known(v_x_4714_, 2);
v_val_4730_ = lean_ctor_get(v_head_4722_, 0);
lean_inc(v_val_4730_);
lean_dec_ref_known(v_head_4722_, 1);
v___x_4731_ = lean_array_get_size(v_xs_4713_);
v___x_4732_ = lean_nat_dec_lt(v_val_4730_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_object* v___x_4733_; lean_object* v___x_4734_; 
lean_dec(v_val_4730_);
lean_dec(v_tail_4729_);
lean_dec_ref(v_x_4715_);
lean_dec_ref(v_xs_4713_);
v___x_4733_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4734_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4733_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_);
return v___x_4734_;
}
else
{
lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
v___x_4735_ = l_Lean_instInhabitedExpr;
v___x_4736_ = lean_array_get_borrowed(v___x_4735_, v_xs_4713_, v_val_4730_);
lean_dec(v_val_4730_);
v___x_4737_ = lean_unsigned_to_nat(1u);
v___x_4738_ = lean_mk_empty_array_with_capacity(v___x_4737_);
lean_inc(v___x_4736_);
v___x_4739_ = lean_array_push(v___x_4738_, v___x_4736_);
v___x_4740_ = l_Lean_Meta_instantiateForall(v_x_4715_, v___x_4739_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_);
lean_dec_ref(v___x_4739_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref_known(v___x_4740_, 1);
v_x_4714_ = v_tail_4729_;
v_x_4715_ = v_a_4741_;
goto _start;
}
else
{
lean_dec(v_tail_4729_);
lean_dec_ref(v_xs_4713_);
return v___x_4740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4743_, lean_object* v_xs_4744_, lean_object* v_tail_4745_, lean_object* v_ys_4746_, lean_object* v_type_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v___x_4753_; uint8_t v___x_4754_; 
v___x_4753_ = lean_array_get_size(v_ys_4746_);
v___x_4754_ = lean_nat_dec_eq(v___x_4753_, v___x_4743_);
if (v___x_4754_ == 0)
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
lean_dec_ref(v_type_4747_);
lean_dec(v_tail_4745_);
lean_dec_ref(v_xs_4744_);
v___x_4755_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4756_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4755_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
return v___x_4756_;
}
else
{
lean_object* v___x_4757_; 
v___x_4757_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4744_, v_tail_4745_, v_type_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; uint8_t v___x_4759_; uint8_t v___x_4760_; lean_object* v___x_4761_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v___x_4757_, 1);
v___x_4759_ = 0;
v___x_4760_ = 1;
v___x_4761_ = l_Lean_Meta_mkForallFVars(v_ys_4746_, v_a_4758_, v___x_4759_, v___x_4754_, v___x_4754_, v___x_4760_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
return v___x_4761_;
}
else
{
return v___x_4757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4762_, lean_object* v_x_4763_, lean_object* v_x_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4762_, v_x_4763_, v_x_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
return v_res_4770_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4773_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4774_ = lean_unsigned_to_nat(2u);
v___x_4775_ = lean_unsigned_to_nat(343u);
v___x_4776_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4777_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4778_ = l_mkPanicMessageWithDecl(v___x_4777_, v___x_4776_, v___x_4775_, v___x_4774_, v___x_4773_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4779_, lean_object* v_type_u2080_4780_, lean_object* v_xs_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4787_ = lean_array_get_size(v_xs_4781_);
v___x_4788_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4779_);
v___x_4789_ = lean_nat_dec_eq(v___x_4787_, v___x_4788_);
lean_dec(v___x_4788_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; lean_object* v___x_4791_; 
lean_dec_ref(v_xs_4781_);
lean_dec_ref(v_type_u2080_4780_);
lean_dec_ref(v_perm_4779_);
v___x_4790_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4791_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4790_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
return v___x_4791_;
}
else
{
lean_object* v_mask_4792_; lean_object* v___x_4793_; 
v_mask_4792_ = lean_array_to_list(v_perm_4779_);
v___x_4793_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4781_, v_mask_4792_, v_type_u2080_4780_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
return v___x_4793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4794_, lean_object* v_type_u2080_4795_, lean_object* v_xs_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4794_, v_type_u2080_4795_, v_xs_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4803_, lean_object* v_maxFVars_4804_, lean_object* v_k_4805_, uint8_t v_cleanupAnnotations_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v___f_4812_; uint8_t v___x_4813_; uint8_t v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___f_4812_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4812_, 0, v_k_4805_);
v___x_4813_ = 1;
v___x_4814_ = 0;
v___x_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4815_, 0, v_maxFVars_4804_);
v___x_4816_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4803_, v___x_4813_, v___x_4814_, v___x_4813_, v___x_4814_, v___x_4815_, v___f_4812_, v_cleanupAnnotations_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec_ref_known(v___x_4815_, 1);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4816_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4816_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
v_a_4825_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4827_ = v___x_4816_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4816_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4833_, lean_object* v_maxFVars_4834_, lean_object* v_k_4835_, lean_object* v_cleanupAnnotations_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4842_; lean_object* v_res_4843_; 
v_cleanupAnnotations_boxed_4842_ = lean_unbox(v_cleanupAnnotations_4836_);
v_res_4843_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4833_, v_maxFVars_4834_, v_k_4835_, v_cleanupAnnotations_boxed_4842_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4844_, lean_object* v_e_4845_, lean_object* v_maxFVars_4846_, lean_object* v_k_4847_, uint8_t v_cleanupAnnotations_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v___x_4854_; 
v___x_4854_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4845_, v_maxFVars_4846_, v_k_4847_, v_cleanupAnnotations_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4855_, lean_object* v_e_4856_, lean_object* v_maxFVars_4857_, lean_object* v_k_4858_, lean_object* v_cleanupAnnotations_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4865_; lean_object* v_res_4866_; 
v_cleanupAnnotations_boxed_4865_ = lean_unbox(v_cleanupAnnotations_4859_);
v_res_4866_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4855_, v_e_4856_, v_maxFVars_4857_, v_k_4858_, v_cleanupAnnotations_boxed_4865_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
return v_res_4866_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4867_){
_start:
{
if (lean_obj_tag(v_x_4867_) == 0)
{
uint8_t v___x_4868_; 
v___x_4868_ = 1;
return v___x_4868_;
}
else
{
lean_object* v_head_4869_; 
v_head_4869_ = lean_ctor_get(v_x_4867_, 0);
if (lean_obj_tag(v_head_4869_) == 0)
{
lean_object* v_tail_4870_; 
v_tail_4870_ = lean_ctor_get(v_x_4867_, 1);
v_x_4867_ = v_tail_4870_;
goto _start;
}
else
{
uint8_t v___x_4872_; 
v___x_4872_ = 0;
return v___x_4872_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4873_){
_start:
{
uint8_t v_res_4874_; lean_object* v_r_4875_; 
v_res_4874_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4873_);
lean_dec(v_x_4873_);
v_r_4875_ = lean_box(v_res_4874_);
return v_r_4875_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4878_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4879_ = lean_unsigned_to_nat(12u);
v___x_4880_ = lean_unsigned_to_nat(376u);
v___x_4881_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4882_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4883_ = l_mkPanicMessageWithDecl(v___x_4882_, v___x_4881_, v___x_4880_, v___x_4879_, v___x_4878_);
return v___x_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4884_, lean_object* v_xs_4885_, lean_object* v_tail_4886_, lean_object* v___x_4887_, lean_object* v___x_4888_, lean_object* v_ys_4889_, lean_object* v_value_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
uint8_t v___x_1213__boxed_4896_; uint8_t v___x_1214__boxed_4897_; lean_object* v_res_4898_; 
v___x_1213__boxed_4896_ = lean_unbox(v___x_4887_);
v___x_1214__boxed_4897_ = lean_unbox(v___x_4888_);
v_res_4898_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4884_, v_xs_4885_, v_tail_4886_, v___x_1213__boxed_4896_, v___x_1214__boxed_4897_, v_ys_4889_, v_value_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec_ref(v_ys_4889_);
lean_dec(v___x_4884_);
return v_res_4898_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4899_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4900_ = lean_unsigned_to_nat(8u);
v___x_4901_ = lean_unsigned_to_nat(368u);
v___x_4902_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4904_ = l_mkPanicMessageWithDecl(v___x_4903_, v___x_4902_, v___x_4901_, v___x_4900_, v___x_4899_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4905_, lean_object* v_x_4906_, lean_object* v_x_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_){
_start:
{
if (lean_obj_tag(v_x_4906_) == 0)
{
lean_object* v___x_4913_; 
lean_dec_ref(v_xs_4905_);
v___x_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4913_, 0, v_x_4907_);
return v___x_4913_;
}
else
{
lean_object* v_head_4914_; 
v_head_4914_ = lean_ctor_get(v_x_4906_, 0);
if (lean_obj_tag(v_head_4914_) == 0)
{
lean_object* v_tail_4915_; uint8_t v___x_4916_; 
v_tail_4915_ = lean_ctor_get(v_x_4906_, 1);
lean_inc(v_tail_4915_);
lean_dec_ref_known(v_x_4906_, 2);
v___x_4916_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4915_);
if (v___x_4916_ == 0)
{
uint8_t v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___f_4921_; lean_object* v___x_4922_; 
v___x_4917_ = 1;
v___x_4918_ = lean_unsigned_to_nat(1u);
v___x_4919_ = lean_box(v___x_4916_);
v___x_4920_ = lean_box(v___x_4917_);
v___f_4921_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4921_, 0, v___x_4918_);
lean_closure_set(v___f_4921_, 1, v_xs_4905_);
lean_closure_set(v___f_4921_, 2, v_tail_4915_);
lean_closure_set(v___f_4921_, 3, v___x_4919_);
lean_closure_set(v___f_4921_, 4, v___x_4920_);
v___x_4922_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4907_, v___x_4918_, v___f_4921_, v___x_4916_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_);
return v___x_4922_;
}
else
{
lean_object* v___x_4923_; 
lean_dec(v_tail_4915_);
lean_dec_ref(v_xs_4905_);
v___x_4923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4923_, 0, v_x_4907_);
return v___x_4923_;
}
}
else
{
lean_object* v_tail_4924_; lean_object* v_val_4925_; lean_object* v___x_4926_; uint8_t v___x_4927_; 
lean_inc_ref(v_head_4914_);
v_tail_4924_ = lean_ctor_get(v_x_4906_, 1);
lean_inc(v_tail_4924_);
lean_dec_ref_known(v_x_4906_, 2);
v_val_4925_ = lean_ctor_get(v_head_4914_, 0);
lean_inc(v_val_4925_);
lean_dec_ref_known(v_head_4914_, 1);
v___x_4926_ = lean_array_get_size(v_xs_4905_);
v___x_4927_ = lean_nat_dec_lt(v_val_4925_, v___x_4926_);
if (v___x_4927_ == 0)
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
lean_dec(v_val_4925_);
lean_dec(v_tail_4924_);
lean_dec_ref(v_x_4907_);
lean_dec_ref(v_xs_4905_);
v___x_4928_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4929_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4928_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_);
return v___x_4929_;
}
else
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
v___x_4930_ = l_Lean_instInhabitedExpr;
v___x_4931_ = lean_array_get_borrowed(v___x_4930_, v_xs_4905_, v_val_4925_);
lean_dec(v_val_4925_);
v___x_4932_ = lean_unsigned_to_nat(1u);
v___x_4933_ = lean_mk_empty_array_with_capacity(v___x_4932_);
lean_inc(v___x_4931_);
v___x_4934_ = lean_array_push(v___x_4933_, v___x_4931_);
v___x_4935_ = l_Lean_Meta_instantiateLambda(v_x_4907_, v___x_4934_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_);
lean_dec_ref(v___x_4934_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v_a_4936_; 
v_a_4936_ = lean_ctor_get(v___x_4935_, 0);
lean_inc(v_a_4936_);
lean_dec_ref_known(v___x_4935_, 1);
v_x_4906_ = v_tail_4924_;
v_x_4907_ = v_a_4936_;
goto _start;
}
else
{
lean_dec(v_tail_4924_);
lean_dec_ref(v_xs_4905_);
return v___x_4935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4938_, lean_object* v_xs_4939_, lean_object* v_tail_4940_, uint8_t v___x_4941_, uint8_t v___x_4942_, lean_object* v_ys_4943_, lean_object* v_value_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
lean_object* v___x_4950_; uint8_t v___x_4951_; 
v___x_4950_ = lean_array_get_size(v_ys_4943_);
v___x_4951_ = lean_nat_dec_eq(v___x_4950_, v___x_4938_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_dec_ref(v_value_4944_);
lean_dec(v_tail_4940_);
lean_dec_ref(v_xs_4939_);
v___x_4952_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4953_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4952_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
return v___x_4953_;
}
else
{
lean_object* v___x_4954_; 
v___x_4954_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4939_, v_tail_4940_, v_value_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; uint8_t v___x_4956_; lean_object* v___x_4957_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref_known(v___x_4954_, 1);
v___x_4956_ = 1;
v___x_4957_ = l_Lean_Meta_mkLambdaFVars(v_ys_4943_, v_a_4955_, v___x_4941_, v___x_4942_, v___x_4941_, v___x_4942_, v___x_4956_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
return v___x_4957_;
}
else
{
return v___x_4954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4958_, lean_object* v_x_4959_, lean_object* v_x_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4958_, v_x_4959_, v_x_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_);
lean_dec(v_a_4964_);
lean_dec_ref(v_a_4963_);
lean_dec(v_a_4962_);
lean_dec_ref(v_a_4961_);
return v_res_4966_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4968_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4969_ = lean_unsigned_to_nat(2u);
v___x_4970_ = lean_unsigned_to_nat(362u);
v___x_4971_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_4972_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4973_ = l_mkPanicMessageWithDecl(v___x_4972_, v___x_4971_, v___x_4970_, v___x_4969_, v___x_4968_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_4974_, lean_object* v_value_u2080_4975_, lean_object* v_xs_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_){
_start:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; uint8_t v___x_4984_; 
v___x_4982_ = lean_array_get_size(v_xs_4976_);
v___x_4983_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4974_);
v___x_4984_ = lean_nat_dec_eq(v___x_4982_, v___x_4983_);
lean_dec(v___x_4983_);
if (v___x_4984_ == 0)
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
lean_dec_ref(v_xs_4976_);
lean_dec_ref(v_value_u2080_4975_);
lean_dec_ref(v_perm_4974_);
v___x_4985_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_4986_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4985_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_);
return v___x_4986_;
}
else
{
lean_object* v_mask_4987_; lean_object* v___x_4988_; 
v_mask_4987_ = lean_array_to_list(v_perm_4974_);
v___x_4988_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4976_, v_mask_4987_, v_value_u2080_4975_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_);
return v___x_4988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_4989_, lean_object* v_value_u2080_4990_, lean_object* v_xs_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_4989_, v_value_u2080_4990_, v_xs_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
lean_dec(v_a_4995_);
lean_dec_ref(v_a_4994_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
return v_res_4997_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_5005_; 
v___x_5005_ = l_Array_instInhabited(lean_box(0));
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5006_){
_start:
{
lean_object* v___f_5007_; lean_object* v___f_5008_; lean_object* v___f_5009_; lean_object* v___f_5010_; lean_object* v___f_5011_; lean_object* v___f_5012_; lean_object* v___f_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___f_5007_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5008_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5009_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5010_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5011_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5012_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5013_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5014_, 0, v___f_5007_);
lean_ctor_set(v___x_5014_, 1, v___f_5008_);
v___x_5015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5014_);
lean_ctor_set(v___x_5015_, 1, v___f_5009_);
lean_ctor_set(v___x_5015_, 2, v___f_5010_);
lean_ctor_set(v___x_5015_, 3, v___f_5011_);
lean_ctor_set(v___x_5015_, 4, v___f_5012_);
v___x_5016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5015_);
lean_ctor_set(v___x_5016_, 1, v___f_5013_);
v___x_5017_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5018_ = l_instInhabitedOfMonad___redArg(v___x_5016_, v___x_5017_);
v___x_5019_ = lean_panic_fn_borrowed(v___x_5018_, v_msg_5006_);
lean_dec(v___x_5018_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5020_, lean_object* v_msg_5021_){
_start:
{
lean_object* v___x_5022_; 
v___x_5022_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5021_);
return v___x_5022_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5025_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5026_ = lean_unsigned_to_nat(8u);
v___x_5027_ = lean_unsigned_to_nat(394u);
v___x_5028_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5029_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5030_ = l_mkPanicMessageWithDecl(v___x_5029_, v___x_5028_, v___x_5027_, v___x_5026_, v___x_5025_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5031_, lean_object* v_x_5032_){
_start:
{
if (lean_obj_tag(v_x_5031_) == 0)
{
return v_x_5032_;
}
else
{
lean_object* v_head_5033_; lean_object* v_fst_5034_; 
v_head_5033_ = lean_ctor_get(v_x_5031_, 0);
v_fst_5034_ = lean_ctor_get(v_head_5033_, 0);
if (lean_obj_tag(v_fst_5034_) == 0)
{
lean_object* v_tail_5035_; 
v_tail_5035_ = lean_ctor_get(v_x_5031_, 1);
lean_inc(v_tail_5035_);
lean_dec_ref_known(v_x_5031_, 2);
v_x_5031_ = v_tail_5035_;
goto _start;
}
else
{
lean_object* v_tail_5037_; lean_object* v_snd_5038_; lean_object* v_val_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; 
lean_inc_ref(v_fst_5034_);
lean_inc(v_head_5033_);
v_tail_5037_ = lean_ctor_get(v_x_5031_, 1);
lean_inc(v_tail_5037_);
lean_dec_ref_known(v_x_5031_, 2);
v_snd_5038_ = lean_ctor_get(v_head_5033_, 1);
lean_inc(v_snd_5038_);
lean_dec(v_head_5033_);
v_val_5039_ = lean_ctor_get(v_fst_5034_, 0);
lean_inc(v_val_5039_);
lean_dec_ref_known(v_fst_5034_, 1);
v___x_5040_ = lean_array_get_size(v_x_5032_);
v___x_5041_ = lean_nat_dec_lt(v_val_5039_, v___x_5040_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5042_; lean_object* v___x_5043_; 
lean_dec(v_val_5039_);
lean_dec(v_snd_5038_);
lean_dec(v_tail_5037_);
lean_dec_ref(v_x_5032_);
v___x_5042_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5043_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5042_);
return v___x_5043_;
}
else
{
lean_object* v___x_5044_; 
v___x_5044_ = lean_array_set(v_x_5032_, v_val_5039_, v_snd_5038_);
lean_dec(v_val_5039_);
v_x_5031_ = v_tail_5037_;
v_x_5032_ = v___x_5044_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5046_, lean_object* v_x_5047_, lean_object* v_x_5048_){
_start:
{
lean_object* v___x_5049_; 
v___x_5049_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5047_, v_x_5048_);
return v___x_5049_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5052_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5053_ = lean_unsigned_to_nat(2u);
v___x_5054_ = lean_unsigned_to_nat(384u);
v___x_5055_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5056_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5057_ = l_mkPanicMessageWithDecl(v___x_5056_, v___x_5055_, v___x_5054_, v___x_5053_, v___x_5052_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5060_, lean_object* v_xs_5061_){
_start:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; uint8_t v___x_5064_; 
v___x_5062_ = lean_array_get_size(v_xs_5061_);
v___x_5063_ = lean_array_get_size(v_perm_5060_);
v___x_5064_ = lean_nat_dec_eq(v___x_5062_, v___x_5063_);
if (v___x_5064_ == 0)
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5066_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5065_);
return v___x_5066_;
}
else
{
lean_object* v___x_5067_; uint8_t v___x_5068_; 
v___x_5067_ = lean_unsigned_to_nat(0u);
v___x_5068_ = lean_nat_dec_eq(v___x_5062_, v___x_5067_);
if (v___x_5068_ == 0)
{
lean_object* v_dummy_5069_; lean_object* v___x_5070_; lean_object* v_ys_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v_dummy_5069_ = lean_array_fget_borrowed(v_xs_5061_, v___x_5067_);
v___x_5070_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5060_);
lean_inc(v_dummy_5069_);
v_ys_5071_ = lean_mk_array(v___x_5070_, v_dummy_5069_);
v___x_5072_ = l_Array_zip___redArg(v_perm_5060_, v_xs_5061_);
v___x_5073_ = lean_array_to_list(v___x_5072_);
v___x_5074_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5073_, v_ys_5071_);
return v___x_5074_;
}
else
{
lean_object* v___x_5075_; 
v___x_5075_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5076_, lean_object* v_xs_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5076_, v_xs_5077_);
lean_dec_ref(v_xs_5077_);
lean_dec_ref(v_perm_5076_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5079_, lean_object* v_perm_5080_, lean_object* v_xs_5081_){
_start:
{
lean_object* v___x_5082_; 
v___x_5082_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5080_, v_xs_5081_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5083_, lean_object* v_perm_5084_, lean_object* v_xs_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5083_, v_perm_5084_, v_xs_5085_);
lean_dec_ref(v_xs_5085_);
lean_dec_ref(v_perm_5084_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5087_, lean_object* v_upperBound_5088_, lean_object* v_perm_5089_, lean_object* v_a_5090_, lean_object* v_b_5091_){
_start:
{
lean_object* v_a_5093_; uint8_t v___x_5100_; 
v___x_5100_ = lean_nat_dec_lt(v_a_5090_, v_upperBound_5088_);
if (v___x_5100_ == 0)
{
lean_dec(v_a_5090_);
return v_b_5091_;
}
else
{
lean_object* v___x_5101_; uint8_t v___x_5102_; 
v___x_5101_ = lean_array_get_size(v_perm_5089_);
v___x_5102_ = lean_nat_dec_lt(v_a_5090_, v___x_5101_);
if (v___x_5102_ == 0)
{
goto v___jp_5097_;
}
else
{
lean_object* v___x_5103_; 
v___x_5103_ = lean_array_fget_borrowed(v_perm_5089_, v_a_5090_);
if (lean_obj_tag(v___x_5103_) == 0)
{
goto v___jp_5097_;
}
else
{
v_a_5093_ = v_b_5091_;
goto v___jp_5092_;
}
}
}
v___jp_5092_:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; 
v___x_5094_ = lean_unsigned_to_nat(1u);
v___x_5095_ = lean_nat_add(v_a_5090_, v___x_5094_);
lean_dec(v_a_5090_);
v_a_5090_ = v___x_5095_;
v_b_5091_ = v_a_5093_;
goto _start;
}
v___jp_5097_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
v___x_5098_ = lean_array_fget_borrowed(v_xs_5087_, v_a_5090_);
lean_inc(v___x_5098_);
v___x_5099_ = lean_array_push(v_b_5091_, v___x_5098_);
v_a_5093_ = v___x_5099_;
goto v___jp_5092_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5104_, lean_object* v_upperBound_5105_, lean_object* v_perm_5106_, lean_object* v_a_5107_, lean_object* v_b_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5104_, v_upperBound_5105_, v_perm_5106_, v_a_5107_, v_b_5108_);
lean_dec_ref(v_perm_5106_);
lean_dec(v_upperBound_5105_);
lean_dec_ref(v_xs_5104_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5110_, lean_object* v_xs_5111_){
_start:
{
lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v_ys_5114_; lean_object* v___x_5115_; 
v___x_5112_ = lean_array_get_size(v_xs_5111_);
v___x_5113_ = lean_unsigned_to_nat(0u);
v_ys_5114_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5115_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5111_, v___x_5112_, v_perm_5110_, v___x_5113_, v_ys_5114_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5116_, lean_object* v_xs_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5116_, v_xs_5117_);
lean_dec_ref(v_xs_5117_);
lean_dec_ref(v_perm_5116_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5119_, lean_object* v_perm_5120_, lean_object* v_xs_5121_){
_start:
{
lean_object* v___x_5122_; 
v___x_5122_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5120_, v_xs_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5123_, lean_object* v_perm_5124_, lean_object* v_xs_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5123_, v_perm_5124_, v_xs_5125_);
lean_dec_ref(v_xs_5125_);
lean_dec_ref(v_perm_5124_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5127_, lean_object* v_xs_5128_, lean_object* v_upperBound_5129_, lean_object* v_perm_5130_, lean_object* v_inst_5131_, lean_object* v_R_5132_, lean_object* v_a_5133_, lean_object* v_b_5134_, lean_object* v_c_5135_){
_start:
{
lean_object* v___x_5136_; 
v___x_5136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5128_, v_upperBound_5129_, v_perm_5130_, v_a_5133_, v_b_5134_);
return v___x_5136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5137_, lean_object* v_xs_5138_, lean_object* v_upperBound_5139_, lean_object* v_perm_5140_, lean_object* v_inst_5141_, lean_object* v_R_5142_, lean_object* v_a_5143_, lean_object* v_b_5144_, lean_object* v_c_5145_){
_start:
{
lean_object* v_res_5146_; 
v_res_5146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5137_, v_xs_5138_, v_upperBound_5139_, v_perm_5140_, v_inst_5141_, v_R_5142_, v_a_5143_, v_b_5144_, v_c_5145_);
lean_dec_ref(v_perm_5140_);
lean_dec(v_upperBound_5139_);
lean_dec_ref(v_xs_5138_);
return v_res_5146_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5147_){
_start:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5148_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7, &l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__7);
v___x_5149_ = lean_panic_fn_borrowed(v___x_5148_, v_msg_5147_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5150_, lean_object* v_msg_5151_){
_start:
{
lean_object* v___x_5152_; 
v___x_5152_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5151_);
return v___x_5152_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5153_, lean_object* v___x_5154_, lean_object* v_i_5155_, lean_object* v___x_5156_, lean_object* v_as_5157_, size_t v_i_5158_, size_t v_stop_5159_){
_start:
{
uint8_t v___x_5160_; 
v___x_5160_ = lean_usize_dec_eq(v_i_5158_, v_stop_5159_);
if (v___x_5160_ == 0)
{
uint8_t v___x_5161_; uint8_t v___y_5163_; lean_object* v___x_5167_; 
v___x_5161_ = 1;
v___x_5167_ = lean_array_uget_borrowed(v_as_5157_, v_i_5158_);
if (lean_obj_tag(v___x_5167_) == 0)
{
uint8_t v___x_5168_; 
v___x_5168_ = lean_nat_dec_lt(v_j_5153_, v___x_5154_);
v___y_5163_ = v___x_5168_;
goto v___jp_5162_;
}
else
{
uint8_t v___x_5169_; 
v___x_5169_ = lean_nat_dec_lt(v_i_5155_, v___x_5156_);
v___y_5163_ = v___x_5169_;
goto v___jp_5162_;
}
v___jp_5162_:
{
if (v___y_5163_ == 0)
{
size_t v___x_5164_; size_t v___x_5165_; 
v___x_5164_ = ((size_t)1ULL);
v___x_5165_ = lean_usize_add(v_i_5158_, v___x_5164_);
v_i_5158_ = v___x_5165_;
goto _start;
}
else
{
return v___x_5161_;
}
}
}
else
{
uint8_t v___x_5170_; 
v___x_5170_ = 0;
return v___x_5170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5171_, lean_object* v___x_5172_, lean_object* v_i_5173_, lean_object* v___x_5174_, lean_object* v_as_5175_, lean_object* v_i_5176_, lean_object* v_stop_5177_){
_start:
{
size_t v_i_boxed_5178_; size_t v_stop_boxed_5179_; uint8_t v_res_5180_; lean_object* v_r_5181_; 
v_i_boxed_5178_ = lean_unbox_usize(v_i_5176_);
lean_dec(v_i_5176_);
v_stop_boxed_5179_ = lean_unbox_usize(v_stop_5177_);
lean_dec(v_stop_5177_);
v_res_5180_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5171_, v___x_5172_, v_i_5173_, v___x_5174_, v_as_5175_, v_i_boxed_5178_, v_stop_boxed_5179_);
lean_dec_ref(v_as_5175_);
lean_dec(v___x_5174_);
lean_dec(v_i_5173_);
lean_dec(v___x_5172_);
lean_dec(v_j_5171_);
v_r_5181_ = lean_box(v_res_5180_);
return v_r_5181_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; 
v___x_5184_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5185_ = lean_unsigned_to_nat(10u);
v___x_5186_ = lean_unsigned_to_nat(425u);
v___x_5187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5188_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5189_ = l_mkPanicMessageWithDecl(v___x_5188_, v___x_5187_, v___x_5186_, v___x_5185_, v___x_5184_);
return v___x_5189_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5191_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5192_ = lean_unsigned_to_nat(12u);
v___x_5193_ = lean_unsigned_to_nat(433u);
v___x_5194_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5195_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5196_ = l_mkPanicMessageWithDecl(v___x_5195_, v___x_5194_, v___x_5193_, v___x_5192_, v___x_5191_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5197_, lean_object* v_fixedArgs_5198_, lean_object* v_varyingArgs_5199_, lean_object* v_i_5200_, lean_object* v_j_5201_, lean_object* v_xs_5202_){
_start:
{
lean_object* v_lower_5204_; lean_object* v_upper_5205_; lean_object* v___x_5209_; uint8_t v___x_5210_; 
v___x_5209_ = lean_array_get_size(v_perm_5197_);
v___x_5210_ = lean_nat_dec_lt(v_i_5200_, v___x_5209_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; lean_object* v___x_5212_; uint8_t v___x_5213_; 
lean_dec(v_i_5200_);
lean_dec_ref(v_perm_5197_);
v___x_5211_ = lean_unsigned_to_nat(0u);
v___x_5212_ = lean_array_get_size(v_varyingArgs_5199_);
v___x_5213_ = lean_nat_dec_le(v_j_5201_, v___x_5211_);
if (v___x_5213_ == 0)
{
v_lower_5204_ = v_j_5201_;
v_upper_5205_ = v___x_5212_;
goto v___jp_5203_;
}
else
{
lean_dec(v_j_5201_);
v_lower_5204_ = v___x_5211_;
v_upper_5205_ = v___x_5212_;
goto v___jp_5203_;
}
}
else
{
lean_object* v___x_5214_; 
v___x_5214_ = lean_array_fget_borrowed(v_perm_5197_, v_i_5200_);
if (lean_obj_tag(v___x_5214_) == 1)
{
lean_object* v_val_5215_; lean_object* v___x_5216_; uint8_t v___x_5217_; 
v_val_5215_ = lean_ctor_get(v___x_5214_, 0);
v___x_5216_ = lean_array_get_size(v_fixedArgs_5198_);
v___x_5217_ = lean_nat_dec_lt(v_val_5215_, v___x_5216_);
if (v___x_5217_ == 0)
{
lean_object* v___x_5218_; lean_object* v___x_5219_; 
lean_dec_ref(v_xs_5202_);
lean_dec(v_j_5201_);
lean_dec(v_i_5200_);
lean_dec_ref(v_varyingArgs_5199_);
lean_dec_ref(v_perm_5197_);
v___x_5218_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5219_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5218_);
return v___x_5219_;
}
else
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; 
v___x_5220_ = lean_unsigned_to_nat(1u);
v___x_5221_ = lean_nat_add(v_i_5200_, v___x_5220_);
lean_dec(v_i_5200_);
v___x_5222_ = lean_array_fget_borrowed(v_fixedArgs_5198_, v_val_5215_);
lean_inc(v___x_5222_);
v___x_5223_ = lean_array_push(v_xs_5202_, v___x_5222_);
v_i_5200_ = v___x_5221_;
v_xs_5202_ = v___x_5223_;
goto _start;
}
}
else
{
lean_object* v___x_5225_; lean_object* v___y_5227_; lean_object* v___y_5228_; lean_object* v___y_5229_; lean_object* v_lower_5237_; lean_object* v_upper_5238_; uint8_t v___x_5246_; 
v___x_5225_ = lean_array_get_size(v_varyingArgs_5199_);
v___x_5246_ = lean_nat_dec_lt(v_j_5201_, v___x_5225_);
if (v___x_5246_ == 0)
{
lean_object* v___x_5247_; uint8_t v___x_5248_; 
lean_dec_ref(v_varyingArgs_5199_);
v___x_5247_ = lean_unsigned_to_nat(0u);
v___x_5248_ = lean_nat_dec_le(v_i_5200_, v___x_5247_);
if (v___x_5248_ == 0)
{
lean_inc(v_i_5200_);
v_lower_5237_ = v_i_5200_;
v_upper_5238_ = v___x_5209_;
goto v___jp_5236_;
}
else
{
v_lower_5237_ = v___x_5247_;
v_upper_5238_ = v___x_5209_;
goto v___jp_5236_;
}
}
else
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; 
v___x_5249_ = lean_unsigned_to_nat(1u);
v___x_5250_ = lean_nat_add(v_i_5200_, v___x_5249_);
lean_dec(v_i_5200_);
v___x_5251_ = lean_nat_add(v_j_5201_, v___x_5249_);
v___x_5252_ = lean_array_fget_borrowed(v_varyingArgs_5199_, v_j_5201_);
lean_dec(v_j_5201_);
lean_inc(v___x_5252_);
v___x_5253_ = lean_array_push(v_xs_5202_, v___x_5252_);
v_i_5200_ = v___x_5250_;
v_j_5201_ = v___x_5251_;
v_xs_5202_ = v___x_5253_;
goto _start;
}
v___jp_5226_:
{
uint8_t v___x_5230_; 
v___x_5230_ = lean_nat_dec_lt(v___y_5228_, v___y_5229_);
if (v___x_5230_ == 0)
{
lean_dec(v___y_5229_);
lean_dec(v___y_5228_);
lean_dec_ref(v___y_5227_);
lean_dec(v_j_5201_);
lean_dec(v_i_5200_);
return v_xs_5202_;
}
else
{
size_t v___x_5231_; size_t v___x_5232_; uint8_t v___x_5233_; 
v___x_5231_ = lean_usize_of_nat(v___y_5228_);
lean_dec(v___y_5228_);
v___x_5232_ = lean_usize_of_nat(v___y_5229_);
lean_dec(v___y_5229_);
v___x_5233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5201_, v___x_5225_, v_i_5200_, v___x_5209_, v___y_5227_, v___x_5231_, v___x_5232_);
lean_dec_ref(v___y_5227_);
lean_dec(v_i_5200_);
lean_dec(v_j_5201_);
if (v___x_5233_ == 0)
{
return v_xs_5202_;
}
else
{
lean_object* v___x_5234_; lean_object* v___x_5235_; 
lean_dec_ref(v_xs_5202_);
v___x_5234_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5235_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5234_);
return v___x_5235_;
}
}
}
v___jp_5236_:
{
lean_object* v___x_5239_; lean_object* v_array_5240_; lean_object* v_start_5241_; lean_object* v_stop_5242_; uint8_t v___x_5243_; 
v___x_5239_ = l_Array_toSubarray___redArg(v_perm_5197_, v_lower_5237_, v_upper_5238_);
v_array_5240_ = lean_ctor_get(v___x_5239_, 0);
lean_inc_ref(v_array_5240_);
v_start_5241_ = lean_ctor_get(v___x_5239_, 1);
lean_inc(v_start_5241_);
v_stop_5242_ = lean_ctor_get(v___x_5239_, 2);
lean_inc(v_stop_5242_);
lean_dec_ref(v___x_5239_);
v___x_5243_ = lean_nat_dec_lt(v_start_5241_, v_stop_5242_);
if (v___x_5243_ == 0)
{
lean_dec(v_stop_5242_);
lean_dec(v_start_5241_);
lean_dec_ref(v_array_5240_);
lean_dec(v_j_5201_);
lean_dec(v_i_5200_);
return v_xs_5202_;
}
else
{
lean_object* v___x_5244_; uint8_t v___x_5245_; 
v___x_5244_ = lean_array_get_size(v_array_5240_);
v___x_5245_ = lean_nat_dec_le(v_stop_5242_, v___x_5244_);
if (v___x_5245_ == 0)
{
lean_dec(v_stop_5242_);
v___y_5227_ = v_array_5240_;
v___y_5228_ = v_start_5241_;
v___y_5229_ = v___x_5244_;
goto v___jp_5226_;
}
else
{
v___y_5227_ = v_array_5240_;
v___y_5228_ = v_start_5241_;
v___y_5229_ = v_stop_5242_;
goto v___jp_5226_;
}
}
}
}
}
v___jp_5203_:
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; 
v___x_5206_ = l_Array_toSubarray___redArg(v_varyingArgs_5199_, v_lower_5204_, v_upper_5205_);
v___x_5207_ = l_Subarray_copy___redArg(v___x_5206_);
v___x_5208_ = l_Array_append___redArg(v_xs_5202_, v___x_5207_);
lean_dec_ref(v___x_5207_);
return v___x_5208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5255_, lean_object* v_fixedArgs_5256_, lean_object* v_varyingArgs_5257_, lean_object* v_i_5258_, lean_object* v_j_5259_, lean_object* v_xs_5260_){
_start:
{
lean_object* v_res_5261_; 
v_res_5261_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5255_, v_fixedArgs_5256_, v_varyingArgs_5257_, v_i_5258_, v_j_5259_, v_xs_5260_);
lean_dec_ref(v_fixedArgs_5256_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5262_, lean_object* v_perm_5263_, lean_object* v_fixedArgs_5264_, lean_object* v_varyingArgs_5265_, lean_object* v_i_5266_, lean_object* v_j_5267_, lean_object* v_xs_5268_){
_start:
{
lean_object* v___x_5269_; 
v___x_5269_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5263_, v_fixedArgs_5264_, v_varyingArgs_5265_, v_i_5266_, v_j_5267_, v_xs_5268_);
return v___x_5269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5270_, lean_object* v_perm_5271_, lean_object* v_fixedArgs_5272_, lean_object* v_varyingArgs_5273_, lean_object* v_i_5274_, lean_object* v_j_5275_, lean_object* v_xs_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5270_, v_perm_5271_, v_fixedArgs_5272_, v_varyingArgs_5273_, v_i_5274_, v_j_5275_, v_xs_5276_);
lean_dec_ref(v_fixedArgs_5272_);
return v_res_5277_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; 
v___x_5280_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5281_ = lean_unsigned_to_nat(2u);
v___x_5282_ = lean_unsigned_to_nat(416u);
v___x_5283_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5285_ = l_mkPanicMessageWithDecl(v___x_5284_, v___x_5283_, v___x_5282_, v___x_5281_, v___x_5280_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5286_, lean_object* v_fixedArgs_5287_, lean_object* v_varyingArgs_5288_){
_start:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; uint8_t v___x_5291_; 
v___x_5289_ = lean_array_get_size(v_fixedArgs_5287_);
v___x_5290_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5286_);
v___x_5291_ = lean_nat_dec_eq(v___x_5289_, v___x_5290_);
lean_dec(v___x_5290_);
if (v___x_5291_ == 0)
{
lean_object* v___x_5292_; lean_object* v___x_5293_; 
lean_dec_ref(v_varyingArgs_5288_);
lean_dec_ref(v_perm_5286_);
v___x_5292_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5293_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5292_);
return v___x_5293_;
}
else
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5294_ = lean_unsigned_to_nat(0u);
v___x_5295_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5296_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5286_, v_fixedArgs_5287_, v_varyingArgs_5288_, v___x_5294_, v___x_5294_, v___x_5295_);
return v___x_5296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5297_, lean_object* v_fixedArgs_5298_, lean_object* v_varyingArgs_5299_){
_start:
{
lean_object* v_res_5300_; 
v_res_5300_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5297_, v_fixedArgs_5298_, v_varyingArgs_5299_);
lean_dec_ref(v_fixedArgs_5298_);
return v_res_5300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5301_, lean_object* v_perm_5302_, lean_object* v_fixedArgs_5303_, lean_object* v_varyingArgs_5304_){
_start:
{
lean_object* v___x_5305_; 
v___x_5305_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5302_, v_fixedArgs_5303_, v_varyingArgs_5304_);
return v___x_5305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5306_, lean_object* v_perm_5307_, lean_object* v_fixedArgs_5308_, lean_object* v_varyingArgs_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5306_, v_perm_5307_, v_fixedArgs_5308_, v_varyingArgs_5309_);
lean_dec_ref(v_fixedArgs_5308_);
return v_res_5310_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5311_, lean_object* v_x_5312_){
_start:
{
if (lean_obj_tag(v_x_5311_) == 0)
{
if (lean_obj_tag(v_x_5312_) == 0)
{
uint8_t v___x_5313_; 
v___x_5313_ = 1;
return v___x_5313_;
}
else
{
uint8_t v___x_5314_; 
v___x_5314_ = 0;
return v___x_5314_;
}
}
else
{
if (lean_obj_tag(v_x_5312_) == 0)
{
uint8_t v___x_5315_; 
v___x_5315_ = 0;
return v___x_5315_;
}
else
{
lean_object* v_val_5316_; lean_object* v_val_5317_; uint8_t v___x_5318_; 
v_val_5316_ = lean_ctor_get(v_x_5311_, 0);
v_val_5317_ = lean_ctor_get(v_x_5312_, 0);
v___x_5318_ = lean_nat_dec_eq(v_val_5316_, v_val_5317_);
return v___x_5318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5319_, lean_object* v_x_5320_){
_start:
{
uint8_t v_res_5321_; lean_object* v_r_5322_; 
v_res_5321_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5319_, v_x_5320_);
lean_dec(v_x_5320_);
lean_dec(v_x_5319_);
v_r_5322_ = lean_box(v_res_5321_);
return v_r_5322_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5323_, lean_object* v_ys_5324_, lean_object* v_x_5325_){
_start:
{
lean_object* v_zero_5326_; uint8_t v_isZero_5327_; 
v_zero_5326_ = lean_unsigned_to_nat(0u);
v_isZero_5327_ = lean_nat_dec_eq(v_x_5325_, v_zero_5326_);
if (v_isZero_5327_ == 1)
{
lean_dec(v_x_5325_);
return v_isZero_5327_;
}
else
{
lean_object* v_one_5328_; lean_object* v_n_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; uint8_t v___x_5332_; 
v_one_5328_ = lean_unsigned_to_nat(1u);
v_n_5329_ = lean_nat_sub(v_x_5325_, v_one_5328_);
lean_dec(v_x_5325_);
v___x_5330_ = lean_array_fget_borrowed(v_xs_5323_, v_n_5329_);
v___x_5331_ = lean_array_fget_borrowed(v_ys_5324_, v_n_5329_);
v___x_5332_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5330_, v___x_5331_);
if (v___x_5332_ == 0)
{
lean_dec(v_n_5329_);
return v___x_5332_;
}
else
{
v_x_5325_ = v_n_5329_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5334_, lean_object* v_ys_5335_, lean_object* v_x_5336_){
_start:
{
uint8_t v_res_5337_; lean_object* v_r_5338_; 
v_res_5337_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5334_, v_ys_5335_, v_x_5336_);
lean_dec_ref(v_ys_5335_);
lean_dec_ref(v_xs_5334_);
v_r_5338_ = lean_box(v_res_5337_);
return v_r_5338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5339_, size_t v_i_5340_, lean_object* v_bs_5341_){
_start:
{
uint8_t v___x_5342_; 
v___x_5342_ = lean_usize_dec_lt(v_i_5340_, v_sz_5339_);
if (v___x_5342_ == 0)
{
return v_bs_5341_;
}
else
{
lean_object* v_v_5343_; lean_object* v___x_5344_; lean_object* v_bs_x27_5345_; lean_object* v___x_5346_; size_t v___x_5347_; size_t v___x_5348_; lean_object* v___x_5349_; 
v_v_5343_ = lean_array_uget(v_bs_5341_, v_i_5340_);
v___x_5344_ = lean_unsigned_to_nat(0u);
v_bs_x27_5345_ = lean_array_uset(v_bs_5341_, v_i_5340_, v___x_5344_);
v___x_5346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5346_, 0, v_v_5343_);
v___x_5347_ = ((size_t)1ULL);
v___x_5348_ = lean_usize_add(v_i_5340_, v___x_5347_);
v___x_5349_ = lean_array_uset(v_bs_x27_5345_, v_i_5340_, v___x_5346_);
v_i_5340_ = v___x_5348_;
v_bs_5341_ = v___x_5349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5351_, lean_object* v_i_5352_, lean_object* v_bs_5353_){
_start:
{
size_t v_sz_boxed_5354_; size_t v_i_boxed_5355_; lean_object* v_res_5356_; 
v_sz_boxed_5354_ = lean_unbox_usize(v_sz_5351_);
lean_dec(v_sz_5351_);
v_i_boxed_5355_ = lean_unbox_usize(v_i_5352_);
lean_dec(v_i_5352_);
v_res_5356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5354_, v_i_boxed_5355_, v_bs_5353_);
return v_res_5356_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5357_, lean_object* v_as_5358_, size_t v_i_5359_, size_t v_stop_5360_){
_start:
{
uint8_t v___x_5361_; 
v___x_5361_ = lean_usize_dec_eq(v_i_5359_, v_stop_5360_);
if (v___x_5361_ == 0)
{
lean_object* v_numFixed_5362_; uint8_t v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; size_t v_sz_5366_; size_t v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; uint8_t v___x_5375_; 
v_numFixed_5362_ = lean_ctor_get(v_fixedParamPerms_5357_, 0);
v___x_5363_ = 1;
v___x_5364_ = lean_array_uget_borrowed(v_as_5358_, v_i_5359_);
lean_inc(v_numFixed_5362_);
v___x_5365_ = l_Array_range(v_numFixed_5362_);
v_sz_5366_ = lean_array_size(v___x_5365_);
v___x_5367_ = ((size_t)0ULL);
v___x_5368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5366_, v___x_5367_, v___x_5365_);
v___x_5369_ = lean_array_get_size(v___x_5364_);
v___x_5370_ = lean_nat_sub(v___x_5369_, v_numFixed_5362_);
v___x_5371_ = lean_box(0);
v___x_5372_ = lean_mk_array(v___x_5370_, v___x_5371_);
v___x_5373_ = l_Array_append___redArg(v___x_5368_, v___x_5372_);
lean_dec_ref(v___x_5372_);
v___x_5374_ = lean_array_get_size(v___x_5373_);
v___x_5375_ = lean_nat_dec_eq(v___x_5369_, v___x_5374_);
if (v___x_5375_ == 0)
{
lean_dec_ref(v___x_5373_);
lean_dec_ref(v_fixedParamPerms_5357_);
return v___x_5363_;
}
else
{
uint8_t v___x_5376_; 
v___x_5376_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5364_, v___x_5373_, v___x_5369_);
lean_dec_ref(v___x_5373_);
if (v___x_5376_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5357_);
return v___x_5363_;
}
else
{
size_t v___x_5377_; size_t v___x_5378_; 
v___x_5377_ = ((size_t)1ULL);
v___x_5378_ = lean_usize_add(v_i_5359_, v___x_5377_);
v_i_5359_ = v___x_5378_;
goto _start;
}
}
}
else
{
uint8_t v___x_5380_; 
lean_dec_ref(v_fixedParamPerms_5357_);
v___x_5380_ = 0;
return v___x_5380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5381_, lean_object* v_as_5382_, lean_object* v_i_5383_, lean_object* v_stop_5384_){
_start:
{
size_t v_i_boxed_5385_; size_t v_stop_boxed_5386_; uint8_t v_res_5387_; lean_object* v_r_5388_; 
v_i_boxed_5385_ = lean_unbox_usize(v_i_5383_);
lean_dec(v_i_5383_);
v_stop_boxed_5386_ = lean_unbox_usize(v_stop_5384_);
lean_dec(v_stop_5384_);
v_res_5387_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5381_, v_as_5382_, v_i_boxed_5385_, v_stop_boxed_5386_);
lean_dec_ref(v_as_5382_);
v_r_5388_ = lean_box(v_res_5387_);
return v_r_5388_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5389_){
_start:
{
lean_object* v_perms_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; uint8_t v___x_5393_; 
v_perms_5390_ = lean_ctor_get(v_fixedParamPerms_5389_, 1);
lean_inc_ref(v_perms_5390_);
v___x_5391_ = lean_unsigned_to_nat(0u);
v___x_5392_ = lean_array_get_size(v_perms_5390_);
v___x_5393_ = lean_nat_dec_lt(v___x_5391_, v___x_5392_);
if (v___x_5393_ == 0)
{
uint8_t v___x_5394_; 
lean_dec_ref(v_perms_5390_);
lean_dec_ref(v_fixedParamPerms_5389_);
v___x_5394_ = 1;
return v___x_5394_;
}
else
{
if (v___x_5393_ == 0)
{
lean_dec_ref(v_perms_5390_);
lean_dec_ref(v_fixedParamPerms_5389_);
return v___x_5393_;
}
else
{
size_t v___x_5395_; size_t v___x_5396_; uint8_t v___x_5397_; 
v___x_5395_ = ((size_t)0ULL);
v___x_5396_ = lean_usize_of_nat(v___x_5392_);
v___x_5397_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5389_, v_perms_5390_, v___x_5395_, v___x_5396_);
lean_dec_ref(v_perms_5390_);
if (v___x_5397_ == 0)
{
return v___x_5393_;
}
else
{
uint8_t v___x_5398_; 
v___x_5398_ = 0;
return v___x_5398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5399_){
_start:
{
uint8_t v_res_5400_; lean_object* v_r_5401_; 
v_res_5400_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5399_);
v_r_5401_ = lean_box(v_res_5400_);
return v_r_5401_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5402_, lean_object* v_ys_5403_, lean_object* v_hsz_5404_, lean_object* v_x_5405_, lean_object* v_x_5406_){
_start:
{
uint8_t v___x_5407_; 
v___x_5407_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5402_, v_ys_5403_, v_x_5405_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5408_, lean_object* v_ys_5409_, lean_object* v_hsz_5410_, lean_object* v_x_5411_, lean_object* v_x_5412_){
_start:
{
uint8_t v_res_5413_; lean_object* v_r_5414_; 
v_res_5413_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5408_, v_ys_5409_, v_hsz_5410_, v_x_5411_, v_x_5412_);
lean_dec_ref(v_ys_5409_);
lean_dec_ref(v_xs_5408_);
v_r_5414_ = lean_box(v_res_5413_);
return v_r_5414_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5415_; 
v___x_5415_ = l_Array_instInhabited(lean_box(0));
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5416_){
_start:
{
lean_object* v___f_5417_; lean_object* v___f_5418_; lean_object* v___f_5419_; lean_object* v___f_5420_; lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___f_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; 
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
v___x_5427_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5428_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5428_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___x_5430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5430_, 0, v___x_5427_);
lean_ctor_set(v___x_5430_, 1, v___x_5429_);
v___x_5431_ = l_instInhabitedOfMonad___redArg(v___x_5426_, v___x_5430_);
v___x_5432_ = lean_panic_fn_borrowed(v___x_5431_, v_msg_5416_);
lean_dec(v___x_5431_);
return v___x_5432_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5433_; 
v___x_5433_ = l_Array_instInhabited(lean_box(0));
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5434_){
_start:
{
lean_object* v___f_5435_; lean_object* v___f_5436_; lean_object* v___f_5437_; lean_object* v___f_5438_; lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___f_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___f_5435_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5436_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5437_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5438_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5439_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5440_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5441_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5442_, 0, v___f_5435_);
lean_ctor_set(v___x_5442_, 1, v___f_5436_);
v___x_5443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5442_);
lean_ctor_set(v___x_5443_, 1, v___f_5437_);
lean_ctor_set(v___x_5443_, 2, v___f_5438_);
lean_ctor_set(v___x_5443_, 3, v___f_5439_);
lean_ctor_set(v___x_5443_, 4, v___f_5440_);
v___x_5444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5443_);
lean_ctor_set(v___x_5444_, 1, v___f_5441_);
v___x_5445_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5446_, 0, v___x_5445_);
v___x_5447_ = l_instInhabitedOfMonad___redArg(v___x_5444_, v___x_5446_);
v___x_5448_ = lean_panic_fn_borrowed(v___x_5447_, v_msg_5434_);
lean_dec(v___x_5447_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5449_, uint8_t v___x_5450_, lean_object* v___x_5451_, lean_object* v___x_5452_, lean_object* v_as_5453_, size_t v_sz_5454_, size_t v_i_5455_, lean_object* v_b_5456_){
_start:
{
lean_object* v_a_5458_; uint8_t v___x_5462_; 
v___x_5462_ = lean_usize_dec_lt(v_i_5455_, v_sz_5454_);
if (v___x_5462_ == 0)
{
return v_b_5456_;
}
else
{
lean_object* v_fst_5463_; lean_object* v_snd_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5486_; 
v_fst_5463_ = lean_ctor_get(v_b_5456_, 0);
v_snd_5464_ = lean_ctor_get(v_b_5456_, 1);
v_isSharedCheck_5486_ = !lean_is_exclusive(v_b_5456_);
if (v_isSharedCheck_5486_ == 0)
{
v___x_5466_ = v_b_5456_;
v_isShared_5467_ = v_isSharedCheck_5486_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_snd_5464_);
lean_inc(v_fst_5463_);
lean_dec(v_b_5456_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5486_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5472_; lean_object* v_a_5473_; lean_object* v___x_5474_; 
v___x_5472_ = lean_box(0);
v_a_5473_ = lean_array_uget_borrowed(v_as_5453_, v_i_5455_);
v___x_5474_ = lean_array_get_borrowed(v___x_5472_, v___x_5449_, v_a_5473_);
if (lean_obj_tag(v___x_5474_) == 1)
{
lean_object* v_val_5475_; uint8_t v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; uint8_t v___x_5479_; 
v_val_5475_ = lean_ctor_get(v___x_5474_, 0);
v___x_5476_ = 0;
v___x_5477_ = lean_box(v___x_5476_);
v___x_5478_ = lean_array_get(v___x_5477_, v_fst_5463_, v_val_5475_);
lean_dec(v___x_5477_);
v___x_5479_ = lean_unbox(v___x_5478_);
lean_dec(v___x_5478_);
if (v___x_5479_ == 0)
{
if (v___x_5450_ == 0)
{
goto v___jp_5468_;
}
else
{
uint8_t v_changed_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; 
lean_del_object(v___x_5466_);
lean_dec(v_snd_5464_);
v_changed_5480_ = lean_nat_dec_eq(v___x_5451_, v___x_5452_);
v___x_5481_ = lean_box(v_changed_5480_);
v___x_5482_ = lean_array_set(v_fst_5463_, v_val_5475_, v___x_5481_);
v___x_5483_ = lean_box(v_changed_5480_);
v___x_5484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5482_);
lean_ctor_set(v___x_5484_, 1, v___x_5483_);
v_a_5458_ = v___x_5484_;
goto v___jp_5457_;
}
}
else
{
goto v___jp_5468_;
}
}
else
{
lean_object* v___x_5485_; 
lean_del_object(v___x_5466_);
v___x_5485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5485_, 0, v_fst_5463_);
lean_ctor_set(v___x_5485_, 1, v_snd_5464_);
v_a_5458_ = v___x_5485_;
goto v___jp_5457_;
}
v___jp_5468_:
{
lean_object* v___x_5470_; 
if (v_isShared_5467_ == 0)
{
v___x_5470_ = v___x_5466_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_fst_5463_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v_snd_5464_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
v_a_5458_ = v___x_5470_;
goto v___jp_5457_;
}
}
}
}
v___jp_5457_:
{
size_t v___x_5459_; size_t v___x_5460_; 
v___x_5459_ = ((size_t)1ULL);
v___x_5460_ = lean_usize_add(v_i_5455_, v___x_5459_);
v_i_5455_ = v___x_5460_;
v_b_5456_ = v_a_5458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5487_, lean_object* v___x_5488_, lean_object* v___x_5489_, lean_object* v___x_5490_, lean_object* v_as_5491_, lean_object* v_sz_5492_, lean_object* v_i_5493_, lean_object* v_b_5494_){
_start:
{
uint8_t v___x_6987__boxed_5495_; size_t v_sz_boxed_5496_; size_t v_i_boxed_5497_; lean_object* v_res_5498_; 
v___x_6987__boxed_5495_ = lean_unbox(v___x_5488_);
v_sz_boxed_5496_ = lean_unbox_usize(v_sz_5492_);
lean_dec(v_sz_5492_);
v_i_boxed_5497_ = lean_unbox_usize(v_i_5493_);
lean_dec(v_i_5493_);
v_res_5498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5487_, v___x_6987__boxed_5495_, v___x_5489_, v___x_5490_, v_as_5491_, v_sz_boxed_5496_, v_i_boxed_5497_, v_b_5494_);
lean_dec_ref(v_as_5491_);
lean_dec(v___x_5490_);
lean_dec(v___x_5489_);
lean_dec_ref(v___x_5487_);
return v_res_5498_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_5499_; 
v___x_5499_ = l_Array_instInhabited(lean_box(0));
return v___x_5499_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object* v_upperBound_5500_, lean_object* v___x_5501_, lean_object* v_fixedParamPerms_5502_, lean_object* v_next_5503_, lean_object* v___x_5504_, lean_object* v___x_5505_, lean_object* v_a_5506_, lean_object* v_b_5507_){
_start:
{
lean_object* v_a_5509_; uint8_t v___x_5513_; 
v___x_5513_ = lean_nat_dec_lt(v_a_5506_, v_upperBound_5500_);
if (v___x_5513_ == 0)
{
lean_dec(v_a_5506_);
return v_b_5507_;
}
else
{
lean_object* v_fst_5514_; lean_object* v_snd_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5551_; 
v_fst_5514_ = lean_ctor_get(v_b_5507_, 0);
v_snd_5515_ = lean_ctor_get(v_b_5507_, 1);
v_isSharedCheck_5551_ = !lean_is_exclusive(v_b_5507_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5517_ = v_b_5507_;
v_isShared_5518_ = v_isSharedCheck_5551_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_snd_5515_);
lean_inc(v_fst_5514_);
lean_dec(v_b_5507_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5551_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5519_; 
v___x_5519_ = lean_array_fget_borrowed(v___x_5501_, v_a_5506_);
if (lean_obj_tag(v___x_5519_) == 1)
{
lean_object* v_val_5520_; uint8_t v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; uint8_t v___x_5524_; 
v_val_5520_ = lean_ctor_get(v___x_5519_, 0);
v___x_5521_ = 0;
v___x_5522_ = lean_box(v___x_5521_);
v___x_5523_ = lean_array_get(v___x_5522_, v_fst_5514_, v_val_5520_);
lean_dec(v___x_5522_);
v___x_5524_ = lean_unbox(v___x_5523_);
if (v___x_5524_ == 0)
{
lean_object* v___x_5526_; 
lean_dec(v___x_5523_);
if (v_isShared_5518_ == 0)
{
v___x_5526_ = v___x_5517_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_fst_5514_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v_snd_5515_);
v___x_5526_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
v_a_5509_ = v___x_5526_;
goto v___jp_5508_;
}
}
else
{
lean_object* v_revDeps_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5533_; 
v_revDeps_5528_ = lean_ctor_get(v_fixedParamPerms_5502_, 2);
v___x_5529_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0);
v___x_5530_ = lean_array_get_borrowed(v___x_5529_, v_revDeps_5528_, v_next_5503_);
v___x_5531_ = lean_array_get_borrowed(v___x_5529_, v___x_5530_, v_a_5506_);
if (v_isShared_5518_ == 0)
{
v___x_5533_ = v___x_5517_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_fst_5514_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_snd_5515_);
v___x_5533_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
size_t v_sz_5534_; size_t v___x_5535_; uint8_t v___x_5536_; lean_object* v___x_5537_; lean_object* v_fst_5538_; lean_object* v_snd_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
v_sz_5534_ = lean_array_size(v___x_5531_);
v___x_5535_ = ((size_t)0ULL);
v___x_5536_ = lean_unbox(v___x_5523_);
lean_dec(v___x_5523_);
v___x_5537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5501_, v___x_5536_, v___x_5504_, v___x_5505_, v___x_5531_, v_sz_5534_, v___x_5535_, v___x_5533_);
v_fst_5538_ = lean_ctor_get(v___x_5537_, 0);
v_snd_5539_ = lean_ctor_get(v___x_5537_, 1);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5537_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5537_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_snd_5539_);
lean_inc(v_fst_5538_);
lean_dec(v___x_5537_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5544_; 
if (v_isShared_5542_ == 0)
{
v___x_5544_ = v___x_5541_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_fst_5538_);
lean_ctor_set(v_reuseFailAlloc_5545_, 1, v_snd_5539_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
v_a_5509_ = v___x_5544_;
goto v___jp_5508_;
}
}
}
}
}
else
{
lean_object* v___x_5549_; 
if (v_isShared_5518_ == 0)
{
v___x_5549_ = v___x_5517_;
goto v_reusejp_5548_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_fst_5514_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v_snd_5515_);
v___x_5549_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5548_;
}
v_reusejp_5548_:
{
v_a_5509_ = v___x_5549_;
goto v___jp_5508_;
}
}
}
}
v___jp_5508_:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = lean_unsigned_to_nat(1u);
v___x_5511_ = lean_nat_add(v_a_5506_, v___x_5510_);
lean_dec(v_a_5506_);
v_a_5506_ = v___x_5511_;
v_b_5507_ = v_a_5509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object* v_upperBound_5552_, lean_object* v___x_5553_, lean_object* v_fixedParamPerms_5554_, lean_object* v_next_5555_, lean_object* v___x_5556_, lean_object* v___x_5557_, lean_object* v_a_5558_, lean_object* v_b_5559_){
_start:
{
lean_object* v_res_5560_; 
v_res_5560_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5552_, v___x_5553_, v_fixedParamPerms_5554_, v_next_5555_, v___x_5556_, v___x_5557_, v_a_5558_, v_b_5559_);
lean_dec(v___x_5557_);
lean_dec(v___x_5556_);
lean_dec(v_next_5555_);
lean_dec_ref(v_fixedParamPerms_5554_);
lean_dec_ref(v___x_5553_);
lean_dec(v_upperBound_5552_);
return v_res_5560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5561_, lean_object* v___x_5562_, lean_object* v___x_5563_, lean_object* v___x_5564_, lean_object* v_fixedParamPerms_5565_, lean_object* v_next_5566_, lean_object* v_a_5567_, lean_object* v_b_5568_){
_start:
{
lean_object* v_a_5570_; uint8_t v___x_5574_; 
v___x_5574_ = lean_nat_dec_lt(v_a_5567_, v_upperBound_5561_);
if (v___x_5574_ == 0)
{
return v_b_5568_;
}
else
{
lean_object* v_fst_5575_; lean_object* v_snd_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5612_; 
v_fst_5575_ = lean_ctor_get(v_b_5568_, 0);
v_snd_5576_ = lean_ctor_get(v_b_5568_, 1);
v_isSharedCheck_5612_ = !lean_is_exclusive(v_b_5568_);
if (v_isSharedCheck_5612_ == 0)
{
v___x_5578_ = v_b_5568_;
v_isShared_5579_ = v_isSharedCheck_5612_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_snd_5576_);
lean_inc(v_fst_5575_);
lean_dec(v_b_5568_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5612_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5580_; 
v___x_5580_ = lean_array_fget_borrowed(v___x_5562_, v_a_5567_);
if (lean_obj_tag(v___x_5580_) == 1)
{
lean_object* v_val_5581_; uint8_t v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; uint8_t v___x_5585_; 
v_val_5581_ = lean_ctor_get(v___x_5580_, 0);
v___x_5582_ = 0;
v___x_5583_ = lean_box(v___x_5582_);
v___x_5584_ = lean_array_get(v___x_5583_, v_fst_5575_, v_val_5581_);
lean_dec(v___x_5583_);
v___x_5585_ = lean_unbox(v___x_5584_);
if (v___x_5585_ == 0)
{
lean_object* v___x_5587_; 
lean_dec(v___x_5584_);
if (v_isShared_5579_ == 0)
{
v___x_5587_ = v___x_5578_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_fst_5575_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v_snd_5576_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
v_a_5570_ = v___x_5587_;
goto v___jp_5569_;
}
}
else
{
lean_object* v_revDeps_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5594_; 
v_revDeps_5589_ = lean_ctor_get(v_fixedParamPerms_5565_, 2);
v___x_5590_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___closed__0);
v___x_5591_ = lean_array_get_borrowed(v___x_5590_, v_revDeps_5589_, v_next_5566_);
v___x_5592_ = lean_array_get_borrowed(v___x_5590_, v___x_5591_, v_a_5567_);
if (v_isShared_5579_ == 0)
{
v___x_5594_ = v___x_5578_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_fst_5575_);
lean_ctor_set(v_reuseFailAlloc_5608_, 1, v_snd_5576_);
v___x_5594_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
size_t v_sz_5595_; size_t v___x_5596_; uint8_t v___x_5597_; lean_object* v___x_5598_; lean_object* v_fst_5599_; lean_object* v_snd_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5607_; 
v_sz_5595_ = lean_array_size(v___x_5592_);
v___x_5596_ = ((size_t)0ULL);
v___x_5597_ = lean_unbox(v___x_5584_);
lean_dec(v___x_5584_);
v___x_5598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5562_, v___x_5597_, v___x_5563_, v___x_5564_, v___x_5592_, v_sz_5595_, v___x_5596_, v___x_5594_);
v_fst_5599_ = lean_ctor_get(v___x_5598_, 0);
v_snd_5600_ = lean_ctor_get(v___x_5598_, 1);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5602_ = v___x_5598_;
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_snd_5600_);
lean_inc(v_fst_5599_);
lean_dec(v___x_5598_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5605_; 
if (v_isShared_5603_ == 0)
{
v___x_5605_ = v___x_5602_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_fst_5599_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v_snd_5600_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
v_a_5570_ = v___x_5605_;
goto v___jp_5569_;
}
}
}
}
}
else
{
lean_object* v___x_5610_; 
if (v_isShared_5579_ == 0)
{
v___x_5610_ = v___x_5578_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v_fst_5575_);
lean_ctor_set(v_reuseFailAlloc_5611_, 1, v_snd_5576_);
v___x_5610_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
v_a_5570_ = v___x_5610_;
goto v___jp_5569_;
}
}
}
}
v___jp_5569_:
{
lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; 
v___x_5571_ = lean_unsigned_to_nat(1u);
v___x_5572_ = lean_nat_add(v_a_5567_, v___x_5571_);
v___x_5573_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5561_, v___x_5562_, v_fixedParamPerms_5565_, v_next_5566_, v___x_5563_, v___x_5564_, v___x_5572_, v_a_5570_);
return v___x_5573_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5613_, lean_object* v___x_5614_, lean_object* v___x_5615_, lean_object* v___x_5616_, lean_object* v_fixedParamPerms_5617_, lean_object* v_next_5618_, lean_object* v_a_5619_, lean_object* v_b_5620_){
_start:
{
lean_object* v_res_5621_; 
v_res_5621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5613_, v___x_5614_, v___x_5615_, v___x_5616_, v_fixedParamPerms_5617_, v_next_5618_, v_a_5619_, v_b_5620_);
lean_dec(v_a_5619_);
lean_dec(v_next_5618_);
lean_dec_ref(v_fixedParamPerms_5617_);
lean_dec(v___x_5616_);
lean_dec(v___x_5615_);
lean_dec_ref(v___x_5614_);
lean_dec(v_upperBound_5613_);
return v_res_5621_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5622_, lean_object* v___x_5623_, lean_object* v___x_5624_, lean_object* v___x_5625_, lean_object* v_fixedParamPerms_5626_, lean_object* v_a_5627_, lean_object* v_b_5628_){
_start:
{
uint8_t v___x_5629_; 
v___x_5629_ = lean_nat_dec_lt(v_a_5627_, v_upperBound_5622_);
if (v___x_5629_ == 0)
{
lean_dec(v_a_5627_);
return v_b_5628_;
}
else
{
lean_object* v_fst_5630_; lean_object* v_snd_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5654_; 
v_fst_5630_ = lean_ctor_get(v_b_5628_, 0);
v_snd_5631_ = lean_ctor_get(v_b_5628_, 1);
v_isSharedCheck_5654_ = !lean_is_exclusive(v_b_5628_);
if (v_isSharedCheck_5654_ == 0)
{
v___x_5633_ = v_b_5628_;
v_isShared_5634_ = v_isSharedCheck_5654_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_snd_5631_);
lean_inc(v_fst_5630_);
lean_dec(v_b_5628_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5654_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5639_; 
v___x_5635_ = lean_array_fget_borrowed(v___x_5623_, v_a_5627_);
v___x_5636_ = lean_array_get_size(v___x_5635_);
v___x_5637_ = lean_unsigned_to_nat(0u);
if (v_isShared_5634_ == 0)
{
v___x_5639_ = v___x_5633_;
goto v_reusejp_5638_;
}
else
{
lean_object* v_reuseFailAlloc_5653_; 
v_reuseFailAlloc_5653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5653_, 0, v_fst_5630_);
lean_ctor_set(v_reuseFailAlloc_5653_, 1, v_snd_5631_);
v___x_5639_ = v_reuseFailAlloc_5653_;
goto v_reusejp_5638_;
}
v_reusejp_5638_:
{
lean_object* v___x_5640_; lean_object* v_fst_5641_; lean_object* v_snd_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5652_; 
v___x_5640_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5636_, v___x_5635_, v___x_5624_, v___x_5625_, v_fixedParamPerms_5626_, v_a_5627_, v___x_5637_, v___x_5639_);
v_fst_5641_ = lean_ctor_get(v___x_5640_, 0);
v_snd_5642_ = lean_ctor_get(v___x_5640_, 1);
v_isSharedCheck_5652_ = !lean_is_exclusive(v___x_5640_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5644_ = v___x_5640_;
v_isShared_5645_ = v_isSharedCheck_5652_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_snd_5642_);
lean_inc(v_fst_5641_);
lean_dec(v___x_5640_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5652_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_fst_5641_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v_snd_5642_);
v___x_5647_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
lean_object* v___x_5648_; lean_object* v___x_5649_; 
v___x_5648_ = lean_unsigned_to_nat(1u);
v___x_5649_ = lean_nat_add(v_a_5627_, v___x_5648_);
lean_dec(v_a_5627_);
v_a_5627_ = v___x_5649_;
v_b_5628_ = v___x_5647_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5655_, lean_object* v___x_5656_, lean_object* v___x_5657_, lean_object* v___x_5658_, lean_object* v_fixedParamPerms_5659_, lean_object* v_a_5660_, lean_object* v_b_5661_){
_start:
{
lean_object* v_res_5662_; 
v_res_5662_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5655_, v___x_5656_, v___x_5657_, v___x_5658_, v_fixedParamPerms_5659_, v_a_5660_, v_b_5661_);
lean_dec_ref(v_fixedParamPerms_5659_);
lean_dec(v___x_5658_);
lean_dec(v___x_5657_);
lean_dec_ref(v___x_5656_);
lean_dec(v_upperBound_5655_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5663_, lean_object* v___x_5664_, lean_object* v___x_5665_, lean_object* v_fixedParamPerms_5666_, lean_object* v_a_5667_){
_start:
{
lean_object* v_snd_5668_; uint8_t v___x_5669_; 
v_snd_5668_ = lean_ctor_get(v_a_5667_, 1);
v___x_5669_ = lean_unbox(v_snd_5668_);
if (v___x_5669_ == 0)
{
lean_object* v_fst_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5677_; 
lean_inc(v_snd_5668_);
v_fst_5670_ = lean_ctor_get(v_a_5667_, 0);
v_isSharedCheck_5677_ = !lean_is_exclusive(v_a_5667_);
if (v_isSharedCheck_5677_ == 0)
{
lean_object* v_unused_5678_; 
v_unused_5678_ = lean_ctor_get(v_a_5667_, 1);
lean_dec(v_unused_5678_);
v___x_5672_ = v_a_5667_;
v_isShared_5673_ = v_isSharedCheck_5677_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_fst_5670_);
lean_dec(v_a_5667_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5677_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
lean_object* v___x_5675_; 
if (v_isShared_5673_ == 0)
{
v___x_5675_ = v___x_5672_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_fst_5670_);
lean_ctor_set(v_reuseFailAlloc_5676_, 1, v_snd_5668_);
v___x_5675_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
return v___x_5675_;
}
}
}
else
{
lean_object* v_fst_5679_; lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5700_; 
v_fst_5679_ = lean_ctor_get(v_a_5667_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v_a_5667_);
if (v_isSharedCheck_5700_ == 0)
{
lean_object* v_unused_5701_; 
v_unused_5701_ = lean_ctor_get(v_a_5667_, 1);
lean_dec(v_unused_5701_);
v___x_5681_ = v_a_5667_;
v_isShared_5682_ = v_isSharedCheck_5700_;
goto v_resetjp_5680_;
}
else
{
lean_inc(v_fst_5679_);
lean_dec(v_a_5667_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5700_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
uint8_t v_changed_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5687_; 
v_changed_5683_ = 0;
v___x_5684_ = lean_unsigned_to_nat(0u);
v___x_5685_ = lean_box(v_changed_5683_);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 1, v___x_5685_);
v___x_5687_ = v___x_5681_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_fst_5679_);
lean_ctor_set(v_reuseFailAlloc_5699_, 1, v___x_5685_);
v___x_5687_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
lean_object* v___x_5688_; lean_object* v_fst_5689_; lean_object* v_snd_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5698_; 
v___x_5688_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5663_, v___x_5664_, v___x_5665_, v___x_5663_, v_fixedParamPerms_5666_, v___x_5684_, v___x_5687_);
v_fst_5689_ = lean_ctor_get(v___x_5688_, 0);
v_snd_5690_ = lean_ctor_get(v___x_5688_, 1);
v_isSharedCheck_5698_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5692_ = v___x_5688_;
v_isShared_5693_ = v_isSharedCheck_5698_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_snd_5690_);
lean_inc(v_fst_5689_);
lean_dec(v___x_5688_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5698_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5693_ == 0)
{
v___x_5695_ = v___x_5692_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_fst_5689_);
lean_ctor_set(v_reuseFailAlloc_5697_, 1, v_snd_5690_);
v___x_5695_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
v_a_5667_ = v___x_5695_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5702_, lean_object* v___x_5703_, lean_object* v___x_5704_, lean_object* v_fixedParamPerms_5705_, lean_object* v_a_5706_){
_start:
{
lean_object* v_res_5707_; 
v_res_5707_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5702_, v___x_5703_, v___x_5704_, v_fixedParamPerms_5705_, v_a_5706_);
lean_dec_ref(v_fixedParamPerms_5705_);
lean_dec(v___x_5704_);
lean_dec_ref(v___x_5703_);
lean_dec(v___x_5702_);
return v_res_5707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5708_, lean_object* v_a_5709_, lean_object* v_b_5710_){
_start:
{
lean_object* v_a_5712_; uint8_t v___x_5716_; 
v___x_5716_ = lean_nat_dec_lt(v_a_5709_, v_upperBound_5708_);
if (v___x_5716_ == 0)
{
lean_dec(v_a_5709_);
return v_b_5710_;
}
else
{
lean_object* v_snd_5717_; lean_object* v_snd_5718_; lean_object* v_snd_5719_; lean_object* v_snd_5720_; lean_object* v_fst_5721_; lean_object* v___x_5723_; uint8_t v_isShared_5724_; uint8_t v_isSharedCheck_5833_; 
v_snd_5717_ = lean_ctor_get(v_b_5710_, 1);
lean_inc(v_snd_5717_);
v_snd_5718_ = lean_ctor_get(v_snd_5717_, 1);
lean_inc(v_snd_5718_);
v_snd_5719_ = lean_ctor_get(v_snd_5718_, 1);
lean_inc(v_snd_5719_);
v_snd_5720_ = lean_ctor_get(v_snd_5719_, 1);
lean_inc(v_snd_5720_);
v_fst_5721_ = lean_ctor_get(v_b_5710_, 0);
v_isSharedCheck_5833_ = !lean_is_exclusive(v_b_5710_);
if (v_isSharedCheck_5833_ == 0)
{
lean_object* v_unused_5834_; 
v_unused_5834_ = lean_ctor_get(v_b_5710_, 1);
lean_dec(v_unused_5834_);
v___x_5723_ = v_b_5710_;
v_isShared_5724_ = v_isSharedCheck_5833_;
goto v_resetjp_5722_;
}
else
{
lean_inc(v_fst_5721_);
lean_dec(v_b_5710_);
v___x_5723_ = lean_box(0);
v_isShared_5724_ = v_isSharedCheck_5833_;
goto v_resetjp_5722_;
}
v_resetjp_5722_:
{
lean_object* v_fst_5725_; lean_object* v___x_5727_; uint8_t v_isShared_5728_; uint8_t v_isSharedCheck_5831_; 
v_fst_5725_ = lean_ctor_get(v_snd_5717_, 0);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_snd_5717_);
if (v_isSharedCheck_5831_ == 0)
{
lean_object* v_unused_5832_; 
v_unused_5832_ = lean_ctor_get(v_snd_5717_, 1);
lean_dec(v_unused_5832_);
v___x_5727_ = v_snd_5717_;
v_isShared_5728_ = v_isSharedCheck_5831_;
goto v_resetjp_5726_;
}
else
{
lean_inc(v_fst_5725_);
lean_dec(v_snd_5717_);
v___x_5727_ = lean_box(0);
v_isShared_5728_ = v_isSharedCheck_5831_;
goto v_resetjp_5726_;
}
v_resetjp_5726_:
{
lean_object* v_fst_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5829_; 
v_fst_5729_ = lean_ctor_get(v_snd_5718_, 0);
v_isSharedCheck_5829_ = !lean_is_exclusive(v_snd_5718_);
if (v_isSharedCheck_5829_ == 0)
{
lean_object* v_unused_5830_; 
v_unused_5830_ = lean_ctor_get(v_snd_5718_, 1);
lean_dec(v_unused_5830_);
v___x_5731_ = v_snd_5718_;
v_isShared_5732_ = v_isSharedCheck_5829_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_fst_5729_);
lean_dec(v_snd_5718_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5829_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v_fst_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5827_; 
v_fst_5733_ = lean_ctor_get(v_snd_5719_, 0);
v_isSharedCheck_5827_ = !lean_is_exclusive(v_snd_5719_);
if (v_isSharedCheck_5827_ == 0)
{
lean_object* v_unused_5828_; 
v_unused_5828_ = lean_ctor_get(v_snd_5719_, 1);
lean_dec(v_unused_5828_);
v___x_5735_ = v_snd_5719_;
v_isShared_5736_ = v_isSharedCheck_5827_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_fst_5733_);
lean_dec(v_snd_5719_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5827_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v_array_5737_; lean_object* v_start_5738_; lean_object* v_stop_5739_; uint8_t v___x_5740_; 
v_array_5737_ = lean_ctor_get(v_snd_5720_, 0);
v_start_5738_ = lean_ctor_get(v_snd_5720_, 1);
v_stop_5739_ = lean_ctor_get(v_snd_5720_, 2);
v___x_5740_ = lean_nat_dec_lt(v_start_5738_, v_stop_5739_);
if (v___x_5740_ == 0)
{
lean_object* v___x_5742_; 
lean_dec(v_a_5709_);
if (v_isShared_5736_ == 0)
{
v___x_5742_ = v___x_5735_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_fst_5733_);
lean_ctor_set(v_reuseFailAlloc_5752_, 1, v_snd_5720_);
v___x_5742_ = v_reuseFailAlloc_5752_;
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
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_fst_5729_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v___x_5742_);
v___x_5744_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
lean_object* v___x_5746_; 
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5744_);
v___x_5746_ = v___x_5727_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_fst_5725_);
lean_ctor_set(v_reuseFailAlloc_5750_, 1, v___x_5744_);
v___x_5746_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
lean_object* v___x_5748_; 
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 1, v___x_5746_);
v___x_5748_ = v___x_5723_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_fst_5721_);
lean_ctor_set(v_reuseFailAlloc_5749_, 1, v___x_5746_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
}
}
}
else
{
lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5823_; 
lean_inc(v_stop_5739_);
lean_inc(v_start_5738_);
lean_inc_ref(v_array_5737_);
v_isSharedCheck_5823_ = !lean_is_exclusive(v_snd_5720_);
if (v_isSharedCheck_5823_ == 0)
{
lean_object* v_unused_5824_; lean_object* v_unused_5825_; lean_object* v_unused_5826_; 
v_unused_5824_ = lean_ctor_get(v_snd_5720_, 2);
lean_dec(v_unused_5824_);
v_unused_5825_ = lean_ctor_get(v_snd_5720_, 1);
lean_dec(v_unused_5825_);
v_unused_5826_ = lean_ctor_get(v_snd_5720_, 0);
lean_dec(v_unused_5826_);
v___x_5754_ = v_snd_5720_;
v_isShared_5755_ = v_isSharedCheck_5823_;
goto v_resetjp_5753_;
}
else
{
lean_dec(v_snd_5720_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5823_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v_array_5756_; lean_object* v_start_5757_; lean_object* v_stop_5758_; lean_object* v___x_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5763_; 
v_array_5756_ = lean_ctor_get(v_fst_5733_, 0);
v_start_5757_ = lean_ctor_get(v_fst_5733_, 1);
v_stop_5758_ = lean_ctor_get(v_fst_5733_, 2);
v___x_5759_ = lean_array_fget(v_array_5737_, v_start_5738_);
v___x_5760_ = lean_unsigned_to_nat(1u);
v___x_5761_ = lean_nat_add(v_start_5738_, v___x_5760_);
lean_dec(v_start_5738_);
if (v_isShared_5755_ == 0)
{
lean_ctor_set(v___x_5754_, 1, v___x_5761_);
v___x_5763_ = v___x_5754_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_array_5737_);
lean_ctor_set(v_reuseFailAlloc_5822_, 1, v___x_5761_);
lean_ctor_set(v_reuseFailAlloc_5822_, 2, v_stop_5739_);
v___x_5763_ = v_reuseFailAlloc_5822_;
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
lean_dec(v_a_5709_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5763_);
v___x_5766_ = v___x_5735_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_fst_5733_);
lean_ctor_set(v_reuseFailAlloc_5776_, 1, v___x_5763_);
v___x_5766_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
lean_object* v___x_5768_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5766_);
v___x_5768_ = v___x_5731_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_fst_5729_);
lean_ctor_set(v_reuseFailAlloc_5775_, 1, v___x_5766_);
v___x_5768_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
lean_object* v___x_5770_; 
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5768_);
v___x_5770_ = v___x_5727_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_fst_5725_);
lean_ctor_set(v_reuseFailAlloc_5774_, 1, v___x_5768_);
v___x_5770_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
lean_object* v___x_5772_; 
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 1, v___x_5770_);
v___x_5772_ = v___x_5723_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_fst_5721_);
lean_ctor_set(v_reuseFailAlloc_5773_, 1, v___x_5770_);
v___x_5772_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
return v___x_5772_;
}
}
}
}
}
else
{
lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5818_; 
lean_inc(v_stop_5758_);
lean_inc(v_start_5757_);
lean_inc_ref(v_array_5756_);
v_isSharedCheck_5818_ = !lean_is_exclusive(v_fst_5733_);
if (v_isSharedCheck_5818_ == 0)
{
lean_object* v_unused_5819_; lean_object* v_unused_5820_; lean_object* v_unused_5821_; 
v_unused_5819_ = lean_ctor_get(v_fst_5733_, 2);
lean_dec(v_unused_5819_);
v_unused_5820_ = lean_ctor_get(v_fst_5733_, 1);
lean_dec(v_unused_5820_);
v_unused_5821_ = lean_ctor_get(v_fst_5733_, 0);
lean_dec(v_unused_5821_);
v___x_5778_ = v_fst_5733_;
v_isShared_5779_ = v_isSharedCheck_5818_;
goto v_resetjp_5777_;
}
else
{
lean_dec(v_fst_5733_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5818_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5783_; 
v___x_5780_ = lean_array_fget(v_array_5756_, v_start_5757_);
v___x_5781_ = lean_nat_add(v_start_5757_, v___x_5760_);
lean_dec(v_start_5757_);
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 1, v___x_5781_);
v___x_5783_ = v___x_5778_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_array_5756_);
lean_ctor_set(v_reuseFailAlloc_5817_, 1, v___x_5781_);
lean_ctor_set(v_reuseFailAlloc_5817_, 2, v_stop_5758_);
v___x_5783_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
uint8_t v___x_5784_; 
v___x_5784_ = lean_unbox(v___x_5780_);
lean_dec(v___x_5780_);
if (v___x_5784_ == 0)
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5790_; 
v___x_5785_ = lean_array_get_size(v_fst_5729_);
v___x_5786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5786_, 0, v___x_5785_);
v___x_5787_ = lean_array_push(v_fst_5721_, v___x_5786_);
v___x_5788_ = lean_array_push(v_fst_5729_, v___x_5759_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5763_);
lean_ctor_set(v___x_5735_, 0, v___x_5783_);
v___x_5790_ = v___x_5735_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v___x_5783_);
lean_ctor_set(v_reuseFailAlloc_5800_, 1, v___x_5763_);
v___x_5790_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
lean_object* v___x_5792_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5790_);
lean_ctor_set(v___x_5731_, 0, v___x_5788_);
v___x_5792_ = v___x_5731_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v___x_5788_);
lean_ctor_set(v_reuseFailAlloc_5799_, 1, v___x_5790_);
v___x_5792_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5791_;
}
v_reusejp_5791_:
{
lean_object* v___x_5794_; 
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5792_);
v___x_5794_ = v___x_5727_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_fst_5725_);
lean_ctor_set(v_reuseFailAlloc_5798_, 1, v___x_5792_);
v___x_5794_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
lean_object* v___x_5796_; 
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 1, v___x_5794_);
lean_ctor_set(v___x_5723_, 0, v___x_5787_);
v___x_5796_ = v___x_5723_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5787_);
lean_ctor_set(v_reuseFailAlloc_5797_, 1, v___x_5794_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
v_a_5712_ = v___x_5796_;
goto v___jp_5711_;
}
}
}
}
}
else
{
lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5806_; 
v___x_5801_ = lean_box(0);
v___x_5802_ = lean_array_push(v_fst_5721_, v___x_5801_);
v___x_5803_ = l_Lean_Expr_fvarId_x21(v___x_5759_);
lean_dec(v___x_5759_);
v___x_5804_ = lean_array_push(v_fst_5725_, v___x_5803_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5763_);
lean_ctor_set(v___x_5735_, 0, v___x_5783_);
v___x_5806_ = v___x_5735_;
goto v_reusejp_5805_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v___x_5783_);
lean_ctor_set(v_reuseFailAlloc_5816_, 1, v___x_5763_);
v___x_5806_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5805_;
}
v_reusejp_5805_:
{
lean_object* v___x_5808_; 
if (v_isShared_5732_ == 0)
{
lean_ctor_set(v___x_5731_, 1, v___x_5806_);
v___x_5808_ = v___x_5731_;
goto v_reusejp_5807_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v_fst_5729_);
lean_ctor_set(v_reuseFailAlloc_5815_, 1, v___x_5806_);
v___x_5808_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5807_;
}
v_reusejp_5807_:
{
lean_object* v___x_5810_; 
if (v_isShared_5728_ == 0)
{
lean_ctor_set(v___x_5727_, 1, v___x_5808_);
lean_ctor_set(v___x_5727_, 0, v___x_5804_);
v___x_5810_ = v___x_5727_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v___x_5804_);
lean_ctor_set(v_reuseFailAlloc_5814_, 1, v___x_5808_);
v___x_5810_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
lean_object* v___x_5812_; 
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 1, v___x_5810_);
lean_ctor_set(v___x_5723_, 0, v___x_5802_);
v___x_5812_ = v___x_5723_;
goto v_reusejp_5811_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5802_);
lean_ctor_set(v_reuseFailAlloc_5813_, 1, v___x_5810_);
v___x_5812_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5811_;
}
v_reusejp_5811_:
{
v_a_5712_ = v___x_5812_;
goto v___jp_5711_;
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
v___jp_5711_:
{
lean_object* v___x_5713_; lean_object* v___x_5714_; 
v___x_5713_ = lean_unsigned_to_nat(1u);
v___x_5714_ = lean_nat_add(v_a_5709_, v___x_5713_);
lean_dec(v_a_5709_);
v_a_5709_ = v___x_5714_;
v_b_5710_ = v_a_5712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5835_, lean_object* v_a_5836_, lean_object* v_b_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5835_, v_a_5836_, v_b_5837_);
lean_dec(v_upperBound_5835_);
return v_res_5838_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5839_, size_t v_i_5840_, size_t v_stop_5841_){
_start:
{
uint8_t v___x_5842_; 
v___x_5842_ = lean_usize_dec_eq(v_i_5840_, v_stop_5841_);
if (v___x_5842_ == 0)
{
lean_object* v___x_5843_; uint8_t v___x_5844_; 
v___x_5843_ = lean_array_uget_borrowed(v_as_5839_, v_i_5840_);
v___x_5844_ = l_Lean_Expr_isFVar(v___x_5843_);
if (v___x_5844_ == 0)
{
uint8_t v___x_5845_; 
v___x_5845_ = 1;
return v___x_5845_;
}
else
{
size_t v___x_5846_; size_t v___x_5847_; 
v___x_5846_ = ((size_t)1ULL);
v___x_5847_ = lean_usize_add(v_i_5840_, v___x_5846_);
v_i_5840_ = v___x_5847_;
goto _start;
}
}
else
{
uint8_t v___x_5849_; 
v___x_5849_ = 0;
return v___x_5849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5850_, lean_object* v_i_5851_, lean_object* v_stop_5852_){
_start:
{
size_t v_i_boxed_5853_; size_t v_stop_boxed_5854_; uint8_t v_res_5855_; lean_object* v_r_5856_; 
v_i_boxed_5853_ = lean_unbox_usize(v_i_5851_);
lean_dec(v_i_5851_);
v_stop_boxed_5854_ = lean_unbox_usize(v_stop_5852_);
lean_dec(v_stop_5852_);
v_res_5855_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5850_, v_i_boxed_5853_, v_stop_boxed_5854_);
lean_dec_ref(v_as_5850_);
v_r_5856_ = lean_box(v_res_5855_);
return v_r_5856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5857_, size_t v_sz_5858_, size_t v_i_5859_, lean_object* v_bs_5860_){
_start:
{
uint8_t v___x_5861_; 
v___x_5861_ = lean_usize_dec_lt(v_i_5859_, v_sz_5858_);
if (v___x_5861_ == 0)
{
return v_bs_5860_;
}
else
{
lean_object* v_v_5862_; lean_object* v___x_5863_; lean_object* v_bs_x27_5864_; lean_object* v___y_5866_; 
v_v_5862_ = lean_array_uget(v_bs_5860_, v_i_5859_);
v___x_5863_ = lean_unsigned_to_nat(0u);
v_bs_x27_5864_ = lean_array_uset(v_bs_5860_, v_i_5859_, v___x_5863_);
if (lean_obj_tag(v_v_5862_) == 0)
{
v___y_5866_ = v_v_5862_;
goto v___jp_5865_;
}
else
{
lean_object* v_val_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; 
v_val_5871_ = lean_ctor_get(v_v_5862_, 0);
lean_inc(v_val_5871_);
lean_dec_ref_known(v_v_5862_, 1);
v___x_5872_ = lean_box(0);
v___x_5873_ = lean_array_get_borrowed(v___x_5872_, v___x_5857_, v_val_5871_);
lean_dec(v_val_5871_);
lean_inc(v___x_5873_);
v___y_5866_ = v___x_5873_;
goto v___jp_5865_;
}
v___jp_5865_:
{
size_t v___x_5867_; size_t v___x_5868_; lean_object* v___x_5869_; 
v___x_5867_ = ((size_t)1ULL);
v___x_5868_ = lean_usize_add(v_i_5859_, v___x_5867_);
v___x_5869_ = lean_array_uset(v_bs_x27_5864_, v_i_5859_, v___y_5866_);
v_i_5859_ = v___x_5868_;
v_bs_5860_ = v___x_5869_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5874_, lean_object* v_sz_5875_, lean_object* v_i_5876_, lean_object* v_bs_5877_){
_start:
{
size_t v_sz_boxed_5878_; size_t v_i_boxed_5879_; lean_object* v_res_5880_; 
v_sz_boxed_5878_ = lean_unbox_usize(v_sz_5875_);
lean_dec(v_sz_5875_);
v_i_boxed_5879_ = lean_unbox_usize(v_i_5876_);
lean_dec(v_i_5876_);
v_res_5880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5874_, v_sz_boxed_5878_, v_i_boxed_5879_, v_bs_5877_);
lean_dec_ref(v___x_5874_);
return v_res_5880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5881_, size_t v_sz_5882_, size_t v_i_5883_, lean_object* v_bs_5884_){
_start:
{
uint8_t v___x_5885_; 
v___x_5885_ = lean_usize_dec_lt(v_i_5883_, v_sz_5882_);
if (v___x_5885_ == 0)
{
return v_bs_5884_;
}
else
{
lean_object* v_v_5886_; lean_object* v___x_5887_; lean_object* v_bs_x27_5888_; size_t v_sz_5889_; size_t v___x_5890_; lean_object* v___x_5891_; size_t v___x_5892_; size_t v___x_5893_; lean_object* v___x_5894_; 
v_v_5886_ = lean_array_uget(v_bs_5884_, v_i_5883_);
v___x_5887_ = lean_unsigned_to_nat(0u);
v_bs_x27_5888_ = lean_array_uset(v_bs_5884_, v_i_5883_, v___x_5887_);
v_sz_5889_ = lean_array_size(v_v_5886_);
v___x_5890_ = ((size_t)0ULL);
v___x_5891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5881_, v_sz_5889_, v___x_5890_, v_v_5886_);
v___x_5892_ = ((size_t)1ULL);
v___x_5893_ = lean_usize_add(v_i_5883_, v___x_5892_);
v___x_5894_ = lean_array_uset(v_bs_x27_5888_, v_i_5883_, v___x_5891_);
v_i_5883_ = v___x_5893_;
v_bs_5884_ = v___x_5894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5896_, lean_object* v_sz_5897_, lean_object* v_i_5898_, lean_object* v_bs_5899_){
_start:
{
size_t v_sz_boxed_5900_; size_t v_i_boxed_5901_; lean_object* v_res_5902_; 
v_sz_boxed_5900_ = lean_unbox_usize(v_sz_5897_);
lean_dec(v_sz_5897_);
v_i_boxed_5901_ = lean_unbox_usize(v_i_5898_);
lean_dec(v_i_5898_);
v_res_5902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5896_, v_sz_boxed_5900_, v_i_boxed_5901_, v_bs_5899_);
lean_dec_ref(v___x_5896_);
return v_res_5902_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; 
v___x_5905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5906_ = lean_unsigned_to_nat(6u);
v___x_5907_ = lean_unsigned_to_nat(463u);
v___x_5908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5909_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5910_ = l_mkPanicMessageWithDecl(v___x_5909_, v___x_5908_, v___x_5907_, v___x_5906_, v___x_5905_);
return v___x_5910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5911_, lean_object* v___x_5912_, lean_object* v___x_5913_, lean_object* v_as_5914_, size_t v_sz_5915_, size_t v_i_5916_, lean_object* v_b_5917_){
_start:
{
lean_object* v_a_5919_; uint8_t v___x_5923_; 
v___x_5923_ = lean_usize_dec_lt(v_i_5916_, v_sz_5915_);
if (v___x_5923_ == 0)
{
return v_b_5917_;
}
else
{
lean_object* v_a_5924_; lean_object* v___x_5925_; uint8_t v___x_5926_; 
v_a_5924_ = lean_array_uget_borrowed(v_as_5914_, v_i_5916_);
v___x_5925_ = lean_array_get_size(v___x_5911_);
v___x_5926_ = lean_nat_dec_lt(v_a_5924_, v___x_5925_);
if (v___x_5926_ == 0)
{
lean_object* v___x_5927_; lean_object* v___x_5928_; 
lean_dec_ref(v_b_5917_);
v___x_5927_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5928_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5927_);
if (lean_obj_tag(v___x_5928_) == 0)
{
lean_object* v_a_5929_; 
v_a_5929_ = lean_ctor_get(v___x_5928_, 0);
lean_inc(v_a_5929_);
lean_dec_ref_known(v___x_5928_, 1);
return v_a_5929_;
}
else
{
lean_object* v_a_5930_; 
v_a_5930_ = lean_ctor_get(v___x_5928_, 0);
lean_inc(v_a_5930_);
lean_dec_ref_known(v___x_5928_, 1);
v_a_5919_ = v_a_5930_;
goto v___jp_5918_;
}
}
else
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = lean_box(0);
v___x_5932_ = lean_array_get_borrowed(v___x_5931_, v___x_5911_, v_a_5924_);
if (lean_obj_tag(v___x_5932_) == 1)
{
lean_object* v_val_5933_; uint8_t v_changed_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v_val_5933_ = lean_ctor_get(v___x_5932_, 0);
v_changed_5934_ = lean_nat_dec_eq(v___x_5912_, v___x_5913_);
v___x_5935_ = lean_box(v_changed_5934_);
v___x_5936_ = lean_array_set(v_b_5917_, v_val_5933_, v___x_5935_);
v_a_5919_ = v___x_5936_;
goto v___jp_5918_;
}
else
{
v_a_5919_ = v_b_5917_;
goto v___jp_5918_;
}
}
}
v___jp_5918_:
{
size_t v___x_5920_; size_t v___x_5921_; 
v___x_5920_ = ((size_t)1ULL);
v___x_5921_ = lean_usize_add(v_i_5916_, v___x_5920_);
v_i_5916_ = v___x_5921_;
v_b_5917_ = v_a_5919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5937_, lean_object* v___x_5938_, lean_object* v___x_5939_, lean_object* v_as_5940_, lean_object* v_sz_5941_, lean_object* v_i_5942_, lean_object* v_b_5943_){
_start:
{
size_t v_sz_boxed_5944_; size_t v_i_boxed_5945_; lean_object* v_res_5946_; 
v_sz_boxed_5944_ = lean_unbox_usize(v_sz_5941_);
lean_dec(v_sz_5941_);
v_i_boxed_5945_ = lean_unbox_usize(v_i_5942_);
lean_dec(v_i_5942_);
v_res_5946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5937_, v___x_5938_, v___x_5939_, v_as_5940_, v_sz_boxed_5944_, v_i_boxed_5945_, v_b_5943_);
lean_dec_ref(v_as_5940_);
lean_dec(v___x_5939_);
lean_dec(v___x_5938_);
lean_dec_ref(v___x_5937_);
return v_res_5946_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5947_, lean_object* v___x_5948_, lean_object* v___x_5949_, lean_object* v_a_5950_, lean_object* v_b_5951_){
_start:
{
uint8_t v___x_5952_; 
v___x_5952_ = lean_nat_dec_lt(v_a_5950_, v_upperBound_5947_);
if (v___x_5952_ == 0)
{
lean_dec(v_a_5950_);
return v_b_5951_;
}
else
{
lean_object* v_snd_5953_; lean_object* v_snd_5954_; lean_object* v_fst_5955_; lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_6021_; 
v_snd_5953_ = lean_ctor_get(v_b_5951_, 1);
lean_inc(v_snd_5953_);
v_snd_5954_ = lean_ctor_get(v_snd_5953_, 1);
lean_inc(v_snd_5954_);
v_fst_5955_ = lean_ctor_get(v_b_5951_, 0);
v_isSharedCheck_6021_ = !lean_is_exclusive(v_b_5951_);
if (v_isSharedCheck_6021_ == 0)
{
lean_object* v_unused_6022_; 
v_unused_6022_ = lean_ctor_get(v_b_5951_, 1);
lean_dec(v_unused_6022_);
v___x_5957_ = v_b_5951_;
v_isShared_5958_ = v_isSharedCheck_6021_;
goto v_resetjp_5956_;
}
else
{
lean_inc(v_fst_5955_);
lean_dec(v_b_5951_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_6021_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
lean_object* v_fst_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_6019_; 
v_fst_5959_ = lean_ctor_get(v_snd_5953_, 0);
v_isSharedCheck_6019_ = !lean_is_exclusive(v_snd_5953_);
if (v_isSharedCheck_6019_ == 0)
{
lean_object* v_unused_6020_; 
v_unused_6020_ = lean_ctor_get(v_snd_5953_, 1);
lean_dec(v_unused_6020_);
v___x_5961_ = v_snd_5953_;
v_isShared_5962_ = v_isSharedCheck_6019_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_fst_5959_);
lean_dec(v_snd_5953_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_6019_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v_array_5963_; lean_object* v_start_5964_; lean_object* v_stop_5965_; uint8_t v___x_5966_; 
v_array_5963_ = lean_ctor_get(v_snd_5954_, 0);
v_start_5964_ = lean_ctor_get(v_snd_5954_, 1);
v_stop_5965_ = lean_ctor_get(v_snd_5954_, 2);
v___x_5966_ = lean_nat_dec_lt(v_start_5964_, v_stop_5965_);
if (v___x_5966_ == 0)
{
lean_object* v___x_5968_; 
lean_dec(v_a_5950_);
if (v_isShared_5962_ == 0)
{
v___x_5968_ = v___x_5961_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_fst_5959_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v_snd_5954_);
v___x_5968_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
lean_object* v___x_5970_; 
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5968_);
v___x_5970_ = v___x_5957_;
goto v_reusejp_5969_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_fst_5955_);
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
lean_object* v___x_5974_; uint8_t v_isShared_5975_; uint8_t v_isSharedCheck_6015_; 
lean_inc(v_stop_5965_);
lean_inc(v_start_5964_);
lean_inc_ref(v_array_5963_);
v_isSharedCheck_6015_ = !lean_is_exclusive(v_snd_5954_);
if (v_isSharedCheck_6015_ == 0)
{
lean_object* v_unused_6016_; lean_object* v_unused_6017_; lean_object* v_unused_6018_; 
v_unused_6016_ = lean_ctor_get(v_snd_5954_, 2);
lean_dec(v_unused_6016_);
v_unused_6017_ = lean_ctor_get(v_snd_5954_, 1);
lean_dec(v_unused_6017_);
v_unused_6018_ = lean_ctor_get(v_snd_5954_, 0);
lean_dec(v_unused_6018_);
v___x_5974_ = v_snd_5954_;
v_isShared_5975_ = v_isSharedCheck_6015_;
goto v_resetjp_5973_;
}
else
{
lean_dec(v_snd_5954_);
v___x_5974_ = lean_box(0);
v_isShared_5975_ = v_isSharedCheck_6015_;
goto v_resetjp_5973_;
}
v_resetjp_5973_:
{
lean_object* v_array_5976_; lean_object* v_start_5977_; lean_object* v_stop_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5983_; 
v_array_5976_ = lean_ctor_get(v_fst_5959_, 0);
v_start_5977_ = lean_ctor_get(v_fst_5959_, 1);
v_stop_5978_ = lean_ctor_get(v_fst_5959_, 2);
v___x_5979_ = lean_array_fget(v_array_5963_, v_start_5964_);
v___x_5980_ = lean_unsigned_to_nat(1u);
v___x_5981_ = lean_nat_add(v_start_5964_, v___x_5980_);
lean_dec(v_start_5964_);
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 1, v___x_5981_);
v___x_5983_ = v___x_5974_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_6014_; 
v_reuseFailAlloc_6014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6014_, 0, v_array_5963_);
lean_ctor_set(v_reuseFailAlloc_6014_, 1, v___x_5981_);
lean_ctor_set(v_reuseFailAlloc_6014_, 2, v_stop_5965_);
v___x_5983_ = v_reuseFailAlloc_6014_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
uint8_t v___x_5984_; 
v___x_5984_ = lean_nat_dec_lt(v_start_5977_, v_stop_5978_);
if (v___x_5984_ == 0)
{
lean_object* v___x_5986_; 
lean_dec(v___x_5979_);
lean_dec(v_a_5950_);
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 1, v___x_5983_);
v___x_5986_ = v___x_5961_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_fst_5959_);
lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5983_);
v___x_5986_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
lean_object* v___x_5988_; 
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5986_);
v___x_5988_ = v___x_5957_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_fst_5955_);
lean_ctor_set(v_reuseFailAlloc_5989_, 1, v___x_5986_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
else
{
lean_object* v___x_5992_; uint8_t v_isShared_5993_; uint8_t v_isSharedCheck_6010_; 
lean_inc(v_stop_5978_);
lean_inc(v_start_5977_);
lean_inc_ref(v_array_5976_);
v_isSharedCheck_6010_ = !lean_is_exclusive(v_fst_5959_);
if (v_isSharedCheck_6010_ == 0)
{
lean_object* v_unused_6011_; lean_object* v_unused_6012_; lean_object* v_unused_6013_; 
v_unused_6011_ = lean_ctor_get(v_fst_5959_, 2);
lean_dec(v_unused_6011_);
v_unused_6012_ = lean_ctor_get(v_fst_5959_, 1);
lean_dec(v_unused_6012_);
v_unused_6013_ = lean_ctor_get(v_fst_5959_, 0);
lean_dec(v_unused_6013_);
v___x_5992_ = v_fst_5959_;
v_isShared_5993_ = v_isSharedCheck_6010_;
goto v_resetjp_5991_;
}
else
{
lean_dec(v_fst_5959_);
v___x_5992_ = lean_box(0);
v_isShared_5993_ = v_isSharedCheck_6010_;
goto v_resetjp_5991_;
}
v_resetjp_5991_:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5997_; 
v___x_5994_ = lean_array_fget(v_array_5976_, v_start_5977_);
v___x_5995_ = lean_nat_add(v_start_5977_, v___x_5980_);
lean_dec(v_start_5977_);
if (v_isShared_5993_ == 0)
{
lean_ctor_set(v___x_5992_, 1, v___x_5995_);
v___x_5997_ = v___x_5992_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v_array_5976_);
lean_ctor_set(v_reuseFailAlloc_6009_, 1, v___x_5995_);
lean_ctor_set(v_reuseFailAlloc_6009_, 2, v_stop_5978_);
v___x_5997_ = v_reuseFailAlloc_6009_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
size_t v_sz_5998_; size_t v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6002_; 
v_sz_5998_ = lean_array_size(v___x_5994_);
v___x_5999_ = ((size_t)0ULL);
v___x_6000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5979_, v___x_5948_, v___x_5949_, v___x_5994_, v_sz_5998_, v___x_5999_, v_fst_5955_);
lean_dec(v___x_5994_);
lean_dec(v___x_5979_);
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 1, v___x_5983_);
lean_ctor_set(v___x_5961_, 0, v___x_5997_);
v___x_6002_ = v___x_5961_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v___x_5997_);
lean_ctor_set(v_reuseFailAlloc_6008_, 1, v___x_5983_);
v___x_6002_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
lean_object* v___x_6004_; 
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_6002_);
lean_ctor_set(v___x_5957_, 0, v___x_6000_);
v___x_6004_ = v___x_5957_;
goto v_reusejp_6003_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v___x_6000_);
lean_ctor_set(v_reuseFailAlloc_6007_, 1, v___x_6002_);
v___x_6004_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6003_;
}
v_reusejp_6003_:
{
lean_object* v___x_6005_; 
v___x_6005_ = lean_nat_add(v_a_5950_, v___x_5980_);
lean_dec(v_a_5950_);
v_a_5950_ = v___x_6005_;
v_b_5951_ = v___x_6004_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6023_, lean_object* v___x_6024_, lean_object* v___x_6025_, lean_object* v_a_6026_, lean_object* v_b_6027_){
_start:
{
lean_object* v_res_6028_; 
v_res_6028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6023_, v___x_6024_, v___x_6025_, v_a_6026_, v_b_6027_);
lean_dec(v___x_6025_);
lean_dec(v___x_6024_);
lean_dec(v_upperBound_6023_);
return v_res_6028_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; 
v___x_6030_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6031_ = lean_unsigned_to_nat(2u);
v___x_6032_ = lean_unsigned_to_nat(457u);
v___x_6033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6034_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6035_ = l_mkPanicMessageWithDecl(v___x_6034_, v___x_6033_, v___x_6032_, v___x_6031_, v___x_6030_);
return v___x_6035_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; 
v___x_6037_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6038_ = lean_unsigned_to_nat(2u);
v___x_6039_ = lean_unsigned_to_nat(458u);
v___x_6040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6041_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6042_ = l_mkPanicMessageWithDecl(v___x_6041_, v___x_6040_, v___x_6039_, v___x_6038_, v___x_6037_);
return v___x_6042_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___x_6044_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6045_ = lean_unsigned_to_nat(2u);
v___x_6046_ = lean_unsigned_to_nat(456u);
v___x_6047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6048_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6049_ = l_mkPanicMessageWithDecl(v___x_6048_, v___x_6047_, v___x_6046_, v___x_6045_, v___x_6044_);
return v___x_6049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6050_, lean_object* v_xs_6051_, lean_object* v_toErase_6052_){
_start:
{
lean_object* v___x_6053_; lean_object* v___x_6054_; uint8_t v___x_6138_; 
v___x_6053_ = lean_unsigned_to_nat(0u);
v___x_6054_ = lean_array_get_size(v_xs_6051_);
v___x_6138_ = lean_nat_dec_lt(v___x_6053_, v___x_6054_);
if (v___x_6138_ == 0)
{
goto v___jp_6055_;
}
else
{
if (v___x_6138_ == 0)
{
goto v___jp_6055_;
}
else
{
size_t v___x_6139_; size_t v___x_6140_; uint8_t v___x_6141_; 
v___x_6139_ = ((size_t)0ULL);
v___x_6140_ = lean_usize_of_nat(v___x_6054_);
v___x_6141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6051_, v___x_6139_, v___x_6140_);
if (v___x_6141_ == 0)
{
goto v___jp_6055_;
}
else
{
lean_object* v___x_6142_; lean_object* v___x_6143_; 
lean_dec_ref(v_toErase_6052_);
lean_dec_ref(v_xs_6051_);
lean_dec_ref(v_fixedParamPerms_6050_);
v___x_6142_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6143_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6142_);
return v___x_6143_;
}
}
}
v___jp_6055_:
{
lean_object* v_numFixed_6056_; lean_object* v_perms_6057_; lean_object* v_revDeps_6058_; uint8_t v___x_6059_; 
v_numFixed_6056_ = lean_ctor_get(v_fixedParamPerms_6050_, 0);
v_perms_6057_ = lean_ctor_get(v_fixedParamPerms_6050_, 1);
lean_inc_ref(v_perms_6057_);
v_revDeps_6058_ = lean_ctor_get(v_fixedParamPerms_6050_, 2);
lean_inc_ref(v_revDeps_6058_);
v___x_6059_ = lean_nat_dec_eq(v_numFixed_6056_, v___x_6054_);
if (v___x_6059_ == 0)
{
lean_object* v___x_6060_; lean_object* v___x_6061_; 
lean_dec_ref(v_revDeps_6058_);
lean_dec_ref(v_perms_6057_);
lean_dec_ref(v_toErase_6052_);
lean_dec_ref(v_xs_6051_);
lean_dec_ref(v_fixedParamPerms_6050_);
v___x_6060_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6061_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6060_);
return v___x_6061_;
}
else
{
lean_object* v___x_6062_; lean_object* v___x_6063_; uint8_t v_changed_6064_; 
v___x_6062_ = lean_array_get_size(v_toErase_6052_);
v___x_6063_ = lean_array_get_size(v_perms_6057_);
v_changed_6064_ = lean_nat_dec_eq(v___x_6062_, v___x_6063_);
if (v_changed_6064_ == 0)
{
lean_object* v___x_6065_; lean_object* v___x_6066_; 
lean_dec_ref(v_revDeps_6058_);
lean_dec_ref(v_perms_6057_);
lean_dec_ref(v_toErase_6052_);
lean_dec_ref(v_xs_6051_);
lean_dec_ref(v_fixedParamPerms_6050_);
v___x_6065_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6066_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6065_);
return v___x_6066_;
}
else
{
uint8_t v_changed_6067_; lean_object* v___x_6068_; lean_object* v_mask_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v_fst_6075_; lean_object* v___x_6077_; uint8_t v_isShared_6078_; uint8_t v_isSharedCheck_6136_; 
v_changed_6067_ = 0;
v___x_6068_ = lean_box(v_changed_6067_);
lean_inc(v_numFixed_6056_);
v_mask_6069_ = lean_mk_array(v_numFixed_6056_, v___x_6068_);
v___x_6070_ = l_Array_toSubarray___redArg(v_toErase_6052_, v___x_6053_, v___x_6062_);
lean_inc_ref(v_perms_6057_);
v___x_6071_ = l_Array_toSubarray___redArg(v_perms_6057_, v___x_6053_, v___x_6063_);
v___x_6072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6070_);
lean_ctor_set(v___x_6072_, 1, v___x_6071_);
v___x_6073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6073_, 0, v_mask_6069_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6062_, v___x_6062_, v___x_6063_, v___x_6053_, v___x_6073_);
v_fst_6075_ = lean_ctor_get(v___x_6074_, 0);
v_isSharedCheck_6136_ = !lean_is_exclusive(v___x_6074_);
if (v_isSharedCheck_6136_ == 0)
{
lean_object* v_unused_6137_; 
v_unused_6137_ = lean_ctor_get(v___x_6074_, 1);
lean_dec(v_unused_6137_);
v___x_6077_ = v___x_6074_;
v_isShared_6078_ = v_isSharedCheck_6136_;
goto v_resetjp_6076_;
}
else
{
lean_inc(v_fst_6075_);
lean_dec(v___x_6074_);
v___x_6077_ = lean_box(0);
v_isShared_6078_ = v_isSharedCheck_6136_;
goto v_resetjp_6076_;
}
v_resetjp_6076_:
{
lean_object* v___x_6079_; lean_object* v___x_6081_; 
v___x_6079_ = lean_box(v_changed_6064_);
if (v_isShared_6078_ == 0)
{
lean_ctor_set(v___x_6077_, 1, v___x_6079_);
v___x_6081_ = v___x_6077_;
goto v_reusejp_6080_;
}
else
{
lean_object* v_reuseFailAlloc_6135_; 
v_reuseFailAlloc_6135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_fst_6075_);
lean_ctor_set(v_reuseFailAlloc_6135_, 1, v___x_6079_);
v___x_6081_ = v_reuseFailAlloc_6135_;
goto v_reusejp_6080_;
}
v_reusejp_6080_:
{
lean_object* v___x_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6131_; 
v___x_6082_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6063_, v_perms_6057_, v___x_6062_, v_fixedParamPerms_6050_, v___x_6081_);
v_isSharedCheck_6131_ = !lean_is_exclusive(v_fixedParamPerms_6050_);
if (v_isSharedCheck_6131_ == 0)
{
lean_object* v_unused_6132_; lean_object* v_unused_6133_; lean_object* v_unused_6134_; 
v_unused_6132_ = lean_ctor_get(v_fixedParamPerms_6050_, 2);
lean_dec(v_unused_6132_);
v_unused_6133_ = lean_ctor_get(v_fixedParamPerms_6050_, 1);
lean_dec(v_unused_6133_);
v_unused_6134_ = lean_ctor_get(v_fixedParamPerms_6050_, 0);
lean_dec(v_unused_6134_);
v___x_6084_ = v_fixedParamPerms_6050_;
v_isShared_6085_ = v_isSharedCheck_6131_;
goto v_resetjp_6083_;
}
else
{
lean_dec(v_fixedParamPerms_6050_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6131_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v_fst_6086_; lean_object* v___x_6088_; uint8_t v_isShared_6089_; uint8_t v_isSharedCheck_6129_; 
v_fst_6086_ = lean_ctor_get(v___x_6082_, 0);
v_isSharedCheck_6129_ = !lean_is_exclusive(v___x_6082_);
if (v_isSharedCheck_6129_ == 0)
{
lean_object* v_unused_6130_; 
v_unused_6130_ = lean_ctor_get(v___x_6082_, 1);
lean_dec(v_unused_6130_);
v___x_6088_ = v___x_6082_;
v_isShared_6089_ = v_isSharedCheck_6129_;
goto v_resetjp_6087_;
}
else
{
lean_inc(v_fst_6086_);
lean_dec(v___x_6082_);
v___x_6088_ = lean_box(0);
v_isShared_6089_ = v_isSharedCheck_6129_;
goto v_resetjp_6087_;
}
v_resetjp_6087_:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6095_; 
v___x_6090_ = lean_array_get_size(v_fst_6086_);
v___x_6091_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6092_ = l_Array_toSubarray___redArg(v_fst_6086_, v___x_6053_, v___x_6090_);
v___x_6093_ = l_Array_toSubarray___redArg(v_xs_6051_, v___x_6053_, v___x_6054_);
if (v_isShared_6089_ == 0)
{
lean_ctor_set(v___x_6088_, 1, v___x_6093_);
lean_ctor_set(v___x_6088_, 0, v___x_6092_);
v___x_6095_ = v___x_6088_;
goto v_reusejp_6094_;
}
else
{
lean_object* v_reuseFailAlloc_6128_; 
v_reuseFailAlloc_6128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6128_, 0, v___x_6092_);
lean_ctor_set(v_reuseFailAlloc_6128_, 1, v___x_6093_);
v___x_6095_ = v_reuseFailAlloc_6128_;
goto v_reusejp_6094_;
}
v_reusejp_6094_:
{
lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v_snd_6100_; lean_object* v_snd_6101_; lean_object* v_fst_6102_; lean_object* v_fst_6103_; lean_object* v___x_6105_; uint8_t v_isShared_6106_; uint8_t v_isSharedCheck_6126_; 
v___x_6096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6091_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
v___x_6097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6091_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6091_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
v___x_6099_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6090_, v___x_6053_, v___x_6098_);
v_snd_6100_ = lean_ctor_get(v___x_6099_, 1);
lean_inc(v_snd_6100_);
v_snd_6101_ = lean_ctor_get(v_snd_6100_, 1);
lean_inc(v_snd_6101_);
v_fst_6102_ = lean_ctor_get(v___x_6099_, 0);
lean_inc(v_fst_6102_);
lean_dec_ref(v___x_6099_);
v_fst_6103_ = lean_ctor_get(v_snd_6100_, 0);
v_isSharedCheck_6126_ = !lean_is_exclusive(v_snd_6100_);
if (v_isSharedCheck_6126_ == 0)
{
lean_object* v_unused_6127_; 
v_unused_6127_ = lean_ctor_get(v_snd_6100_, 1);
lean_dec(v_unused_6127_);
v___x_6105_ = v_snd_6100_;
v_isShared_6106_ = v_isSharedCheck_6126_;
goto v_resetjp_6104_;
}
else
{
lean_inc(v_fst_6103_);
lean_dec(v_snd_6100_);
v___x_6105_ = lean_box(0);
v_isShared_6106_ = v_isSharedCheck_6126_;
goto v_resetjp_6104_;
}
v_resetjp_6104_:
{
lean_object* v_fst_6107_; lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6124_; 
v_fst_6107_ = lean_ctor_get(v_snd_6101_, 0);
v_isSharedCheck_6124_ = !lean_is_exclusive(v_snd_6101_);
if (v_isSharedCheck_6124_ == 0)
{
lean_object* v_unused_6125_; 
v_unused_6125_ = lean_ctor_get(v_snd_6101_, 1);
lean_dec(v_unused_6125_);
v___x_6109_ = v_snd_6101_;
v_isShared_6110_ = v_isSharedCheck_6124_;
goto v_resetjp_6108_;
}
else
{
lean_inc(v_fst_6107_);
lean_dec(v_snd_6101_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6124_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v___x_6111_; size_t v_sz_6112_; size_t v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6116_; 
v___x_6111_ = lean_array_get_size(v_fst_6107_);
v_sz_6112_ = lean_array_size(v_perms_6057_);
v___x_6113_ = ((size_t)0ULL);
v___x_6114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6102_, v_sz_6112_, v___x_6113_, v_perms_6057_);
lean_dec(v_fst_6102_);
if (v_isShared_6085_ == 0)
{
lean_ctor_set(v___x_6084_, 1, v___x_6114_);
lean_ctor_set(v___x_6084_, 0, v___x_6111_);
v___x_6116_ = v___x_6084_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6123_; 
v_reuseFailAlloc_6123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6123_, 0, v___x_6111_);
lean_ctor_set(v_reuseFailAlloc_6123_, 1, v___x_6114_);
lean_ctor_set(v_reuseFailAlloc_6123_, 2, v_revDeps_6058_);
v___x_6116_ = v_reuseFailAlloc_6123_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
lean_object* v___x_6118_; 
if (v_isShared_6110_ == 0)
{
lean_ctor_set(v___x_6109_, 1, v_fst_6103_);
v___x_6118_ = v___x_6109_;
goto v_reusejp_6117_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v_fst_6107_);
lean_ctor_set(v_reuseFailAlloc_6122_, 1, v_fst_6103_);
v___x_6118_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6117_;
}
v_reusejp_6117_:
{
lean_object* v___x_6120_; 
if (v_isShared_6106_ == 0)
{
lean_ctor_set(v___x_6105_, 1, v___x_6118_);
lean_ctor_set(v___x_6105_, 0, v___x_6116_);
v___x_6120_ = v___x_6105_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v___x_6116_);
lean_ctor_set(v_reuseFailAlloc_6121_, 1, v___x_6118_);
v___x_6120_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
return v___x_6120_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6144_, lean_object* v___x_6145_, lean_object* v___x_6146_, lean_object* v___x_6147_, lean_object* v_fixedParamPerms_6148_, lean_object* v_next_6149_, lean_object* v_inst_6150_, lean_object* v_R_6151_, lean_object* v_a_6152_, lean_object* v_b_6153_, lean_object* v_c_6154_){
_start:
{
lean_object* v___x_6155_; 
v___x_6155_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6144_, v___x_6145_, v___x_6146_, v___x_6147_, v_fixedParamPerms_6148_, v_next_6149_, v_a_6152_, v_b_6153_);
return v___x_6155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6156_, lean_object* v___x_6157_, lean_object* v___x_6158_, lean_object* v___x_6159_, lean_object* v_fixedParamPerms_6160_, lean_object* v_next_6161_, lean_object* v_inst_6162_, lean_object* v_R_6163_, lean_object* v_a_6164_, lean_object* v_b_6165_, lean_object* v_c_6166_){
_start:
{
lean_object* v_res_6167_; 
v_res_6167_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6156_, v___x_6157_, v___x_6158_, v___x_6159_, v_fixedParamPerms_6160_, v_next_6161_, v_inst_6162_, v_R_6163_, v_a_6164_, v_b_6165_, v_c_6166_);
lean_dec(v_a_6164_);
lean_dec(v_next_6161_);
lean_dec_ref(v_fixedParamPerms_6160_);
lean_dec(v___x_6159_);
lean_dec(v___x_6158_);
lean_dec_ref(v___x_6157_);
lean_dec(v_upperBound_6156_);
return v_res_6167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6168_, lean_object* v___x_6169_, lean_object* v___x_6170_, lean_object* v___x_6171_, lean_object* v_fixedParamPerms_6172_, lean_object* v_inst_6173_, lean_object* v_R_6174_, lean_object* v_a_6175_, lean_object* v_b_6176_, lean_object* v_c_6177_){
_start:
{
lean_object* v___x_6178_; 
v___x_6178_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6168_, v___x_6169_, v___x_6170_, v___x_6171_, v_fixedParamPerms_6172_, v_a_6175_, v_b_6176_);
return v___x_6178_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6179_, lean_object* v___x_6180_, lean_object* v___x_6181_, lean_object* v___x_6182_, lean_object* v_fixedParamPerms_6183_, lean_object* v_inst_6184_, lean_object* v_R_6185_, lean_object* v_a_6186_, lean_object* v_b_6187_, lean_object* v_c_6188_){
_start:
{
lean_object* v_res_6189_; 
v_res_6189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6179_, v___x_6180_, v___x_6181_, v___x_6182_, v_fixedParamPerms_6183_, v_inst_6184_, v_R_6185_, v_a_6186_, v_b_6187_, v_c_6188_);
lean_dec_ref(v_fixedParamPerms_6183_);
lean_dec(v___x_6182_);
lean_dec(v___x_6181_);
lean_dec_ref(v___x_6180_);
lean_dec(v_upperBound_6179_);
return v_res_6189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6190_, lean_object* v___x_6191_, lean_object* v___x_6192_, lean_object* v_fixedParamPerms_6193_, lean_object* v_inst_6194_, lean_object* v_a_6195_){
_start:
{
lean_object* v___x_6196_; 
v___x_6196_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6190_, v___x_6191_, v___x_6192_, v_fixedParamPerms_6193_, v_a_6195_);
return v___x_6196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6197_, lean_object* v___x_6198_, lean_object* v___x_6199_, lean_object* v_fixedParamPerms_6200_, lean_object* v_inst_6201_, lean_object* v_a_6202_){
_start:
{
lean_object* v_res_6203_; 
v_res_6203_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6197_, v___x_6198_, v___x_6199_, v_fixedParamPerms_6200_, v_inst_6201_, v_a_6202_);
lean_dec_ref(v_fixedParamPerms_6200_);
lean_dec(v___x_6199_);
lean_dec_ref(v___x_6198_);
lean_dec(v___x_6197_);
return v_res_6203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6204_, lean_object* v_inst_6205_, lean_object* v_R_6206_, lean_object* v_a_6207_, lean_object* v_b_6208_, lean_object* v_c_6209_){
_start:
{
lean_object* v___x_6210_; 
v___x_6210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6204_, v_a_6207_, v_b_6208_);
return v___x_6210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6211_, lean_object* v_inst_6212_, lean_object* v_R_6213_, lean_object* v_a_6214_, lean_object* v_b_6215_, lean_object* v_c_6216_){
_start:
{
lean_object* v_res_6217_; 
v_res_6217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6211_, v_inst_6212_, v_R_6213_, v_a_6214_, v_b_6215_, v_c_6216_);
lean_dec(v_upperBound_6211_);
return v_res_6217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6218_, lean_object* v___x_6219_, lean_object* v___x_6220_, lean_object* v_inst_6221_, lean_object* v_R_6222_, lean_object* v_a_6223_, lean_object* v_b_6224_, lean_object* v_c_6225_){
_start:
{
lean_object* v___x_6226_; 
v___x_6226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6218_, v___x_6219_, v___x_6220_, v_a_6223_, v_b_6224_);
return v___x_6226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6227_, lean_object* v___x_6228_, lean_object* v___x_6229_, lean_object* v_inst_6230_, lean_object* v_R_6231_, lean_object* v_a_6232_, lean_object* v_b_6233_, lean_object* v_c_6234_){
_start:
{
lean_object* v_res_6235_; 
v_res_6235_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6227_, v___x_6228_, v___x_6229_, v_inst_6230_, v_R_6231_, v_a_6232_, v_b_6233_, v_c_6234_);
lean_dec(v___x_6229_);
lean_dec(v___x_6228_);
lean_dec(v_upperBound_6227_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object* v_upperBound_6236_, lean_object* v___x_6237_, lean_object* v_fixedParamPerms_6238_, lean_object* v_next_6239_, lean_object* v___x_6240_, lean_object* v___x_6241_, lean_object* v_inst_6242_, lean_object* v_R_6243_, lean_object* v_a_6244_, lean_object* v_b_6245_, lean_object* v_c_6246_){
_start:
{
lean_object* v___x_6247_; 
v___x_6247_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_6236_, v___x_6237_, v_fixedParamPerms_6238_, v_next_6239_, v___x_6240_, v___x_6241_, v_a_6244_, v_b_6245_);
return v___x_6247_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object* v_upperBound_6248_, lean_object* v___x_6249_, lean_object* v_fixedParamPerms_6250_, lean_object* v_next_6251_, lean_object* v___x_6252_, lean_object* v___x_6253_, lean_object* v_inst_6254_, lean_object* v_R_6255_, lean_object* v_a_6256_, lean_object* v_b_6257_, lean_object* v_c_6258_){
_start:
{
lean_object* v_res_6259_; 
v_res_6259_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(v_upperBound_6248_, v___x_6249_, v_fixedParamPerms_6250_, v_next_6251_, v___x_6252_, v___x_6253_, v_inst_6254_, v_R_6255_, v_a_6256_, v_b_6257_, v_c_6258_);
lean_dec(v___x_6253_);
lean_dec(v___x_6252_);
lean_dec(v_next_6251_);
lean_dec_ref(v_fixedParamPerms_6250_);
lean_dec_ref(v___x_6249_);
lean_dec(v_upperBound_6248_);
return v_res_6259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6317_; uint8_t v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; 
v___x_6317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6318_ = 0;
v___x_6319_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6320_ = l_Lean_registerTraceClass(v___x_6317_, v___x_6318_, v___x_6319_);
return v___x_6320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6321_){
_start:
{
lean_object* v_res_6322_; 
v_res_6322_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6322_;
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
