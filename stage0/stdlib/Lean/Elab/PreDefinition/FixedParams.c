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
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_Format_indentD(lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(lean_object* v_revDeps_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_bs_4_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_revDeps_1_ = stack[0].m_obj;
size_t v_sz_2_ = stack[1].m_num;
size_t v_i_3_ = stack[2].m_num;
lean_object* v_bs_4_ = stack[3].m_obj;
lean_object* v_res_19_;
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(v_revDeps_1_, v_sz_2_, v_i_3_, v_bs_4_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0___boxed(lean_object* v_revDeps_20_, lean_object* v_sz_21_, lean_object* v_i_22_, lean_object* v_bs_23_){
_start:
{
size_t v_sz_boxed_24_; size_t v_i_boxed_25_; lean_object* v_res_26_; 
v_sz_boxed_24_ = lean_unbox_usize(v_sz_21_);
lean_dec(v_sz_21_);
v_i_boxed_25_ = lean_unbox_usize(v_i_22_);
lean_dec(v_i_22_);
v_res_26_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(v_revDeps_20_, v_sz_boxed_24_, v_i_boxed_25_, v_bs_23_);
lean_dec_ref(v_revDeps_20_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_init(lean_object* v_revDeps_27_){
_start:
{
size_t v_sz_28_; size_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_sz_28_ = lean_array_size(v_revDeps_27_);
v___x_29_ = ((size_t)0ULL);
lean_inc_ref(v_revDeps_27_);
v___x_30_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParams_Info_init_spec__0(v_revDeps_27_, v_sz_28_, v___x_29_, v_revDeps_27_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v_revDeps_27_);
return v___x_31_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(lean_object* v_i_32_, size_t v_sz_33_, size_t v_i_34_, lean_object* v_bs_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = lean_usize_dec_lt(v_i_34_, v_sz_33_);
if (v___x_36_ == 0)
{
return v_bs_35_;
}
else
{
lean_object* v_v_37_; lean_object* v___x_38_; lean_object* v_bs_x27_39_; lean_object* v___y_41_; 
v_v_37_ = lean_array_uget(v_bs_35_, v_i_34_);
v___x_38_ = lean_unsigned_to_nat(0u);
v_bs_x27_39_ = lean_array_uset(v_bs_35_, v_i_34_, v___x_38_);
if (lean_obj_tag(v_v_37_) == 0)
{
v___y_41_ = v_v_37_;
goto v___jp_40_;
}
else
{
lean_object* v_val_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_56_; 
v_val_46_ = lean_ctor_get(v_v_37_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v_v_37_);
if (v_isSharedCheck_56_ == 0)
{
v___x_48_ = v_v_37_;
v_isShared_49_ = v_isSharedCheck_56_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_val_46_);
lean_dec(v_v_37_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_56_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = lean_usize_to_nat(v_i_34_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_55_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_array_set(v_val_46_, v_i_32_, v___x_52_);
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
v___y_41_ = v___x_54_;
goto v___jp_40_;
}
}
}
v___jp_40_:
{
size_t v___x_42_; size_t v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((size_t)1ULL);
v___x_43_ = lean_usize_add(v_i_34_, v___x_42_);
v___x_44_ = lean_array_uset(v_bs_x27_39_, v_i_34_, v___y_41_);
v_i_34_ = v___x_43_;
v_bs_35_ = v___x_44_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_32_ = stack[0].m_obj;
size_t v_sz_33_ = stack[1].m_num;
size_t v_i_34_ = stack[2].m_num;
lean_object* v_bs_35_ = stack[3].m_obj;
lean_object* v_res_57_;
v_res_57_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v_i_32_, v_sz_33_, v_i_34_, v_bs_35_);
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg___boxed(lean_object* v_i_58_, lean_object* v_sz_59_, lean_object* v_i_60_, lean_object* v_bs_61_){
_start:
{
size_t v_sz_boxed_62_; size_t v_i_boxed_63_; lean_object* v_res_64_; 
v_sz_boxed_62_ = lean_unbox_usize(v_sz_59_);
lean_dec(v_sz_59_);
v_i_boxed_63_ = lean_unbox_usize(v_i_60_);
lean_dec(v_i_60_);
v_res_64_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v_i_58_, v_sz_boxed_62_, v_i_boxed_63_, v_bs_61_);
lean_dec(v_i_58_);
return v_res_64_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(size_t v_sz_65_, size_t v_i_66_, lean_object* v_bs_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = lean_usize_dec_lt(v_i_66_, v_sz_65_);
if (v___x_68_ == 0)
{
return v_bs_67_;
}
else
{
lean_object* v_v_69_; lean_object* v___x_70_; lean_object* v_bs_x27_71_; lean_object* v___x_72_; size_t v_sz_73_; size_t v___x_74_; lean_object* v___x_75_; size_t v___x_76_; size_t v___x_77_; lean_object* v___x_78_; 
v_v_69_ = lean_array_uget(v_bs_67_, v_i_66_);
v___x_70_ = lean_unsigned_to_nat(0u);
v_bs_x27_71_ = lean_array_uset(v_bs_67_, v_i_66_, v___x_70_);
v___x_72_ = lean_usize_to_nat(v_i_66_);
v_sz_73_ = lean_array_size(v_v_69_);
v___x_74_ = ((size_t)0ULL);
v___x_75_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v___x_72_, v_sz_73_, v___x_74_, v_v_69_);
lean_dec(v___x_72_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_add(v_i_66_, v___x_76_);
v___x_78_ = lean_array_uset(v_bs_x27_71_, v_i_66_, v___x_75_);
v_i_66_ = v___x_77_;
v_bs_67_ = v___x_78_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_65_ = stack[0].m_num;
size_t v_i_66_ = stack[1].m_num;
lean_object* v_bs_67_ = stack[2].m_obj;
lean_object* v_res_80_;
v_res_80_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_sz_65_, v_i_66_, v_bs_67_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg___boxed(lean_object* v_sz_81_, lean_object* v_i_82_, lean_object* v_bs_83_){
_start:
{
size_t v_sz_boxed_84_; size_t v_i_boxed_85_; lean_object* v_res_86_; 
v_sz_boxed_84_ = lean_unbox_usize(v_sz_81_);
lean_dec(v_sz_81_);
v_i_boxed_85_ = lean_unbox_usize(v_i_82_);
lean_dec(v_i_82_);
v_res_86_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_sz_boxed_84_, v_i_boxed_85_, v_bs_83_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_addSelfCalls(lean_object* v_info_87_){
_start:
{
lean_object* v_graph_88_; lean_object* v_revDeps_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_99_; 
v_graph_88_ = lean_ctor_get(v_info_87_, 0);
v_revDeps_89_ = lean_ctor_get(v_info_87_, 1);
v_isSharedCheck_99_ = !lean_is_exclusive(v_info_87_);
if (v_isSharedCheck_99_ == 0)
{
v___x_91_ = v_info_87_;
v_isShared_92_ = v_isSharedCheck_99_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_revDeps_89_);
lean_inc(v_graph_88_);
lean_dec(v_info_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_99_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
size_t v_sz_93_; size_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v_sz_93_ = lean_array_size(v_graph_88_);
v___x_94_ = ((size_t)0ULL);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_sz_93_, v___x_94_, v_graph_88_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_95_);
v___x_97_ = v___x_91_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_revDeps_89_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(lean_object* v_i_100_, lean_object* v_as_101_, size_t v_sz_102_, size_t v_i_103_, lean_object* v_bs_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___redArg(v_i_100_, v_sz_102_, v_i_103_, v_bs_104_);
return v___x_105_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_100_ = stack[0].m_obj;
lean_object* v_as_101_ = stack[1].m_obj;
size_t v_sz_102_ = stack[2].m_num;
size_t v_i_103_ = stack[3].m_num;
lean_object* v_bs_104_ = stack[4].m_obj;
lean_object* v_res_106_;
v_res_106_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(v_i_100_, v_as_101_, v_sz_102_, v_i_103_, v_bs_104_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0___boxed(lean_object* v_i_107_, lean_object* v_as_108_, lean_object* v_sz_109_, lean_object* v_i_110_, lean_object* v_bs_111_){
_start:
{
size_t v_sz_boxed_112_; size_t v_i_boxed_113_; lean_object* v_res_114_; 
v_sz_boxed_112_ = lean_unbox_usize(v_sz_109_);
lean_dec(v_sz_109_);
v_i_boxed_113_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__0(v_i_107_, v_as_108_, v_sz_boxed_112_, v_i_boxed_113_, v_bs_111_);
lean_dec_ref(v_as_108_);
lean_dec(v_i_107_);
return v_res_114_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(lean_object* v_as_115_, size_t v_sz_116_, size_t v_i_117_, lean_object* v_bs_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___redArg(v_sz_116_, v_i_117_, v_bs_118_);
return v___x_119_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_115_ = stack[0].m_obj;
size_t v_sz_116_ = stack[1].m_num;
size_t v_i_117_ = stack[2].m_num;
lean_object* v_bs_118_ = stack[3].m_obj;
lean_object* v_res_120_;
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(v_as_115_, v_sz_116_, v_i_117_, v_bs_118_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1___boxed(lean_object* v_as_121_, lean_object* v_sz_122_, lean_object* v_i_123_, lean_object* v_bs_124_){
_start:
{
size_t v_sz_boxed_125_; size_t v_i_boxed_126_; lean_object* v_res_127_; 
v_sz_boxed_125_ = lean_unbox_usize(v_sz_122_);
lean_dec(v_sz_122_);
v_i_boxed_126_ = lean_unbox_usize(v_i_123_);
lean_dec(v_i_123_);
v_res_127_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_FixedParams_Info_addSelfCalls_spec__1(v_as_121_, v_sz_boxed_125_, v_i_boxed_126_, v_bs_124_);
lean_dec_ref(v_as_121_);
return v_res_127_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Array_instInhabited___redArg();
return v___x_128_;
}
}
uint8_t l_Lean_Elab_FixedParams_Info_mayBeFixed(lean_object* v_callerIdx_129_, lean_object* v_paramIdx_130_, lean_object* v_info_131_){
_start:
{
lean_object* v_graph_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_graph_132_ = lean_ctor_get(v_info_131_, 0);
v___x_133_ = lean_box(0);
v___x_134_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_135_ = lean_array_get_borrowed(v___x_134_, v_graph_132_, v_callerIdx_129_);
v___x_136_ = lean_array_get_borrowed(v___x_133_, v___x_135_, v_paramIdx_130_);
if (lean_obj_tag(v___x_136_) == 0)
{
uint8_t v___x_137_; 
v___x_137_ = 0;
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = 1;
return v___x_138_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParams_Info_mayBeFixed_0interp(lean_interpreter_value* stack)
{
lean_object* v_callerIdx_129_ = stack[0].m_obj;
lean_object* v_paramIdx_130_ = stack[1].m_obj;
lean_object* v_info_131_ = stack[2].m_obj;
uint8_t v_res_139_;
v_res_139_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_callerIdx_129_, v_paramIdx_130_, v_info_131_);
stack->m_num = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_mayBeFixed___boxed(lean_object* v_callerIdx_140_, lean_object* v_paramIdx_141_, lean_object* v_info_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_callerIdx_140_, v_paramIdx_141_, v_info_142_);
lean_dec_ref(v_info_142_);
lean_dec(v_paramIdx_141_);
lean_dec(v_callerIdx_140_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(lean_object* v_upperBound_145_, lean_object* v_next_146_, lean_object* v_funIdx_147_, lean_object* v_paramIdx_148_, lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
lean_object* v_a_152_; uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_lt(v_a_149_, v_upperBound_145_);
if (v___x_156_ == 0)
{
lean_dec(v_a_149_);
lean_dec(v_paramIdx_148_);
return v_b_150_;
}
else
{
lean_object* v_graph_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_graph_157_ = lean_ctor_get(v_b_150_, 0);
v___x_158_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_159_ = lean_box(0);
v___x_160_ = lean_array_get_borrowed(v___x_158_, v_graph_157_, v_next_146_);
v___x_161_ = lean_array_get(v___x_159_, v___x_160_, v_a_149_);
if (lean_obj_tag(v___x_161_) == 1)
{
lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_173_; 
v_val_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_173_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_173_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_173_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_166_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_167_ = lean_array_get(v___x_159_, v_val_162_, v_funIdx_147_);
lean_dec(v_val_162_);
lean_inc(v_paramIdx_148_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v_paramIdx_148_);
v___x_169_ = v___x_164_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_paramIdx_148_);
v___x_169_ = v_reuseFailAlloc_172_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
uint8_t v___x_170_; 
v___x_170_ = l_Option_instDecidableEq___redArg(v___x_166_, v___x_167_, v___x_169_);
if (v___x_170_ == 0)
{
v_a_152_ = v_b_150_;
goto v___jp_151_;
}
else
{
lean_object* v___x_171_; 
lean_inc(v_a_149_);
v___x_171_ = l_Lean_Elab_FixedParams_Info_setVarying(v_next_146_, v_a_149_, v_b_150_);
v_a_152_ = v___x_171_;
goto v___jp_151_;
}
}
}
}
else
{
lean_dec(v___x_161_);
v_a_152_ = v_b_150_;
goto v___jp_151_;
}
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_add(v_a_149_, v___x_153_);
lean_dec(v_a_149_);
v_a_149_ = v___x_154_;
v_b_150_ = v_a_152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(lean_object* v_upperBound_174_, lean_object* v_funIdx_175_, lean_object* v_paramIdx_176_, lean_object* v_a_177_, lean_object* v_b_178_){
_start:
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_lt(v_a_177_, v_upperBound_174_);
if (v___x_179_ == 0)
{
lean_dec(v_a_177_);
lean_dec(v_paramIdx_176_);
return v_b_178_;
}
else
{
lean_object* v_graph_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_graph_180_ = lean_ctor_get(v_b_178_, 0);
v___x_181_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_182_ = lean_array_get_borrowed(v___x_181_, v_graph_180_, v_a_177_);
v___x_183_ = lean_array_get_size(v___x_182_);
v___x_184_ = lean_unsigned_to_nat(0u);
lean_inc(v_paramIdx_176_);
v___x_185_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v___x_183_, v_a_177_, v_funIdx_175_, v_paramIdx_176_, v___x_184_, v_b_178_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_a_177_, v___x_186_);
lean_dec(v_a_177_);
v_a_177_ = v___x_187_;
v_b_178_ = v___x_185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setVarying(lean_object* v_funIdx_189_, lean_object* v_paramIdx_190_, lean_object* v_info_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_funIdx_189_, v_paramIdx_190_, v_info_191_);
if (v___x_192_ == 0)
{
lean_dec(v_paramIdx_190_);
return v_info_191_;
}
else
{
lean_object* v_graph_193_; lean_object* v_revDeps_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_221_; 
v_graph_193_ = lean_ctor_get(v_info_191_, 0);
v_revDeps_194_ = lean_ctor_get(v_info_191_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_info_191_);
if (v_isSharedCheck_221_ == 0)
{
v___x_196_ = v_info_191_;
v_isShared_197_ = v_isSharedCheck_221_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_revDeps_194_);
lean_inc(v_graph_193_);
lean_dec(v_info_191_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_221_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___y_200_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_198_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_213_ = lean_array_get_size(v_graph_193_);
v___x_214_ = lean_nat_dec_lt(v_funIdx_189_, v___x_213_);
if (v___x_214_ == 0)
{
v___y_200_ = v_graph_193_;
goto v___jp_199_;
}
else
{
lean_object* v_v_215_; lean_object* v___x_216_; lean_object* v_xs_x27_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_v_215_ = lean_array_fget(v_graph_193_, v_funIdx_189_);
v___x_216_ = lean_box(0);
v_xs_x27_217_ = lean_array_fset(v_graph_193_, v_funIdx_189_, v___x_216_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_array_set(v_v_215_, v_paramIdx_190_, v___x_218_);
v___x_220_ = lean_array_fset(v_xs_x27_217_, v_funIdx_189_, v___x_219_);
v___y_200_ = v___x_220_;
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v_info_204_; 
v___x_201_ = lean_array_get_size(v___y_200_);
v___x_202_ = lean_unsigned_to_nat(0u);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___y_200_);
v_info_204_ = v___x_196_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___y_200_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_revDeps_194_);
v_info_204_ = v_reuseFailAlloc_212_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v_revDeps_206_; lean_object* v___x_207_; lean_object* v___x_208_; size_t v_sz_209_; size_t v___x_210_; lean_object* v___x_211_; 
lean_inc(v_paramIdx_190_);
v___x_205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v___x_201_, v_funIdx_189_, v_paramIdx_190_, v___x_202_, v_info_204_);
v_revDeps_206_ = lean_ctor_get(v___x_205_, 1);
v___x_207_ = lean_array_get_borrowed(v___x_198_, v_revDeps_206_, v_funIdx_189_);
v___x_208_ = lean_array_get(v___x_198_, v___x_207_, v_paramIdx_190_);
lean_dec(v_paramIdx_190_);
v_sz_209_ = lean_array_size(v___x_208_);
v___x_210_ = ((size_t)0ULL);
v___x_211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_189_, v___x_208_, v_sz_209_, v___x_210_, v___x_205_);
lean_dec(v___x_208_);
return v___x_211_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(lean_object* v_funIdx_222_, lean_object* v_as_223_, size_t v_sz_224_, size_t v_i_225_, lean_object* v_b_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_227_ == 0)
{
return v_b_226_;
}
else
{
lean_object* v_a_228_; lean_object* v___x_229_; size_t v___x_230_; size_t v___x_231_; 
v_a_228_ = lean_array_uget_borrowed(v_as_223_, v_i_225_);
lean_inc(v_a_228_);
v___x_229_ = l_Lean_Elab_FixedParams_Info_setVarying(v_funIdx_222_, v_a_228_, v_b_226_);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_225_, v___x_230_);
v_i_225_ = v___x_231_;
v_b_226_ = v___x_229_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_funIdx_222_ = stack[0].m_obj;
lean_object* v_as_223_ = stack[1].m_obj;
size_t v_sz_224_ = stack[2].m_num;
size_t v_i_225_ = stack[3].m_num;
lean_object* v_b_226_ = stack[4].m_obj;
lean_object* v_res_233_;
v_res_233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_222_, v_as_223_, v_sz_224_, v_i_225_, v_b_226_);
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0___boxed(lean_object* v_funIdx_234_, lean_object* v_as_235_, lean_object* v_sz_236_, lean_object* v_i_237_, lean_object* v_b_238_){
_start:
{
size_t v_sz_boxed_239_; size_t v_i_boxed_240_; lean_object* v_res_241_; 
v_sz_boxed_239_ = lean_unbox_usize(v_sz_236_);
lean_dec(v_sz_236_);
v_i_boxed_240_ = lean_unbox_usize(v_i_237_);
lean_dec(v_i_237_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_234_, v_as_235_, v_sz_boxed_239_, v_i_boxed_240_, v_b_238_);
lean_dec_ref(v_as_235_);
lean_dec(v_funIdx_234_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg___boxed(lean_object* v_upperBound_242_, lean_object* v_funIdx_243_, lean_object* v_paramIdx_244_, lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v_upperBound_242_, v_funIdx_243_, v_paramIdx_244_, v_a_245_, v_b_246_);
lean_dec(v_funIdx_243_);
lean_dec(v_upperBound_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg___boxed(lean_object* v_upperBound_248_, lean_object* v_next_249_, lean_object* v_funIdx_250_, lean_object* v_paramIdx_251_, lean_object* v_a_252_, lean_object* v_b_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v_upperBound_248_, v_next_249_, v_funIdx_250_, v_paramIdx_251_, v_a_252_, v_b_253_);
lean_dec(v_funIdx_250_);
lean_dec(v_next_249_);
lean_dec(v_upperBound_248_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setVarying___boxed(lean_object* v_funIdx_255_, lean_object* v_paramIdx_256_, lean_object* v_info_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Elab_FixedParams_Info_setVarying(v_funIdx_255_, v_paramIdx_256_, v_info_257_);
lean_dec(v_funIdx_255_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1(lean_object* v_upperBound_259_, lean_object* v_next_260_, lean_object* v_funIdx_261_, lean_object* v_paramIdx_262_, lean_object* v_inst_263_, lean_object* v_R_264_, lean_object* v_a_265_, lean_object* v_b_266_, lean_object* v_c_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___redArg(v_upperBound_259_, v_next_260_, v_funIdx_261_, v_paramIdx_262_, v_a_265_, v_b_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1___boxed(lean_object* v_upperBound_269_, lean_object* v_next_270_, lean_object* v_funIdx_271_, lean_object* v_paramIdx_272_, lean_object* v_inst_273_, lean_object* v_R_274_, lean_object* v_a_275_, lean_object* v_b_276_, lean_object* v_c_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__1(v_upperBound_269_, v_next_270_, v_funIdx_271_, v_paramIdx_272_, v_inst_273_, v_R_274_, v_a_275_, v_b_276_, v_c_277_);
lean_dec(v_funIdx_271_);
lean_dec(v_next_270_);
lean_dec(v_upperBound_269_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2(lean_object* v_upperBound_279_, lean_object* v_funIdx_280_, lean_object* v_paramIdx_281_, lean_object* v_inst_282_, lean_object* v_R_283_, lean_object* v_a_284_, lean_object* v_b_285_, lean_object* v_c_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v_upperBound_279_, v_funIdx_280_, v_paramIdx_281_, v_a_284_, v_b_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___boxed(lean_object* v_upperBound_288_, lean_object* v_funIdx_289_, lean_object* v_paramIdx_290_, lean_object* v_inst_291_, lean_object* v_R_292_, lean_object* v_a_293_, lean_object* v_b_294_, lean_object* v_c_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2(v_upperBound_288_, v_funIdx_289_, v_paramIdx_290_, v_inst_291_, v_R_292_, v_a_293_, v_b_294_, v_c_295_);
lean_dec(v_funIdx_289_);
lean_dec(v_upperBound_288_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(lean_object* v_calleeIdx_297_, lean_object* v_argIdx_298_, lean_object* v_callerIdx_299_, lean_object* v_info_300_){
_start:
{
lean_object* v_graph_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_graph_301_ = lean_ctor_get(v_info_300_, 0);
v___x_302_ = lean_box(0);
v___x_303_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_304_ = lean_array_get_borrowed(v___x_303_, v_graph_301_, v_calleeIdx_297_);
v___x_305_ = lean_array_get_borrowed(v___x_302_, v___x_304_, v_argIdx_298_);
if (lean_obj_tag(v___x_305_) == 0)
{
return v___x_302_;
}
else
{
lean_object* v_val_306_; lean_object* v___x_307_; 
v_val_306_ = lean_ctor_get(v___x_305_, 0);
v___x_307_ = lean_array_get_borrowed(v___x_302_, v_val_306_, v_callerIdx_299_);
lean_inc(v___x_307_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_getCallerParam_x3f___boxed(lean_object* v_calleeIdx_308_, lean_object* v_argIdx_309_, lean_object* v_callerIdx_310_, lean_object* v_info_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_calleeIdx_308_, v_argIdx_309_, v_callerIdx_310_, v_info_311_);
lean_dec_ref(v_info_311_);
lean_dec(v_callerIdx_310_);
lean_dec(v_argIdx_309_);
lean_dec(v_calleeIdx_308_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(lean_object* v_upperBound_313_, lean_object* v_val_314_, lean_object* v_calleeIdx_315_, lean_object* v_argIdx_316_, lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
lean_object* v_a_320_; uint8_t v___x_324_; 
v___x_324_ = lean_nat_dec_lt(v_a_317_, v_upperBound_313_);
if (v___x_324_ == 0)
{
lean_dec(v_a_317_);
lean_dec(v_argIdx_316_);
return v_b_318_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_array_fget_borrowed(v_val_314_, v_a_317_);
if (lean_obj_tag(v___x_325_) == 1)
{
lean_object* v_val_326_; lean_object* v___x_327_; 
v_val_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_326_);
lean_inc(v_argIdx_316_);
v___x_327_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_calleeIdx_315_, v_argIdx_316_, v_a_317_, v_val_326_, v_b_318_);
v_a_320_ = v___x_327_;
goto v___jp_319_;
}
else
{
v_a_320_ = v_b_318_;
goto v___jp_319_;
}
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_a_317_, v___x_321_);
lean_dec(v_a_317_);
v_a_317_ = v___x_322_;
v_b_318_ = v_a_320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setCallerParam(lean_object* v_calleeIdx_328_, lean_object* v_argIdx_329_, lean_object* v_callerIdx_330_, lean_object* v_paramIdx_331_, lean_object* v_info_332_){
_start:
{
lean_object* v_info_334_; lean_object* v_graph_335_; uint8_t v___x_339_; 
v___x_339_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_calleeIdx_328_, v_argIdx_329_, v_info_332_);
if (v___x_339_ == 0)
{
lean_dec(v_paramIdx_331_);
lean_dec(v_argIdx_329_);
return v_info_332_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_callerIdx_330_, v_paramIdx_331_, v_info_332_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_paramIdx_331_);
v___x_341_ = l_Lean_Elab_FixedParams_Info_setVarying(v_calleeIdx_328_, v_argIdx_329_, v_info_332_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_calleeIdx_328_, v_argIdx_329_, v_callerIdx_330_, v_info_332_);
if (lean_obj_tag(v___x_342_) == 1)
{
lean_object* v_val_343_; uint8_t v___x_344_; 
v_val_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = lean_nat_dec_eq(v_paramIdx_331_, v_val_343_);
lean_dec(v_val_343_);
lean_dec(v_paramIdx_331_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Elab_FixedParams_Info_setVarying(v_calleeIdx_328_, v_argIdx_329_, v_info_332_);
return v___x_345_;
}
else
{
lean_dec(v_argIdx_329_);
return v_info_332_;
}
}
else
{
lean_object* v_graph_346_; lean_object* v_revDeps_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_390_; 
lean_dec(v___x_342_);
v_graph_346_ = lean_ctor_get(v_info_332_, 0);
v_revDeps_347_ = lean_ctor_get(v_info_332_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_info_332_);
if (v_isSharedCheck_390_ == 0)
{
v___x_349_ = v_info_332_;
v_isShared_350_ = v_isSharedCheck_390_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_revDeps_347_);
lean_inc(v_graph_346_);
lean_dec(v_info_332_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_390_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___y_354_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_351_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_352_ = lean_box(0);
v___x_365_ = lean_array_get_size(v_graph_346_);
v___x_366_ = lean_nat_dec_lt(v_calleeIdx_328_, v___x_365_);
if (v___x_366_ == 0)
{
v___y_354_ = v_graph_346_;
goto v___jp_353_;
}
else
{
lean_object* v_v_367_; lean_object* v___x_368_; lean_object* v_xs_x27_369_; lean_object* v___y_371_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_v_367_ = lean_array_fget(v_graph_346_, v_calleeIdx_328_);
v___x_368_ = lean_box(0);
v_xs_x27_369_ = lean_array_fset(v_graph_346_, v_calleeIdx_328_, v___x_368_);
v___x_373_ = lean_array_get_size(v_v_367_);
v___x_374_ = lean_nat_dec_lt(v_argIdx_329_, v___x_373_);
if (v___x_374_ == 0)
{
v___y_371_ = v_v_367_;
goto v___jp_370_;
}
else
{
lean_object* v_v_375_; lean_object* v_xs_x27_376_; lean_object* v___y_378_; 
v_v_375_ = lean_array_fget(v_v_367_, v_argIdx_329_);
v_xs_x27_376_ = lean_array_fset(v_v_367_, v_argIdx_329_, v___x_368_);
if (lean_obj_tag(v_v_375_) == 0)
{
v___y_378_ = v_v_375_;
goto v___jp_377_;
}
else
{
lean_object* v_val_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_389_; 
v_val_380_ = lean_ctor_get(v_v_375_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_v_375_);
if (v_isSharedCheck_389_ == 0)
{
v___x_382_ = v_v_375_;
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_val_380_);
lean_dec(v_v_375_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
lean_inc(v_paramIdx_331_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_paramIdx_331_);
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_paramIdx_331_);
v___x_385_ = v_reuseFailAlloc_388_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_array_set(v_val_380_, v_callerIdx_330_, v___x_385_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
v___y_378_ = v___x_387_;
goto v___jp_377_;
}
}
}
v___jp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_array_fset(v_xs_x27_376_, v_argIdx_329_, v___y_378_);
v___y_371_ = v___x_379_;
goto v___jp_370_;
}
}
v___jp_370_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_array_fset(v_xs_x27_369_, v_calleeIdx_328_, v___y_371_);
v___y_354_ = v___x_372_;
goto v___jp_353_;
}
}
v___jp_353_:
{
lean_object* v_info_356_; 
lean_inc_ref(v___y_354_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___y_354_);
v_info_356_ = v___x_349_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___y_354_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_revDeps_347_);
v_info_356_ = v_reuseFailAlloc_364_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_array_get_borrowed(v___x_351_, v___y_354_, v_callerIdx_330_);
v___x_358_ = lean_array_get_borrowed(v___x_352_, v___x_357_, v_paramIdx_331_);
if (lean_obj_tag(v___x_358_) == 1)
{
lean_object* v_val_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_graph_363_; 
lean_inc_ref(v___x_358_);
lean_dec_ref(v___y_354_);
v_val_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_val_359_);
lean_dec_ref_known(v___x_358_, 1);
v___x_360_ = lean_array_get_size(v_val_359_);
v___x_361_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_329_);
v___x_362_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v___x_360_, v_val_359_, v_calleeIdx_328_, v_argIdx_329_, v___x_361_, v_info_356_);
lean_dec(v_val_359_);
v_graph_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_graph_363_);
v_info_334_ = v___x_362_;
v_graph_335_ = v_graph_363_;
goto v___jp_333_;
}
else
{
v_info_334_ = v_info_356_;
v_graph_335_ = v___y_354_;
goto v___jp_333_;
}
}
}
}
}
}
}
v___jp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_array_get_size(v_graph_335_);
lean_dec_ref(v_graph_335_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v___x_336_, v_calleeIdx_328_, v_argIdx_329_, v_callerIdx_330_, v_paramIdx_331_, v___x_337_, v_info_334_);
lean_dec(v_argIdx_329_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(lean_object* v_upperBound_391_, lean_object* v_next_392_, lean_object* v_calleeIdx_393_, lean_object* v_argIdx_394_, lean_object* v_callerIdx_395_, lean_object* v_paramIdx_396_, lean_object* v_a_397_, lean_object* v_b_398_){
_start:
{
lean_object* v_a_400_; uint8_t v___x_404_; 
v___x_404_ = lean_nat_dec_lt(v_a_397_, v_upperBound_391_);
if (v___x_404_ == 0)
{
lean_dec(v_a_397_);
lean_dec(v_paramIdx_396_);
return v_b_398_;
}
else
{
lean_object* v_graph_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_graph_405_ = lean_ctor_get(v_b_398_, 0);
v___x_406_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_407_ = lean_box(0);
v___x_408_ = lean_array_get_borrowed(v___x_406_, v_graph_405_, v_next_392_);
v___x_409_ = lean_array_get_borrowed(v___x_407_, v___x_408_, v_a_397_);
if (lean_obj_tag(v___x_409_) == 1)
{
lean_object* v_val_410_; lean_object* v___x_411_; 
v_val_410_ = lean_ctor_get(v___x_409_, 0);
v___x_411_ = lean_array_get_borrowed(v___x_407_, v_val_410_, v_calleeIdx_393_);
if (lean_obj_tag(v___x_411_) == 1)
{
lean_object* v_val_412_; uint8_t v___x_413_; 
v_val_412_ = lean_ctor_get(v___x_411_, 0);
v___x_413_ = lean_nat_dec_eq(v_val_412_, v_argIdx_394_);
if (v___x_413_ == 0)
{
v_a_400_ = v_b_398_;
goto v___jp_399_;
}
else
{
lean_object* v___x_414_; 
lean_inc(v_paramIdx_396_);
lean_inc(v_a_397_);
v___x_414_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_next_392_, v_a_397_, v_callerIdx_395_, v_paramIdx_396_, v_b_398_);
v_a_400_ = v___x_414_;
goto v___jp_399_;
}
}
else
{
v_a_400_ = v_b_398_;
goto v___jp_399_;
}
}
else
{
v_a_400_ = v_b_398_;
goto v___jp_399_;
}
}
v___jp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_unsigned_to_nat(1u);
v___x_402_ = lean_nat_add(v_a_397_, v___x_401_);
lean_dec(v_a_397_);
v_a_397_ = v___x_402_;
v_b_398_ = v_a_400_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(lean_object* v_upperBound_415_, lean_object* v_calleeIdx_416_, lean_object* v_argIdx_417_, lean_object* v_callerIdx_418_, lean_object* v_paramIdx_419_, lean_object* v_a_420_, lean_object* v_b_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = lean_nat_dec_lt(v_a_420_, v_upperBound_415_);
if (v___x_422_ == 0)
{
lean_dec(v_a_420_);
lean_dec(v_paramIdx_419_);
return v_b_421_;
}
else
{
lean_object* v_graph_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_graph_423_ = lean_ctor_get(v_b_421_, 0);
v___x_424_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_425_ = lean_array_get_borrowed(v___x_424_, v_graph_423_, v_a_420_);
v___x_426_ = lean_array_get_size(v___x_425_);
v___x_427_ = lean_unsigned_to_nat(0u);
lean_inc(v_paramIdx_419_);
v___x_428_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v___x_426_, v_a_420_, v_calleeIdx_416_, v_argIdx_417_, v_callerIdx_418_, v_paramIdx_419_, v___x_427_, v_b_421_);
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_a_420_, v___x_429_);
lean_dec(v_a_420_);
v_a_420_ = v___x_430_;
v_b_421_ = v___x_428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg___boxed(lean_object* v_upperBound_432_, lean_object* v_calleeIdx_433_, lean_object* v_argIdx_434_, lean_object* v_callerIdx_435_, lean_object* v_paramIdx_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v_upperBound_432_, v_calleeIdx_433_, v_argIdx_434_, v_callerIdx_435_, v_paramIdx_436_, v_a_437_, v_b_438_);
lean_dec(v_callerIdx_435_);
lean_dec(v_argIdx_434_);
lean_dec(v_calleeIdx_433_);
lean_dec(v_upperBound_432_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg___boxed(lean_object* v_upperBound_440_, lean_object* v_val_441_, lean_object* v_calleeIdx_442_, lean_object* v_argIdx_443_, lean_object* v_a_444_, lean_object* v_b_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v_upperBound_440_, v_val_441_, v_calleeIdx_442_, v_argIdx_443_, v_a_444_, v_b_445_);
lean_dec(v_calleeIdx_442_);
lean_dec_ref(v_val_441_);
lean_dec(v_upperBound_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg___boxed(lean_object* v_upperBound_447_, lean_object* v_next_448_, lean_object* v_calleeIdx_449_, lean_object* v_argIdx_450_, lean_object* v_callerIdx_451_, lean_object* v_paramIdx_452_, lean_object* v_a_453_, lean_object* v_b_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v_upperBound_447_, v_next_448_, v_calleeIdx_449_, v_argIdx_450_, v_callerIdx_451_, v_paramIdx_452_, v_a_453_, v_b_454_);
lean_dec(v_callerIdx_451_);
lean_dec(v_argIdx_450_);
lean_dec(v_calleeIdx_449_);
lean_dec(v_next_448_);
lean_dec(v_upperBound_447_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_setCallerParam___boxed(lean_object* v_calleeIdx_456_, lean_object* v_argIdx_457_, lean_object* v_callerIdx_458_, lean_object* v_paramIdx_459_, lean_object* v_info_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_calleeIdx_456_, v_argIdx_457_, v_callerIdx_458_, v_paramIdx_459_, v_info_460_);
lean_dec(v_callerIdx_458_);
lean_dec(v_calleeIdx_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0(lean_object* v_upperBound_462_, lean_object* v_next_463_, lean_object* v_calleeIdx_464_, lean_object* v_argIdx_465_, lean_object* v_callerIdx_466_, lean_object* v_paramIdx_467_, lean_object* v_inst_468_, lean_object* v_R_469_, lean_object* v_a_470_, lean_object* v_b_471_, lean_object* v_c_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___redArg(v_upperBound_462_, v_next_463_, v_calleeIdx_464_, v_argIdx_465_, v_callerIdx_466_, v_paramIdx_467_, v_a_470_, v_b_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0___boxed(lean_object* v_upperBound_474_, lean_object* v_next_475_, lean_object* v_calleeIdx_476_, lean_object* v_argIdx_477_, lean_object* v_callerIdx_478_, lean_object* v_paramIdx_479_, lean_object* v_inst_480_, lean_object* v_R_481_, lean_object* v_a_482_, lean_object* v_b_483_, lean_object* v_c_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__0(v_upperBound_474_, v_next_475_, v_calleeIdx_476_, v_argIdx_477_, v_callerIdx_478_, v_paramIdx_479_, v_inst_480_, v_R_481_, v_a_482_, v_b_483_, v_c_484_);
lean_dec(v_callerIdx_478_);
lean_dec(v_argIdx_477_);
lean_dec(v_calleeIdx_476_);
lean_dec(v_next_475_);
lean_dec(v_upperBound_474_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1(lean_object* v_upperBound_486_, lean_object* v_calleeIdx_487_, lean_object* v_argIdx_488_, lean_object* v_callerIdx_489_, lean_object* v_paramIdx_490_, lean_object* v_inst_491_, lean_object* v_R_492_, lean_object* v_a_493_, lean_object* v_b_494_, lean_object* v_c_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___redArg(v_upperBound_486_, v_calleeIdx_487_, v_argIdx_488_, v_callerIdx_489_, v_paramIdx_490_, v_a_493_, v_b_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1___boxed(lean_object* v_upperBound_497_, lean_object* v_calleeIdx_498_, lean_object* v_argIdx_499_, lean_object* v_callerIdx_500_, lean_object* v_paramIdx_501_, lean_object* v_inst_502_, lean_object* v_R_503_, lean_object* v_a_504_, lean_object* v_b_505_, lean_object* v_c_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__1(v_upperBound_497_, v_calleeIdx_498_, v_argIdx_499_, v_callerIdx_500_, v_paramIdx_501_, v_inst_502_, v_R_503_, v_a_504_, v_b_505_, v_c_506_);
lean_dec(v_callerIdx_500_);
lean_dec(v_argIdx_499_);
lean_dec(v_calleeIdx_498_);
lean_dec(v_upperBound_497_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2(lean_object* v_upperBound_508_, lean_object* v_val_509_, lean_object* v_calleeIdx_510_, lean_object* v_argIdx_511_, lean_object* v_inst_512_, lean_object* v_R_513_, lean_object* v_a_514_, lean_object* v_b_515_, lean_object* v_c_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v_upperBound_508_, v_val_509_, v_calleeIdx_510_, v_argIdx_511_, v_a_514_, v_b_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___boxed(lean_object* v_upperBound_518_, lean_object* v_val_519_, lean_object* v_calleeIdx_520_, lean_object* v_argIdx_521_, lean_object* v_inst_522_, lean_object* v_R_523_, lean_object* v_a_524_, lean_object* v_b_525_, lean_object* v_c_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2(v_upperBound_518_, v_val_519_, v_calleeIdx_520_, v_argIdx_521_, v_inst_522_, v_R_523_, v_a_524_, v_b_525_, v_c_526_);
lean_dec(v_calleeIdx_520_);
lean_dec_ref(v_val_519_);
lean_dec(v_upperBound_518_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_FixedParams_Info_format_spec__2(lean_object* v_a_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = lean_nat_to_int(v_a_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1_spec__1(lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_dec(v_x_530_);
return v_x_531_;
}
else
{
lean_object* v_head_533_; lean_object* v_tail_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_543_; 
v_head_533_ = lean_ctor_get(v_x_532_, 0);
v_tail_534_ = lean_ctor_get(v_x_532_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_543_ == 0)
{
v___x_536_ = v_x_532_;
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_tail_534_);
lean_inc(v_head_533_);
lean_dec(v_x_532_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
lean_inc(v_x_530_);
if (v_isShared_537_ == 0)
{
lean_ctor_set_tag(v___x_536_, 5);
lean_ctor_set(v___x_536_, 1, v_x_530_);
lean_ctor_set(v___x_536_, 0, v_x_531_);
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_x_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_x_530_);
v___x_539_ = v_reuseFailAlloc_542_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v_head_533_);
v_x_531_ = v___x_540_;
v_x_532_ = v_tail_534_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v___x_546_; 
lean_dec(v_x_545_);
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v_tail_547_; 
v_tail_547_ = lean_ctor_get(v_x_544_, 1);
if (lean_obj_tag(v_tail_547_) == 0)
{
lean_object* v_head_548_; 
lean_dec(v_x_545_);
v_head_548_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_head_548_);
lean_dec_ref_known(v_x_544_, 2);
return v_head_548_;
}
else
{
lean_object* v_head_549_; lean_object* v___x_550_; 
lean_inc(v_tail_547_);
v_head_549_ = lean_ctor_get(v_x_544_, 0);
lean_inc(v_head_549_);
lean_dec_ref_known(v_x_544_, 2);
v___x_550_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1_spec__1(v_x_545_, v_head_549_, v_tail_547_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0(lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
if (lean_obj_tag(v_a_557_) == 0)
{
lean_object* v___x_559_; 
v___x_559_ = l_List_reverse___redArg(v_a_558_);
return v___x_559_;
}
else
{
lean_object* v_head_560_; lean_object* v_tail_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_585_; 
v_head_560_ = lean_ctor_get(v_a_557_, 0);
v_tail_561_ = lean_ctor_get(v_a_557_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_585_ == 0)
{
v___x_563_ = v_a_557_;
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_tail_561_);
lean_inc(v_head_560_);
lean_dec(v_a_557_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_585_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___y_566_; 
if (lean_obj_tag(v_head_560_) == 0)
{
lean_object* v___x_571_; 
v___x_571_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__1));
v___y_566_ = v___x_571_;
goto v___jp_565_;
}
else
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_584_; 
v_val_572_ = lean_ctor_get(v_head_560_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v_head_560_);
if (v_isSharedCheck_584_ == 0)
{
v___x_574_ = v_head_560_;
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v_head_560_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_576_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0___closed__3));
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_val_572_, v___x_577_);
lean_dec(v_val_572_);
v___x_579_ = l_Nat_reprFast(v___x_578_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 3);
lean_ctor_set(v___x_574_, 0, v___x_579_);
v___x_581_ = v___x_574_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_583_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_576_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___y_566_ = v___x_582_;
goto v___jp_565_;
}
}
}
v___jp_565_:
{
lean_object* v___x_568_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v_a_558_);
lean_ctor_set(v___x_563_, 0, v___y_566_);
v___x_568_ = v___x_563_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___y_566_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_a_558_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v_a_557_ = v_tail_561_;
v_a_558_ = v___x_568_;
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
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__4));
v___x_595_ = lean_string_length(v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6, &l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6_once, _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__6);
v___x_597_ = lean_nat_to_int(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3(lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
if (lean_obj_tag(v_a_602_) == 0)
{
lean_object* v___x_604_; 
v___x_604_ = l_List_reverse___redArg(v_a_603_);
return v___x_604_;
}
else
{
lean_object* v_head_605_; lean_object* v_tail_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_631_; 
v_head_605_ = lean_ctor_get(v_a_602_, 0);
v_tail_606_ = lean_ctor_get(v_a_602_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_631_ == 0)
{
v___x_608_ = v_a_602_;
v_isShared_609_ = v_isSharedCheck_631_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_tail_606_);
lean_inc(v_head_605_);
lean_dec(v_a_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_631_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___y_611_; 
if (lean_obj_tag(v_head_605_) == 0)
{
lean_object* v___x_616_; 
v___x_616_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__1));
v___y_611_ = v___x_616_;
goto v___jp_610_;
}
else
{
lean_object* v_val_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; 
v_val_617_ = lean_ctor_get(v_head_605_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v_head_605_, 1);
v___x_618_ = lean_array_to_list(v_val_617_);
v___x_619_ = lean_box(0);
v___x_620_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__0(v___x_618_, v___x_619_);
v___x_621_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3));
v___x_622_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_620_, v___x_621_);
v___x_623_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7, &l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7_once, _init_l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__7);
v___x_624_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__8));
v___x_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_622_);
v___x_626_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_623_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = 0;
v___x_630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*1, v___x_629_);
v___y_611_ = v___x_630_;
goto v___jp_610_;
}
v___jp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v_a_603_);
lean_ctor_set(v___x_608_, 0, v___y_611_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___y_611_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_a_603_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v_a_602_ = v_tail_606_;
v_a_603_ = v___x_613_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4(lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
if (lean_obj_tag(v_a_635_) == 0)
{
lean_object* v___x_637_; 
v___x_637_ = l_List_reverse___redArg(v_a_636_);
return v___x_637_;
}
else
{
lean_object* v_head_638_; lean_object* v_tail_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_654_; 
v_head_638_ = lean_ctor_get(v_a_635_, 0);
v_tail_639_ = lean_ctor_get(v_a_635_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_635_);
if (v_isSharedCheck_654_ == 0)
{
v___x_641_ = v_a_635_;
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_tail_639_);
lean_inc(v_head_638_);
lean_dec(v_a_635_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_654_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_643_ = lean_array_to_list(v_head_638_);
v___x_644_ = lean_box(0);
v___x_645_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3(v___x_643_, v___x_644_);
v___x_646_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__3));
v___x_647_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_645_, v___x_646_);
v___x_648_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4___closed__1));
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v___x_647_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_a_636_);
lean_ctor_set(v___x_641_, 0, v___x_649_);
v___x_651_ = v___x_641_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_636_);
v___x_651_ = v_reuseFailAlloc_653_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
v_a_635_ = v_tail_639_;
v_a_636_ = v___x_651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParams_Info_format(lean_object* v_info_655_){
_start:
{
lean_object* v_graph_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_graph_656_ = lean_ctor_get(v_info_655_, 0);
lean_inc_ref(v_graph_656_);
lean_dec_ref(v_info_655_);
v___x_657_ = lean_array_to_list(v_graph_656_);
v___x_658_ = lean_box(0);
v___x_659_ = l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__4(v___x_657_, v___x_658_);
v___x_660_ = lean_box(1);
v___x_661_ = l_Std_Format_joinSep___at___00Lean_Elab_FixedParams_Info_format_spec__1(v___x_659_, v___x_660_);
return v___x_661_;
}
}
uint8_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0(lean_object* v_x_664_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = 0;
return v___x_665_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_664_ = stack[0].m_obj;
uint8_t v_res_666_;
v_res_666_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0(v_x_664_);
stack->m_num = v_res_666_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0___boxed(lean_object* v_x_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__0(v_x_667_);
lean_dec(v_x_667_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
uint8_t l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1(lean_object* v_fvarId_670_, lean_object* v_x_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = l_Lean_instBEqFVarId_beq(v_fvarId_670_, v_x_671_);
return v___x_672_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_670_ = stack[0].m_obj;
lean_object* v_x_671_ = stack[1].m_obj;
uint8_t v_res_673_;
v_res_673_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1(v_fvarId_670_, v_x_671_);
stack->m_num = v_res_673_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_674_, lean_object* v_x_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1(v_fvarId_674_, v_x_675_);
lean_dec(v_x_675_);
lean_dec(v_fvarId_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_box(0);
v___x_680_ = lean_unsigned_to_nat(16u);
v___x_681_ = lean_mk_array(v___x_680_, v___x_679_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__1);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
return v___x_684_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(lean_object* v_e_685_, lean_object* v_fvarId_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___f_689_; lean_object* v___f_690_; lean_object* v___x_691_; uint8_t v_fst_693_; lean_object* v_mctx_694_; lean_object* v___y_712_; lean_object* v_mctx_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___f_689_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0));
v___f_690_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_690_, 0, v_fvarId_686_);
v___x_691_ = lean_st_ref_get(v___y_687_);
v_mctx_717_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref_n(v_mctx_717_, 2);
lean_dec(v___x_691_);
v___x_718_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_mctx_717_);
v___x_720_ = l_Lean_Expr_hasFVar(v_e_685_);
if (v___x_720_ == 0)
{
uint8_t v___x_721_; 
v___x_721_ = l_Lean_Expr_hasMVar(v_e_685_);
if (v___x_721_ == 0)
{
lean_dec_ref_known(v___x_719_, 2);
lean_dec_ref(v___f_690_);
lean_dec_ref(v_e_685_);
v_fst_693_ = v___x_721_;
v_mctx_694_ = v_mctx_717_;
goto v___jp_692_;
}
else
{
lean_object* v___x_722_; 
lean_dec_ref(v_mctx_717_);
v___x_722_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_690_, v___f_689_, v_e_685_, v___x_719_);
v___y_712_ = v___x_722_;
goto v___jp_711_;
}
}
else
{
lean_object* v___x_723_; 
lean_dec_ref(v_mctx_717_);
v___x_723_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_690_, v___f_689_, v_e_685_, v___x_719_);
v___y_712_ = v___x_723_;
goto v___jp_711_;
}
v___jp_692_:
{
lean_object* v___x_695_; lean_object* v_cache_696_; lean_object* v_zetaDeltaFVarIds_697_; lean_object* v_postponed_698_; lean_object* v_diag_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_709_; 
v___x_695_ = lean_st_ref_take(v___y_687_);
v_cache_696_ = lean_ctor_get(v___x_695_, 1);
v_zetaDeltaFVarIds_697_ = lean_ctor_get(v___x_695_, 2);
v_postponed_698_ = lean_ctor_get(v___x_695_, 3);
v_diag_699_ = lean_ctor_get(v___x_695_, 4);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_710_);
v___x_701_ = v___x_695_;
v_isShared_702_ = v_isSharedCheck_709_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_diag_699_);
lean_inc(v_postponed_698_);
lean_inc(v_zetaDeltaFVarIds_697_);
lean_inc(v_cache_696_);
lean_dec(v___x_695_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_709_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v_mctx_694_);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_mctx_694_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_cache_696_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_zetaDeltaFVarIds_697_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_postponed_698_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v_diag_699_);
v___x_704_ = v_reuseFailAlloc_708_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_st_ref_put(v___y_687_, v___x_704_);
v___x_706_ = lean_box(v_fst_693_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
}
v___jp_711_:
{
lean_object* v_snd_713_; lean_object* v_fst_714_; lean_object* v_mctx_715_; uint8_t v___x_716_; 
v_snd_713_ = lean_ctor_get(v___y_712_, 1);
lean_inc(v_snd_713_);
v_fst_714_ = lean_ctor_get(v___y_712_, 0);
lean_inc(v_fst_714_);
lean_dec_ref(v___y_712_);
v_mctx_715_ = lean_ctor_get(v_snd_713_, 1);
lean_inc_ref(v_mctx_715_);
lean_dec(v_snd_713_);
v___x_716_ = lean_unbox(v_fst_714_);
lean_dec(v_fst_714_);
v_fst_693_ = v___x_716_;
v_mctx_694_ = v_mctx_715_;
goto v___jp_692_;
}
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_685_ = stack[0].m_obj;
lean_object* v_fvarId_686_ = stack[1].m_obj;
lean_object* v___y_687_ = stack[2].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_685_, v_fvarId_686_, v___y_687_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___boxed(lean_object* v_e_725_, lean_object* v_fvarId_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_725_, v_fvarId_726_, v___y_727_);
lean_dec(v___y_727_);
return v_res_729_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(lean_object* v_e_730_, lean_object* v_fvarId_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_e_730_, v_fvarId_731_, v___y_733_);
return v___x_737_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_730_ = stack[0].m_obj;
lean_object* v_fvarId_731_ = stack[1].m_obj;
lean_object* v___y_732_ = stack[2].m_obj;
lean_object* v___y_733_ = stack[3].m_obj;
lean_object* v___y_734_ = stack[4].m_obj;
lean_object* v___y_735_ = stack[5].m_obj;
lean_object* v_res_738_;
v_res_738_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(v_e_730_, v_fvarId_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___boxed(lean_object* v_e_739_, lean_object* v_fvarId_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0(v_e_739_, v_fvarId_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_746_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(lean_object* v_k_747_, lean_object* v_b_748_, lean_object* v_c_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
v___x_755_ = lean_apply_7(v_k_747_, v_b_748_, v_c_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, lean_box(0));
return v___x_755_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_747_ = stack[0].m_obj;
lean_object* v_b_748_ = stack[1].m_obj;
lean_object* v_c_749_ = stack[2].m_obj;
lean_object* v___y_750_ = stack[3].m_obj;
lean_object* v___y_751_ = stack[4].m_obj;
lean_object* v___y_752_ = stack[5].m_obj;
lean_object* v___y_753_ = stack[6].m_obj;
lean_object* v_res_756_;
v_res_756_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(v_k_747_, v_b_748_, v_c_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
stack->m_obj
 = v_res_756_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed(lean_object* v_k_757_, lean_object* v_b_758_, lean_object* v_c_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0(v_k_757_, v_b_758_, v_c_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_765_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(lean_object* v_e_766_, lean_object* v_k_767_, uint8_t v_cleanupAnnotations_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___f_774_; uint8_t v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___f_774_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_774_, 0, v_k_767_);
v___x_775_ = 1;
v___x_776_ = 0;
v___x_777_ = lean_box(0);
v___x_778_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_766_, v___x_775_, v___x_776_, v___x_775_, v___x_776_, v___x_777_, v___f_774_, v_cleanupAnnotations_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_778_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_778_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_766_ = stack[0].m_obj;
lean_object* v_k_767_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_768_ = stack[2].m_num;
lean_object* v___y_769_ = stack[3].m_obj;
lean_object* v___y_770_ = stack[4].m_obj;
lean_object* v___y_771_ = stack[5].m_obj;
lean_object* v___y_772_ = stack[6].m_obj;
lean_object* v_res_795_;
v_res_795_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_766_, v_k_767_, v_cleanupAnnotations_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
stack->m_obj
 = v_res_795_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___boxed(lean_object* v_e_796_, lean_object* v_k_797_, lean_object* v_cleanupAnnotations_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_804_; lean_object* v_res_805_; 
v_cleanupAnnotations_boxed_804_ = lean_unbox(v_cleanupAnnotations_798_);
v_res_805_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_796_, v_k_797_, v_cleanupAnnotations_boxed_804_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_805_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(lean_object* v_00_u03b1_806_, lean_object* v_e_807_, lean_object* v_k_808_, uint8_t v_cleanupAnnotations_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_e_807_, v_k_808_, v_cleanupAnnotations_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_807_ = stack[1].m_obj;
lean_object* v_k_808_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_809_ = stack[3].m_num;
lean_object* v___y_810_ = stack[4].m_obj;
lean_object* v___y_811_ = stack[5].m_obj;
lean_object* v___y_812_ = stack[6].m_obj;
lean_object* v___y_813_ = stack[7].m_obj;
lean_object* v_res_816_;
v_res_816_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(lean_box(0), v_e_807_, v_k_808_, v_cleanupAnnotations_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
stack->m_obj
 = v_res_816_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___boxed(lean_object* v_00_u03b1_817_, lean_object* v_e_818_, lean_object* v_k_819_, lean_object* v_cleanupAnnotations_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_826_; lean_object* v_res_827_; 
v_cleanupAnnotations_boxed_826_ = lean_unbox(v_cleanupAnnotations_820_);
v_res_827_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3(v_00_u03b1_817_, v_e_818_, v_k_819_, v_cleanupAnnotations_boxed_826_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_827_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(lean_object* v_upperBound_828_, lean_object* v_xs_829_, lean_object* v_next_830_, lean_object* v_a_831_, lean_object* v_b_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_a_839_; uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_lt(v_a_831_, v_upperBound_828_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v_a_831_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_b_832_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_array_fget_borrowed(v_xs_829_, v_a_831_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___x_845_);
v___x_846_ = lean_infer_type(v___x_845_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_array_fget_borrowed(v_xs_829_, v_next_830_);
v___x_849_ = l_Lean_Expr_fvarId_x21(v___x_848_);
v___x_850_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_a_847_, v___x_849_, v___y_834_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; uint8_t v___x_852_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = lean_unbox(v_a_851_);
lean_dec(v_a_851_);
if (v___x_852_ == 0)
{
v_a_839_ = v_b_832_;
goto v___jp_838_;
}
else
{
lean_object* v___x_853_; 
lean_inc(v_a_831_);
v___x_853_ = lean_array_push(v_b_832_, v_a_831_);
v_a_839_ = v___x_853_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec_ref(v_b_832_);
lean_dec(v_a_831_);
v_a_854_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_850_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_850_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v_b_832_);
lean_dec(v_a_831_);
v_a_862_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_846_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_846_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
v___jp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_a_831_, v___x_840_);
lean_dec(v_a_831_);
v_a_831_ = v___x_841_;
v_b_832_ = v_a_839_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_828_ = stack[0].m_obj;
lean_object* v_xs_829_ = stack[1].m_obj;
lean_object* v_next_830_ = stack[2].m_obj;
lean_object* v_a_831_ = stack[3].m_obj;
lean_object* v_b_832_ = stack[4].m_obj;
lean_object* v___y_833_ = stack[5].m_obj;
lean_object* v___y_834_ = stack[6].m_obj;
lean_object* v___y_835_ = stack[7].m_obj;
lean_object* v___y_836_ = stack[8].m_obj;
lean_object* v_res_870_;
v_res_870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_828_, v_xs_829_, v_next_830_, v_a_831_, v_b_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg___boxed(lean_object* v_upperBound_871_, lean_object* v_xs_872_, lean_object* v_next_873_, lean_object* v_a_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_871_, v_xs_872_, v_next_873_, v_a_874_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v_next_873_);
lean_dec_ref(v_xs_872_);
lean_dec(v_upperBound_871_);
return v_res_881_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(lean_object* v_upperBound_884_, lean_object* v___x_885_, lean_object* v_xs_886_, lean_object* v_a_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
uint8_t v___x_894_; 
v___x_894_ = lean_nat_dec_lt(v_a_887_, v_upperBound_884_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v_a_887_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_b_888_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_add(v_a_887_, v___x_896_);
v___x_898_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___closed__0));
lean_inc(v___x_897_);
v___x_899_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v___x_885_, v_xs_886_, v_a_887_, v___x_897_, v___x_898_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v_a_887_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = lean_array_push(v_b_888_, v_a_900_);
v_a_887_ = v___x_897_;
v_b_888_ = v___x_901_;
goto _start;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v___x_897_);
lean_dec_ref(v_b_888_);
v_a_903_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_899_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_899_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_884_ = stack[0].m_obj;
lean_object* v___x_885_ = stack[1].m_obj;
lean_object* v_xs_886_ = stack[2].m_obj;
lean_object* v_a_887_ = stack[3].m_obj;
lean_object* v_b_888_ = stack[4].m_obj;
lean_object* v___y_889_ = stack[5].m_obj;
lean_object* v___y_890_ = stack[6].m_obj;
lean_object* v___y_891_ = stack[7].m_obj;
lean_object* v___y_892_ = stack[8].m_obj;
lean_object* v_res_911_;
v_res_911_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_884_, v___x_885_, v_xs_886_, v_a_887_, v_b_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg___boxed(lean_object* v_upperBound_912_, lean_object* v___x_913_, lean_object* v_xs_914_, lean_object* v_a_915_, lean_object* v_b_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_912_, v___x_913_, v_xs_914_, v_a_915_, v_b_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec_ref(v_xs_914_);
lean_dec(v___x_913_);
lean_dec(v_upperBound_912_);
return v_res_922_;
}
}
lean_object* l_Lean_Elab_getParamRevDeps___lam__0(lean_object* v_xs_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_revDeps_934_; lean_object* v___x_935_; 
v___x_932_ = lean_array_get_size(v_xs_925_);
v___x_933_ = lean_unsigned_to_nat(0u);
v_revDeps_934_ = ((lean_object*)(l_Lean_Elab_getParamRevDeps___lam__0___closed__0));
v___x_935_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v___x_932_, v___x_932_, v_xs_925_, v___x_933_, v_revDeps_934_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_935_;
}
}
LEAN_EXPORT void l_Lean_Elab_getParamRevDeps___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_925_ = stack[0].m_obj;
lean_object* v_x_926_ = stack[1].m_obj;
lean_object* v___y_927_ = stack[2].m_obj;
lean_object* v___y_928_ = stack[3].m_obj;
lean_object* v___y_929_ = stack[4].m_obj;
lean_object* v___y_930_ = stack[5].m_obj;
lean_object* v_res_936_;
v_res_936_ = l_Lean_Elab_getParamRevDeps___lam__0(v_xs_925_, v_x_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
stack->m_obj
 = v_res_936_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___lam__0___boxed(lean_object* v_xs_937_, lean_object* v_x_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Elab_getParamRevDeps___lam__0(v_xs_937_, v_x_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec_ref(v_x_938_);
lean_dec_ref(v_xs_937_);
return v_res_944_;
}
}
lean_object* l_Lean_Elab_getParamRevDeps(lean_object* v_value_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___f_952_; uint8_t v___x_953_; lean_object* v___x_954_; 
v___f_952_ = ((lean_object*)(l_Lean_Elab_getParamRevDeps___closed__0));
v___x_953_ = 1;
v___x_954_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_946_, v___f_952_, v___x_953_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_954_;
}
}
LEAN_EXPORT void l_Lean_Elab_getParamRevDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_946_ = stack[0].m_obj;
lean_object* v_a_947_ = stack[1].m_obj;
lean_object* v_a_948_ = stack[2].m_obj;
lean_object* v_a_949_ = stack[3].m_obj;
lean_object* v_a_950_ = stack[4].m_obj;
lean_object* v_res_955_;
v_res_955_ = l_Lean_Elab_getParamRevDeps(v_value_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
stack->m_obj
 = v_res_955_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getParamRevDeps___boxed(lean_object* v_value_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Elab_getParamRevDeps(v_value_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_962_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(lean_object* v_upperBound_963_, lean_object* v_xs_964_, lean_object* v_next_965_, lean_object* v_inst_966_, lean_object* v_R_967_, lean_object* v_a_968_, lean_object* v_b_969_, lean_object* v_c_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___redArg(v_upperBound_963_, v_xs_964_, v_next_965_, v_a_968_, v_b_969_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
return v___x_976_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_963_ = stack[0].m_obj;
lean_object* v_xs_964_ = stack[1].m_obj;
lean_object* v_next_965_ = stack[2].m_obj;
lean_object* v_a_968_ = stack[5].m_obj;
lean_object* v_b_969_ = stack[6].m_obj;
lean_object* v___y_971_ = stack[8].m_obj;
lean_object* v___y_972_ = stack[9].m_obj;
lean_object* v___y_973_ = stack[10].m_obj;
lean_object* v___y_974_ = stack[11].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(v_upperBound_963_, v_xs_964_, v_next_965_, lean_box(0), lean_box(0), v_a_968_, v_b_969_, lean_box(0), v___y_971_, v___y_972_, v___y_973_, v___y_974_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1___boxed(lean_object* v_upperBound_978_, lean_object* v_xs_979_, lean_object* v_next_980_, lean_object* v_inst_981_, lean_object* v_R_982_, lean_object* v_a_983_, lean_object* v_b_984_, lean_object* v_c_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__1(v_upperBound_978_, v_xs_979_, v_next_980_, v_inst_981_, v_R_982_, v_a_983_, v_b_984_, v_c_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v_next_980_);
lean_dec_ref(v_xs_979_);
lean_dec(v_upperBound_978_);
return v_res_991_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(lean_object* v_upperBound_992_, lean_object* v___x_993_, lean_object* v_xs_994_, lean_object* v_inst_995_, lean_object* v_R_996_, lean_object* v_a_997_, lean_object* v_b_998_, lean_object* v_c_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___redArg(v_upperBound_992_, v___x_993_, v_xs_994_, v_a_997_, v_b_998_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_992_ = stack[0].m_obj;
lean_object* v___x_993_ = stack[1].m_obj;
lean_object* v_xs_994_ = stack[2].m_obj;
lean_object* v_a_997_ = stack[5].m_obj;
lean_object* v_b_998_ = stack[6].m_obj;
lean_object* v___y_1000_ = stack[8].m_obj;
lean_object* v___y_1001_ = stack[9].m_obj;
lean_object* v___y_1002_ = stack[10].m_obj;
lean_object* v___y_1003_ = stack[11].m_obj;
lean_object* v_res_1006_;
v_res_1006_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(v_upperBound_992_, v___x_993_, v_xs_994_, lean_box(0), lean_box(0), v_a_997_, v_b_998_, lean_box(0), v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2___boxed(lean_object* v_upperBound_1007_, lean_object* v___x_1008_, lean_object* v_xs_1009_, lean_object* v_inst_1010_, lean_object* v_R_1011_, lean_object* v_a_1012_, lean_object* v_b_1013_, lean_object* v_c_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getParamRevDeps_spec__2(v_upperBound_1007_, v___x_1008_, v_xs_1009_, v_inst_1010_, v_R_1011_, v_a_1012_, v_b_1013_, v_c_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec_ref(v_xs_1009_);
lean_dec(v___x_1008_);
lean_dec(v_upperBound_1007_);
return v_res_1020_;
}
}
lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___f_1028_; lean_object* v___x_27265__overap_1029_; lean_object* v___x_1030_; 
v___f_1028_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_27265__overap_1029_ = lean_panic_fn_borrowed(v___f_1028_, v_msg_1022_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
v___x_1030_ = lean_apply_5(v___x_27265__overap_1029_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, lean_box(0));
return v___x_1030_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1022_ = stack[0].m_obj;
lean_object* v___y_1023_ = stack[1].m_obj;
lean_object* v___y_1024_ = stack[2].m_obj;
lean_object* v___y_1025_ = stack[3].m_obj;
lean_object* v___y_1026_ = stack[4].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_msg_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
stack->m_obj
 = v_res_1031_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___boxed(lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(size_t v_sz_1039_, size_t v_i_1040_, lean_object* v_bs_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_usize_dec_lt(v_i_1040_, v_sz_1039_);
if (v___x_1042_ == 0)
{
return v_bs_1041_;
}
else
{
lean_object* v_v_1043_; lean_object* v___x_1044_; lean_object* v_bs_x27_1045_; lean_object* v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v_v_1043_ = lean_array_uget(v_bs_1041_, v_i_1040_);
v___x_1044_ = lean_unsigned_to_nat(0u);
v_bs_x27_1045_ = lean_array_uset(v_bs_1041_, v_i_1040_, v___x_1044_);
v___x_1046_ = lean_array_get_size(v_v_1043_);
lean_dec(v_v_1043_);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_add(v_i_1040_, v___x_1047_);
v___x_1049_ = lean_array_uset(v_bs_x27_1045_, v_i_1040_, v___x_1046_);
v_i_1040_ = v___x_1048_;
v_bs_1041_ = v___x_1049_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1039_ = stack[0].m_num;
size_t v_i_1040_ = stack[1].m_num;
lean_object* v_bs_1041_ = stack[2].m_obj;
lean_object* v_res_1051_;
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_1039_, v_i_1040_, v_bs_1041_);
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1___boxed(lean_object* v_sz_1052_, lean_object* v_i_1053_, lean_object* v_bs_1054_){
_start:
{
size_t v_sz_boxed_1055_; size_t v_i_boxed_1056_; lean_object* v_res_1057_; 
v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1056_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_boxed_1055_, v_i_boxed_1056_, v_bs_1054_);
return v_res_1057_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(size_t v_sz_1058_, size_t v_i_1059_, lean_object* v_bs_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_usize_dec_lt(v_i_1059_, v_sz_1058_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_bs_1060_);
return v___x_1067_;
}
else
{
lean_object* v_v_1068_; lean_object* v_value_1069_; lean_object* v___x_1070_; lean_object* v_bs_x27_1071_; lean_object* v___x_1072_; 
v_v_1068_ = lean_array_uget_borrowed(v_bs_1060_, v_i_1059_);
v_value_1069_ = lean_ctor_get(v_v_1068_, 7);
lean_inc_ref(v_value_1069_);
v___x_1070_ = lean_unsigned_to_nat(0u);
v_bs_x27_1071_ = lean_array_uset(v_bs_1060_, v_i_1059_, v___x_1070_);
v___x_1072_ = l_Lean_Elab_getParamRevDeps(v_value_1069_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; size_t v___x_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = ((size_t)1ULL);
v___x_1075_ = lean_usize_add(v_i_1059_, v___x_1074_);
v___x_1076_ = lean_array_uset(v_bs_x27_1071_, v_i_1059_, v_a_1073_);
v_i_1059_ = v___x_1075_;
v_bs_1060_ = v___x_1076_;
goto _start;
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v_bs_x27_1071_);
v_a_1078_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1072_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1072_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1058_ = stack[0].m_num;
size_t v_i_1059_ = stack[1].m_num;
lean_object* v_bs_1060_ = stack[2].m_obj;
lean_object* v___y_1061_ = stack[3].m_obj;
lean_object* v___y_1062_ = stack[4].m_obj;
lean_object* v___y_1063_ = stack[5].m_obj;
lean_object* v___y_1064_ = stack[6].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_1058_, v_i_1059_, v_bs_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0___boxed(lean_object* v_sz_1087_, lean_object* v_i_1088_, lean_object* v_bs_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
size_t v_sz_boxed_1095_; size_t v_i_boxed_1096_; lean_object* v_res_1097_; 
v_sz_boxed_1095_ = lean_unbox_usize(v_sz_1087_);
lean_dec(v_sz_1087_);
v_i_boxed_1096_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_boxed_1095_, v_i_boxed_1096_, v_bs_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1097_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(lean_object* v_msgData_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v_env_1105_; uint8_t v___x_1106_; lean_object* v_env_1107_; lean_object* v___x_1108_; lean_object* v_toCold_1109_; lean_object* v_mctx_1110_; lean_object* v_lctx_1111_; lean_object* v_options_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1104_ = lean_st_ref_get(v___y_1102_);
v_env_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_env_1105_);
lean_dec(v___x_1104_);
v___x_1106_ = 0;
v_env_1107_ = l_Lean_Environment_setRecordingDeps(v_env_1105_, v___x_1106_);
v___x_1108_ = lean_st_ref_get(v___y_1100_);
v_toCold_1109_ = lean_ctor_get(v___y_1101_, 0);
v_mctx_1110_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_mctx_1110_);
lean_dec(v___x_1108_);
v_lctx_1111_ = lean_ctor_get(v___y_1099_, 2);
v_options_1112_ = lean_ctor_get(v_toCold_1109_, 2);
lean_inc_ref(v_options_1112_);
lean_inc_ref(v_lctx_1111_);
v___x_1113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1113_, 0, v_env_1107_);
lean_ctor_set(v___x_1113_, 1, v_mctx_1110_);
lean_ctor_set(v___x_1113_, 2, v_lctx_1111_);
lean_ctor_set(v___x_1113_, 3, v_options_1112_);
v___x_1114_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_msgData_1098_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1098_ = stack[0].m_obj;
lean_object* v___y_1099_ = stack[1].m_obj;
lean_object* v___y_1100_ = stack[2].m_obj;
lean_object* v___y_1101_ = stack[3].m_obj;
lean_object* v___y_1102_ = stack[4].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msgData_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2___boxed(lean_object* v_msgData_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msgData_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1124_; double v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_float_of_nat(v___x_1124_);
return v___x_1125_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(lean_object* v_cls_1129_, lean_object* v_msg_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_ref_1136_; lean_object* v___x_1137_; lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1183_; 
v_ref_1136_ = lean_ctor_get(v___y_1133_, 2);
v___x_1137_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1183_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1183_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v_traceState_1143_; lean_object* v_env_1144_; lean_object* v_nextMacroScope_1145_; lean_object* v_ngen_1146_; lean_object* v_auxDeclNGen_1147_; lean_object* v_cache_1148_; lean_object* v_recordedDeps_1149_; lean_object* v_messages_1150_; lean_object* v_infoState_1151_; lean_object* v_snapshotTasks_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1182_; 
v___x_1142_ = lean_st_ref_take(v___y_1134_);
v_traceState_1143_ = lean_ctor_get(v___x_1142_, 4);
v_env_1144_ = lean_ctor_get(v___x_1142_, 0);
v_nextMacroScope_1145_ = lean_ctor_get(v___x_1142_, 1);
v_ngen_1146_ = lean_ctor_get(v___x_1142_, 2);
v_auxDeclNGen_1147_ = lean_ctor_get(v___x_1142_, 3);
v_cache_1148_ = lean_ctor_get(v___x_1142_, 5);
v_recordedDeps_1149_ = lean_ctor_get(v___x_1142_, 6);
v_messages_1150_ = lean_ctor_get(v___x_1142_, 7);
v_infoState_1151_ = lean_ctor_get(v___x_1142_, 8);
v_snapshotTasks_1152_ = lean_ctor_get(v___x_1142_, 9);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1154_ = v___x_1142_;
v_isShared_1155_ = v_isSharedCheck_1182_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snapshotTasks_1152_);
lean_inc(v_infoState_1151_);
lean_inc(v_messages_1150_);
lean_inc(v_recordedDeps_1149_);
lean_inc(v_cache_1148_);
lean_inc(v_traceState_1143_);
lean_inc(v_auxDeclNGen_1147_);
lean_inc(v_ngen_1146_);
lean_inc(v_nextMacroScope_1145_);
lean_inc(v_env_1144_);
lean_dec(v___x_1142_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1182_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
uint64_t v_tid_1156_; lean_object* v_traces_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1181_; 
v_tid_1156_ = lean_ctor_get_uint64(v_traceState_1143_, sizeof(void*)*1);
v_traces_1157_ = lean_ctor_get(v_traceState_1143_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_traceState_1143_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1159_ = v_traceState_1143_;
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_traces_1157_);
lean_dec(v_traceState_1143_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; double v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_1164_ = 0;
v___x_1165_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_1166_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1166_, 0, v_cls_1129_);
lean_ctor_set(v___x_1166_, 1, v___x_1162_);
lean_ctor_set(v___x_1166_, 2, v___x_1165_);
lean_ctor_set_float(v___x_1166_, sizeof(void*)*3, v___x_1163_);
lean_ctor_set_float(v___x_1166_, sizeof(void*)*3 + 8, v___x_1163_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*3 + 16, v___x_1164_);
v___x_1167_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_1168_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v_a_1138_);
lean_ctor_set(v___x_1168_, 2, v___x_1167_);
lean_inc(v_ref_1136_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_ref_1136_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_PersistentArray_push___redArg(v_traces_1157_, v___x_1169_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1170_);
v___x_1172_ = v___x_1159_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1170_);
lean_ctor_set_uint64(v_reuseFailAlloc_1180_, sizeof(void*)*1, v_tid_1156_);
v___x_1172_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 4, v___x_1172_);
v___x_1174_ = v___x_1154_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_env_1144_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_nextMacroScope_1145_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_ngen_1146_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_auxDeclNGen_1147_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_cache_1148_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_recordedDeps_1149_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v_messages_1150_);
lean_ctor_set(v_reuseFailAlloc_1179_, 8, v_infoState_1151_);
lean_ctor_set(v_reuseFailAlloc_1179_, 9, v_snapshotTasks_1152_);
v___x_1174_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_st_ref_put(v___y_1134_, v___x_1174_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1161_);
v___x_1177_ = v___x_1140_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1161_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1129_ = stack[0].m_obj;
lean_object* v_msg_1130_ = stack[1].m_obj;
lean_object* v___y_1131_ = stack[2].m_obj;
lean_object* v___y_1132_ = stack[3].m_obj;
lean_object* v___y_1133_ = stack[4].m_obj;
lean_object* v___y_1134_ = stack[5].m_obj;
lean_object* v_res_1184_;
v_res_1184_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_1129_, v_msg_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
stack->m_obj
 = v_res_1184_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_1185_, lean_object* v_msg_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_1185_, v_msg_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1192_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object* v_00_u03b1_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_apply_1(v_x_1194_, lean_box(0));
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1194_ = stack[1].m_obj;
lean_object* v___y_1195_ = stack[2].m_obj;
lean_object* v___y_1196_ = stack[3].m_obj;
lean_object* v___y_1197_ = stack[4].m_obj;
lean_object* v___y_1198_ = stack[5].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v_x_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(v_00_u03b1_1203_, v_x_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object* v_x_1211_, lean_object* v_x_1212_){
_start:
{
if (lean_obj_tag(v_x_1212_) == 0)
{
return v_x_1211_;
}
else
{
lean_object* v_key_1213_; lean_object* v_value_1214_; lean_object* v_tail_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1238_; 
v_key_1213_ = lean_ctor_get(v_x_1212_, 0);
v_value_1214_ = lean_ctor_get(v_x_1212_, 1);
v_tail_1215_ = lean_ctor_get(v_x_1212_, 2);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1212_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1217_ = v_x_1212_;
v_isShared_1218_ = v_isSharedCheck_1238_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_tail_1215_);
lean_inc(v_value_1214_);
lean_inc(v_key_1213_);
lean_dec(v_x_1212_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1238_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; uint64_t v___x_1220_; uint64_t v___x_1221_; uint64_t v___x_1222_; uint64_t v_fold_1223_; uint64_t v___x_1224_; uint64_t v___x_1225_; uint64_t v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1219_ = lean_array_get_size(v_x_1211_);
v___x_1220_ = l_Lean_ExprStructEq_hash(v_key_1213_);
v___x_1221_ = 32ULL;
v___x_1222_ = lean_uint64_shift_right(v___x_1220_, v___x_1221_);
v_fold_1223_ = lean_uint64_xor(v___x_1220_, v___x_1222_);
v___x_1224_ = 16ULL;
v___x_1225_ = lean_uint64_shift_right(v_fold_1223_, v___x_1224_);
v___x_1226_ = lean_uint64_xor(v_fold_1223_, v___x_1225_);
v___x_1227_ = lean_uint64_to_usize(v___x_1226_);
v___x_1228_ = lean_usize_of_nat(v___x_1219_);
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_sub(v___x_1228_, v___x_1229_);
v___x_1231_ = lean_usize_land(v___x_1227_, v___x_1230_);
v___x_1232_ = lean_array_uget_borrowed(v_x_1211_, v___x_1231_);
lean_inc(v___x_1232_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 2, v___x_1232_);
v___x_1234_ = v___x_1217_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_key_1213_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_value_1214_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_array_uset(v_x_1211_, v___x_1231_, v___x_1234_);
v_x_1211_ = v___x_1235_;
v_x_1212_ = v_tail_1215_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object* v_i_1239_, lean_object* v_source_1240_, lean_object* v_target_1241_){
_start:
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_array_get_size(v_source_1240_);
v___x_1243_ = lean_nat_dec_lt(v_i_1239_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v_source_1240_);
lean_dec(v_i_1239_);
return v_target_1241_;
}
else
{
lean_object* v_es_1244_; lean_object* v___x_1245_; lean_object* v_source_1246_; lean_object* v_target_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_es_1244_ = lean_array_fget(v_source_1240_, v_i_1239_);
v___x_1245_ = lean_box(0);
v_source_1246_ = lean_array_fset(v_source_1240_, v_i_1239_, v___x_1245_);
v_target_1247_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_target_1241_, v_es_1244_);
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v_i_1239_, v___x_1248_);
lean_dec(v_i_1239_);
v_i_1239_ = v___x_1249_;
v_source_1240_ = v_source_1246_;
v_target_1241_ = v_target_1247_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object* v_data_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_nbuckets_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1252_ = lean_array_get_size(v_data_1251_);
v___x_1253_ = lean_unsigned_to_nat(2u);
v_nbuckets_1254_ = lean_nat_mul(v___x_1252_, v___x_1253_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_box(0);
v___x_1257_ = lean_mk_array(v_nbuckets_1254_, v___x_1256_);
v___x_1258_ = lean_array_propagate_mark(v_data_1251_, v___x_1257_);
v___x_1259_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1255_, v_data_1251_, v___x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object* v_a_1260_, lean_object* v_b_1261_, lean_object* v_x_1262_){
_start:
{
if (lean_obj_tag(v_x_1262_) == 0)
{
lean_dec(v_b_1261_);
lean_dec_ref(v_a_1260_);
return v_x_1262_;
}
else
{
lean_object* v_key_1263_; lean_object* v_value_1264_; lean_object* v_tail_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1277_; 
v_key_1263_ = lean_ctor_get(v_x_1262_, 0);
v_value_1264_ = lean_ctor_get(v_x_1262_, 1);
v_tail_1265_ = lean_ctor_get(v_x_1262_, 2);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_x_1262_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1267_ = v_x_1262_;
v_isShared_1268_ = v_isSharedCheck_1277_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_tail_1265_);
lean_inc(v_value_1264_);
lean_inc(v_key_1263_);
lean_dec(v_x_1262_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1277_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
uint8_t v___x_1269_; 
v___x_1269_ = l_Lean_ExprStructEq_beq(v_key_1263_, v_a_1260_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1260_, v_b_1261_, v_tail_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 2, v___x_1270_);
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_key_1263_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_value_1264_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_value_1264_);
lean_dec(v_key_1263_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v_b_1261_);
lean_ctor_set(v___x_1267_, 0, v_a_1260_);
v___x_1275_ = v___x_1267_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1260_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_b_1261_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_tail_1265_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_a_1278_, lean_object* v_x_1279_){
_start:
{
if (lean_obj_tag(v_x_1279_) == 0)
{
uint8_t v___x_1280_; 
v___x_1280_ = 0;
return v___x_1280_;
}
else
{
lean_object* v_key_1281_; lean_object* v_tail_1282_; uint8_t v___x_1283_; 
v_key_1281_ = lean_ctor_get(v_x_1279_, 0);
v_tail_1282_ = lean_ctor_get(v_x_1279_, 2);
v___x_1283_ = l_Lean_ExprStructEq_beq(v_key_1281_, v_a_1278_);
if (v___x_1283_ == 0)
{
v_x_1279_ = v_tail_1282_;
goto _start;
}
else
{
return v___x_1283_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1278_ = stack[0].m_obj;
lean_object* v_x_1279_ = stack[1].m_obj;
uint8_t v_res_1285_;
v_res_1285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1278_, v_x_1279_);
stack->m_num = v_res_1285_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_a_1286_, lean_object* v_x_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1286_, v_x_1287_);
lean_dec(v_x_1287_);
lean_dec_ref(v_a_1286_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1290_, lean_object* v_a_1291_, lean_object* v_b_1292_){
_start:
{
lean_object* v_size_1293_; lean_object* v_buckets_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1337_; 
v_size_1293_ = lean_ctor_get(v_m_1290_, 0);
v_buckets_1294_ = lean_ctor_get(v_m_1290_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_m_1290_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1296_ = v_m_1290_;
v_isShared_1297_ = v_isSharedCheck_1337_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_buckets_1294_);
lean_inc(v_size_1293_);
lean_dec(v_m_1290_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1337_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; uint64_t v___x_1299_; uint64_t v___x_1300_; uint64_t v___x_1301_; uint64_t v_fold_1302_; uint64_t v___x_1303_; uint64_t v___x_1304_; uint64_t v___x_1305_; size_t v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; lean_object* v_bkt_1311_; uint8_t v___x_1312_; 
v___x_1298_ = lean_array_get_size(v_buckets_1294_);
v___x_1299_ = l_Lean_ExprStructEq_hash(v_a_1291_);
v___x_1300_ = 32ULL;
v___x_1301_ = lean_uint64_shift_right(v___x_1299_, v___x_1300_);
v_fold_1302_ = lean_uint64_xor(v___x_1299_, v___x_1301_);
v___x_1303_ = 16ULL;
v___x_1304_ = lean_uint64_shift_right(v_fold_1302_, v___x_1303_);
v___x_1305_ = lean_uint64_xor(v_fold_1302_, v___x_1304_);
v___x_1306_ = lean_uint64_to_usize(v___x_1305_);
v___x_1307_ = lean_usize_of_nat(v___x_1298_);
v___x_1308_ = ((size_t)1ULL);
v___x_1309_ = lean_usize_sub(v___x_1307_, v___x_1308_);
v___x_1310_ = lean_usize_land(v___x_1306_, v___x_1309_);
v_bkt_1311_ = lean_array_uget_borrowed(v_buckets_1294_, v___x_1310_);
v___x_1312_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1291_, v_bkt_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; lean_object* v_size_x27_1314_; lean_object* v___x_1315_; lean_object* v_buckets_x27_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1313_ = lean_unsigned_to_nat(1u);
v_size_x27_1314_ = lean_nat_add(v_size_1293_, v___x_1313_);
lean_dec(v_size_1293_);
lean_inc(v_bkt_1311_);
v___x_1315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1315_, 0, v_a_1291_);
lean_ctor_set(v___x_1315_, 1, v_b_1292_);
lean_ctor_set(v___x_1315_, 2, v_bkt_1311_);
v_buckets_x27_1316_ = lean_array_uset(v_buckets_1294_, v___x_1310_, v___x_1315_);
v___x_1317_ = lean_unsigned_to_nat(4u);
v___x_1318_ = lean_nat_mul(v_size_x27_1314_, v___x_1317_);
v___x_1319_ = lean_unsigned_to_nat(3u);
v___x_1320_ = lean_nat_div(v___x_1318_, v___x_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_array_get_size(v_buckets_x27_1316_);
v___x_1322_ = lean_nat_dec_le(v___x_1320_, v___x_1321_);
lean_dec(v___x_1320_);
if (v___x_1322_ == 0)
{
lean_object* v_val_1323_; lean_object* v___x_1325_; 
v_val_1323_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_buckets_x27_1316_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v_val_1323_);
lean_ctor_set(v___x_1296_, 0, v_size_x27_1314_);
v___x_1325_ = v___x_1296_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_size_x27_1314_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_val_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
else
{
lean_object* v___x_1328_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v_buckets_x27_1316_);
lean_ctor_set(v___x_1296_, 0, v_size_x27_1314_);
v___x_1328_ = v___x_1296_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_size_x27_1314_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_buckets_x27_1316_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v___x_1330_; lean_object* v_buckets_x27_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
lean_inc(v_bkt_1311_);
v___x_1330_ = lean_box(0);
v_buckets_x27_1331_ = lean_array_uset(v_buckets_1294_, v___x_1310_, v___x_1330_);
v___x_1332_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1291_, v_b_1292_, v_bkt_1311_);
v___x_1333_ = lean_array_uset(v_buckets_x27_1331_, v___x_1310_, v___x_1332_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v___x_1333_);
v___x_1335_ = v___x_1296_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_size_1293_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1338_, lean_object* v_e_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1342_ = lean_st_ref_take(v_a_1338_);
v___x_1343_ = lean_box(0);
v___x_1344_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1342_, v_e_1339_, v_a_1340_);
v___x_1345_ = lean_st_ref_put(v_a_1338_, v___x_1344_);
return v___x_1343_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1338_ = stack[0].m_obj;
lean_object* v_e_1339_ = stack[1].m_obj;
lean_object* v_a_1340_ = stack[2].m_obj;
lean_object* v_res_1346_;
v_res_1346_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1338_, v_e_1339_, v_a_1340_);
stack->m_obj
 = v_res_1346_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1347_, lean_object* v_e_1348_, lean_object* v_a_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1347_, v_e_1348_, v_a_1349_);
lean_dec(v_a_1347_);
return v_res_1351_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1352_, lean_object* v___y_1353_, lean_object* v_b_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; 
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1353_);
v___x_1360_ = lean_apply_7(v_k_1352_, v_b_1354_, v___y_1353_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1360_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1352_ = stack[0].m_obj;
lean_object* v___y_1353_ = stack[1].m_obj;
lean_object* v_b_1354_ = stack[2].m_obj;
lean_object* v___y_1355_ = stack[3].m_obj;
lean_object* v___y_1356_ = stack[4].m_obj;
lean_object* v___y_1357_ = stack[5].m_obj;
lean_object* v___y_1358_ = stack[6].m_obj;
lean_object* v_res_1361_;
v_res_1361_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1352_, v___y_1353_, v_b_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
stack->m_obj
 = v_res_1361_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1362_, lean_object* v___y_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1362_, v___y_1363_, v_b_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1363_);
return v_res_1370_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1371_, uint8_t v_bi_1372_, lean_object* v_type_1373_, lean_object* v_k_1374_, uint8_t v_kind_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v___f_1382_; lean_object* v___x_1383_; 
lean_inc(v___y_1376_);
v___f_1382_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1382_, 0, v_k_1374_);
lean_closure_set(v___f_1382_, 1, v___y_1376_);
v___x_1383_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1371_, v_bi_1372_, v_type_1373_, v___f_1382_, v_kind_1375_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1383_) == 0)
{
return v___x_1383_;
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1371_ = stack[0].m_obj;
uint8_t v_bi_1372_ = stack[1].m_num;
lean_object* v_type_1373_ = stack[2].m_obj;
lean_object* v_k_1374_ = stack[3].m_obj;
uint8_t v_kind_1375_ = stack[4].m_num;
lean_object* v___y_1376_ = stack[5].m_obj;
lean_object* v___y_1377_ = stack[6].m_obj;
lean_object* v___y_1378_ = stack[7].m_obj;
lean_object* v___y_1379_ = stack[8].m_obj;
lean_object* v___y_1380_ = stack[9].m_obj;
lean_object* v_res_1392_;
v_res_1392_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1371_, v_bi_1372_, v_type_1373_, v_k_1374_, v_kind_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
stack->m_obj
 = v_res_1392_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1393_, lean_object* v_bi_1394_, lean_object* v_type_1395_, lean_object* v_k_1396_, lean_object* v_kind_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v_bi_boxed_1404_; uint8_t v_kind_boxed_1405_; lean_object* v_res_1406_; 
v_bi_boxed_1404_ = lean_unbox(v_bi_1394_);
v_kind_boxed_1405_ = lean_unbox(v_kind_1397_);
v_res_1406_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1393_, v_bi_boxed_1404_, v_type_1395_, v_k_1396_, v_kind_boxed_1405_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
return v_res_1406_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object* v___x_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1407_);
return v___x_1413_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1407_ = stack[0].m_obj;
lean_object* v___y_1408_ = stack[1].m_obj;
lean_object* v___y_1409_ = stack[2].m_obj;
lean_object* v___y_1410_ = stack[3].m_obj;
lean_object* v___y_1411_ = stack[4].m_obj;
lean_object* v_res_1414_;
v_res_1414_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
stack->m_obj
 = v_res_1414_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object* v___x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1421_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1422_, lean_object* v_type_1423_, lean_object* v_val_1424_, lean_object* v_k_1425_, uint8_t v_nondep_1426_, uint8_t v_kind_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___f_1434_; lean_object* v___x_1435_; 
lean_inc(v___y_1428_);
v___f_1434_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1434_, 0, v_k_1425_);
lean_closure_set(v___f_1434_, 1, v___y_1428_);
v___x_1435_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1422_, v_type_1423_, v_val_1424_, v___f_1434_, v_nondep_1426_, v_kind_1427_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1435_) == 0)
{
return v___x_1435_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1422_ = stack[0].m_obj;
lean_object* v_type_1423_ = stack[1].m_obj;
lean_object* v_val_1424_ = stack[2].m_obj;
lean_object* v_k_1425_ = stack[3].m_obj;
uint8_t v_nondep_1426_ = stack[4].m_num;
uint8_t v_kind_1427_ = stack[5].m_num;
lean_object* v___y_1428_ = stack[6].m_obj;
lean_object* v___y_1429_ = stack[7].m_obj;
lean_object* v___y_1430_ = stack[8].m_obj;
lean_object* v___y_1431_ = stack[9].m_obj;
lean_object* v___y_1432_ = stack[10].m_obj;
lean_object* v_res_1444_;
v_res_1444_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1422_, v_type_1423_, v_val_1424_, v_k_1425_, v_nondep_1426_, v_kind_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
stack->m_obj
 = v_res_1444_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1445_, lean_object* v_type_1446_, lean_object* v_val_1447_, lean_object* v_k_1448_, lean_object* v_nondep_1449_, lean_object* v_kind_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v_nondep_boxed_1457_; uint8_t v_kind_boxed_1458_; lean_object* v_res_1459_; 
v_nondep_boxed_1457_ = lean_unbox(v_nondep_1449_);
v_kind_boxed_1458_ = lean_unbox(v_kind_1450_);
v_res_1459_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1445_, v_type_1446_, v_val_1447_, v_k_1448_, v_nondep_boxed_1457_, v_kind_boxed_1458_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
return v_res_1459_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1460_, lean_object* v_x_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_apply_1(v_x_1461_, lean_box(0));
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1461_ = stack[1].m_obj;
lean_object* v___y_1462_ = stack[2].m_obj;
lean_object* v___y_1463_ = stack[3].m_obj;
lean_object* v___y_1464_ = stack[4].m_obj;
lean_object* v___y_1465_ = stack[5].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v_x_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1470_, v_x_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1477_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = l_Lean_maxRecDepthErrorMessage;
v___x_1484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1486_ = l_Lean_MessageData_ofFormat(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1488_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1489_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___x_1487_);
return v___x_1489_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v_ref_1490_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1490_ = stack[0].m_obj;
lean_object* v_res_1495_;
v_res_1495_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1490_);
stack->m_obj
 = v_res_1495_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1496_);
return v_res_1498_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___y_1507_; lean_object* v_toCold_1516_; lean_object* v_currRecDepth_1517_; lean_object* v_ref_1518_; uint16_t v_optionFlags_1519_; uint8_t v_suppressElabErrors_1520_; uint8_t v_isRecordingDeps_1521_; lean_object* v_maxRecDepth_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v_toCold_1516_ = lean_ctor_get(v___y_1503_, 0);
v_currRecDepth_1517_ = lean_ctor_get(v___y_1503_, 1);
v_ref_1518_ = lean_ctor_get(v___y_1503_, 2);
v_optionFlags_1519_ = lean_ctor_get_uint16(v___y_1503_, sizeof(void*)*3);
v_suppressElabErrors_1520_ = lean_ctor_get_uint8(v___y_1503_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1521_ = lean_ctor_get_uint8(v___y_1503_, sizeof(void*)*3 + 3);
v_maxRecDepth_1527_ = lean_ctor_get(v_toCold_1516_, 3);
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_nat_dec_eq(v_maxRecDepth_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_nat_dec_eq(v_currRecDepth_1517_, v_maxRecDepth_1527_);
if (v___x_1530_ == 0)
{
goto v___jp_1522_;
}
else
{
lean_object* v___x_1531_; 
lean_dec_ref(v_x_1499_);
lean_inc(v_ref_1518_);
v___x_1531_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1518_);
v___y_1507_ = v___x_1531_;
goto v___jp_1506_;
}
}
else
{
goto v___jp_1522_;
}
v___jp_1506_:
{
if (lean_obj_tag(v___y_1507_) == 0)
{
return v___y_1507_;
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_a_1508_ = lean_ctor_get(v___y_1507_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___y_1507_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___y_1507_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___y_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
v___jp_1522_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_add(v_currRecDepth_1517_, v___x_1523_);
lean_inc(v_ref_1518_);
lean_inc_ref(v_toCold_1516_);
v___x_1525_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1525_, 0, v_toCold_1516_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
lean_ctor_set(v___x_1525_, 2, v_ref_1518_);
lean_ctor_set_uint16(v___x_1525_, sizeof(void*)*3, v_optionFlags_1519_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*3 + 2, v_suppressElabErrors_1520_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*3 + 3, v_isRecordingDeps_1521_);
lean_inc(v___y_1504_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
v___x_1526_ = lean_apply_6(v_x_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___x_1525_, v___y_1504_, lean_box(0));
v___y_1507_ = v___x_1526_;
goto v___jp_1506_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1499_ = stack[0].m_obj;
lean_object* v___y_1500_ = stack[1].m_obj;
lean_object* v___y_1501_ = stack[2].m_obj;
lean_object* v___y_1502_ = stack[3].m_obj;
lean_object* v___y_1503_ = stack[4].m_obj;
lean_object* v___y_1504_ = stack[5].m_obj;
lean_object* v_res_1532_;
v_res_1532_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
stack->m_obj
 = v_res_1532_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1541_, lean_object* v_x_1542_){
_start:
{
if (lean_obj_tag(v_x_1542_) == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_box(0);
return v___x_1543_;
}
else
{
lean_object* v_key_1544_; lean_object* v_value_1545_; lean_object* v_tail_1546_; uint8_t v___x_1547_; 
v_key_1544_ = lean_ctor_get(v_x_1542_, 0);
v_value_1545_ = lean_ctor_get(v_x_1542_, 1);
v_tail_1546_ = lean_ctor_get(v_x_1542_, 2);
v___x_1547_ = l_Lean_ExprStructEq_beq(v_key_1544_, v_a_1541_);
if (v___x_1547_ == 0)
{
v_x_1542_ = v_tail_1546_;
goto _start;
}
else
{
lean_object* v___x_1549_; 
lean_inc(v_value_1545_);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_value_1545_);
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1550_, lean_object* v_x_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1550_, v_x_1551_);
lean_dec(v_x_1551_);
lean_dec_ref(v_a_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_buckets_1555_; lean_object* v___x_1556_; uint64_t v___x_1557_; uint64_t v___x_1558_; uint64_t v___x_1559_; uint64_t v_fold_1560_; uint64_t v___x_1561_; uint64_t v___x_1562_; uint64_t v___x_1563_; size_t v___x_1564_; size_t v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_buckets_1555_ = lean_ctor_get(v_m_1553_, 1);
v___x_1556_ = lean_array_get_size(v_buckets_1555_);
v___x_1557_ = l_Lean_ExprStructEq_hash(v_a_1554_);
v___x_1558_ = 32ULL;
v___x_1559_ = lean_uint64_shift_right(v___x_1557_, v___x_1558_);
v_fold_1560_ = lean_uint64_xor(v___x_1557_, v___x_1559_);
v___x_1561_ = 16ULL;
v___x_1562_ = lean_uint64_shift_right(v_fold_1560_, v___x_1561_);
v___x_1563_ = lean_uint64_xor(v_fold_1560_, v___x_1562_);
v___x_1564_ = lean_uint64_to_usize(v___x_1563_);
v___x_1565_ = lean_usize_of_nat(v___x_1556_);
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_sub(v___x_1565_, v___x_1566_);
v___x_1568_ = lean_usize_land(v___x_1564_, v___x_1567_);
v___x_1569_ = lean_array_uget_borrowed(v_buckets_1555_, v___x_1568_);
v___x_1570_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1554_, v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1571_, v_a_1572_);
lean_dec_ref(v_a_1572_);
lean_dec_ref(v_m_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_1574_, lean_object* v_pre_1575_, lean_object* v_post_1576_, lean_object* v_usedLetOnly_1577_, lean_object* v_skipConstInApp_1578_, lean_object* v_skipInstances_1579_, lean_object* v_body_1580_, lean_object* v_x_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v_usedLetOnly_boxed_1588_; uint8_t v_skipConstInApp_boxed_1589_; uint8_t v_skipInstances_boxed_1590_; lean_object* v_res_1591_; 
v_usedLetOnly_boxed_1588_ = lean_unbox(v_usedLetOnly_1577_);
v_skipConstInApp_boxed_1589_ = lean_unbox(v_skipConstInApp_1578_);
v_skipInstances_boxed_1590_ = lean_unbox(v_skipInstances_1579_);
v_res_1591_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_1574_, v_pre_1575_, v_post_1576_, v_usedLetOnly_boxed_1588_, v_skipConstInApp_boxed_1589_, v_skipInstances_boxed_1590_, v_body_1580_, v_x_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
return v_res_1591_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1595_, lean_object* v_pre_1596_, lean_object* v_post_1597_, uint8_t v_usedLetOnly_1598_, uint8_t v_skipConstInApp_1599_, uint8_t v_skipInstances_1600_, lean_object* v_body_1601_, lean_object* v_x_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_array_push(v_fvars_1595_, v_x_1602_);
v___x_1610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1596_, v_post_1597_, v_usedLetOnly_1598_, v_skipConstInApp_1599_, v_skipInstances_1600_, v___x_1609_, v_body_1601_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
return v___x_1610_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1595_ = stack[0].m_obj;
lean_object* v_pre_1596_ = stack[1].m_obj;
lean_object* v_post_1597_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1598_ = stack[3].m_num;
uint8_t v_skipConstInApp_1599_ = stack[4].m_num;
uint8_t v_skipInstances_1600_ = stack[5].m_num;
lean_object* v_body_1601_ = stack[6].m_obj;
lean_object* v_x_1602_ = stack[7].m_obj;
lean_object* v___y_1603_ = stack[8].m_obj;
lean_object* v___y_1604_ = stack[9].m_obj;
lean_object* v___y_1605_ = stack[10].m_obj;
lean_object* v___y_1606_ = stack[11].m_obj;
lean_object* v___y_1607_ = stack[12].m_obj;
lean_object* v_res_1611_;
v_res_1611_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1595_, v_pre_1596_, v_post_1597_, v_usedLetOnly_1598_, v_skipConstInApp_1599_, v_skipInstances_1600_, v_body_1601_, v_x_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
stack->m_obj
 = v_res_1611_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1612_, lean_object* v_pre_1613_, lean_object* v_post_1614_, lean_object* v_usedLetOnly_1615_, lean_object* v_skipConstInApp_1616_, lean_object* v_skipInstances_1617_, lean_object* v_body_1618_, lean_object* v_x_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v_usedLetOnly_boxed_1626_; uint8_t v_skipConstInApp_boxed_1627_; uint8_t v_skipInstances_boxed_1628_; lean_object* v_res_1629_; 
v_usedLetOnly_boxed_1626_ = lean_unbox(v_usedLetOnly_1615_);
v_skipConstInApp_boxed_1627_ = lean_unbox(v_skipConstInApp_1616_);
v_skipInstances_boxed_1628_ = lean_unbox(v_skipInstances_1617_);
v_res_1629_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1612_, v_pre_1613_, v_post_1614_, v_usedLetOnly_boxed_1626_, v_skipConstInApp_boxed_1627_, v_skipInstances_boxed_1628_, v_body_1618_, v_x_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1629_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1630_, lean_object* v_post_1631_, uint8_t v_usedLetOnly_1632_, uint8_t v_skipConstInApp_1633_, uint8_t v_skipInstances_1634_, lean_object* v_e_1635_, lean_object* v_a_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
lean_inc_ref(v_post_1631_);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1637_);
lean_inc_ref(v_e_1635_);
v___x_1642_ = lean_apply_6(v_post_1631_, v_e_1635_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, lean_box(0));
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1661_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1661_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1661_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
switch(lean_obj_tag(v_a_1643_))
{
case 0:
{
lean_object* v_e_1647_; lean_object* v___x_1649_; 
lean_dec_ref(v_e_1635_);
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
v_e_1647_ = lean_ctor_get(v_a_1643_, 0);
lean_inc_ref(v_e_1647_);
lean_dec_ref_known(v_a_1643_, 1);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_e_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_e_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
case 1:
{
lean_object* v_e_1651_; lean_object* v___x_1652_; 
lean_del_object(v___x_1645_);
lean_dec_ref(v_e_1635_);
v_e_1651_ = lean_ctor_get(v_a_1643_, 0);
lean_inc_ref(v_e_1651_);
lean_dec_ref_known(v_a_1643_, 1);
v___x_1652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v_e_1651_, v_a_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1652_;
}
default: 
{
lean_object* v_e_x3f_1653_; 
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
v_e_x3f_1653_ = lean_ctor_get(v_a_1643_, 0);
lean_inc(v_e_x3f_1653_);
lean_dec_ref_known(v_a_1643_, 1);
if (lean_obj_tag(v_e_x3f_1653_) == 0)
{
lean_object* v___x_1655_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_e_1635_);
v___x_1655_ = v___x_1645_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_e_1635_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
else
{
lean_object* v_val_1657_; lean_object* v___x_1659_; 
lean_dec_ref(v_e_1635_);
v_val_1657_ = lean_ctor_get(v_e_x3f_1653_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v_e_x3f_1653_, 1);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_val_1657_);
v___x_1659_ = v___x_1645_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_val_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec_ref(v_e_1635_);
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
v_a_1662_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1642_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1642_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1630_ = stack[0].m_obj;
lean_object* v_post_1631_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1632_ = stack[2].m_num;
uint8_t v_skipConstInApp_1633_ = stack[3].m_num;
uint8_t v_skipInstances_1634_ = stack[4].m_num;
lean_object* v_e_1635_ = stack[5].m_obj;
lean_object* v_a_1636_ = stack[6].m_obj;
lean_object* v___y_1637_ = stack[7].m_obj;
lean_object* v___y_1638_ = stack[8].m_obj;
lean_object* v___y_1639_ = stack[9].m_obj;
lean_object* v___y_1640_ = stack[10].m_obj;
lean_object* v_res_1670_;
v_res_1670_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v_e_1635_, v_a_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
stack->m_obj
 = v_res_1670_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1671_, lean_object* v_post_1672_, uint8_t v_usedLetOnly_1673_, uint8_t v_skipConstInApp_1674_, uint8_t v_skipInstances_1675_, lean_object* v_fvars_1676_, lean_object* v_e_1677_, lean_object* v_a_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
if (lean_obj_tag(v_e_1677_) == 6)
{
lean_object* v_binderName_1684_; lean_object* v_binderType_1685_; lean_object* v_body_1686_; uint8_t v_binderInfo_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_binderName_1684_ = lean_ctor_get(v_e_1677_, 0);
lean_inc(v_binderName_1684_);
v_binderType_1685_ = lean_ctor_get(v_e_1677_, 1);
lean_inc_ref(v_binderType_1685_);
v_body_1686_ = lean_ctor_get(v_e_1677_, 2);
lean_inc_ref(v_body_1686_);
v_binderInfo_1687_ = lean_ctor_get_uint8(v_e_1677_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1677_, 3);
v___x_1688_ = lean_box(v_usedLetOnly_1673_);
v___x_1689_ = lean_box(v_skipConstInApp_1674_);
v___x_1690_ = lean_box(v_skipInstances_1675_);
lean_inc_ref(v_post_1672_);
lean_inc_ref(v_pre_1671_);
lean_inc_ref(v_fvars_1676_);
v___f_1691_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1691_, 0, v_fvars_1676_);
lean_closure_set(v___f_1691_, 1, v_pre_1671_);
lean_closure_set(v___f_1691_, 2, v_post_1672_);
lean_closure_set(v___f_1691_, 3, v___x_1688_);
lean_closure_set(v___f_1691_, 4, v___x_1689_);
lean_closure_set(v___f_1691_, 5, v___x_1690_);
lean_closure_set(v___f_1691_, 6, v_body_1686_);
v___x_1692_ = lean_expr_instantiate_rev(v_binderType_1685_, v_fvars_1676_);
lean_dec_ref(v_fvars_1676_);
lean_dec_ref(v_binderType_1685_);
v___x_1693_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1671_, v_post_1672_, v_usedLetOnly_1673_, v_skipConstInApp_1674_, v_skipInstances_1675_, v___x_1692_, v_a_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = 0;
v___x_1696_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1684_, v_binderInfo_1687_, v_a_1694_, v___f_1691_, v___x_1695_, v_a_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1696_;
}
else
{
lean_dec_ref(v___f_1691_);
lean_dec(v_binderName_1684_);
return v___x_1693_;
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_expr_instantiate_rev(v_e_1677_, v_fvars_1676_);
lean_dec_ref(v_e_1677_);
lean_inc_ref(v_post_1672_);
lean_inc_ref(v_pre_1671_);
v___x_1698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1671_, v_post_1672_, v_usedLetOnly_1673_, v_skipConstInApp_1674_, v_skipInstances_1675_, v___x_1697_, v_a_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; uint8_t v___x_1700_; uint8_t v___x_1701_; uint8_t v___x_1702_; lean_object* v___x_1703_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = 0;
v___x_1701_ = 1;
v___x_1702_ = 1;
v___x_1703_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1676_, v_a_1699_, v___x_1700_, v_usedLetOnly_1673_, v___x_1700_, v___x_1701_, v___x_1702_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec_ref(v_fvars_1676_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1671_, v_post_1672_, v_usedLetOnly_1673_, v_skipConstInApp_1674_, v_skipInstances_1675_, v_a_1704_, v_a_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1705_;
}
else
{
lean_dec_ref(v_post_1672_);
lean_dec_ref(v_pre_1671_);
return v___x_1703_;
}
}
else
{
lean_dec_ref(v_fvars_1676_);
lean_dec_ref(v_post_1672_);
lean_dec_ref(v_pre_1671_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1671_ = stack[0].m_obj;
lean_object* v_post_1672_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1673_ = stack[2].m_num;
uint8_t v_skipConstInApp_1674_ = stack[3].m_num;
uint8_t v_skipInstances_1675_ = stack[4].m_num;
lean_object* v_fvars_1676_ = stack[5].m_obj;
lean_object* v_e_1677_ = stack[6].m_obj;
lean_object* v_a_1678_ = stack[7].m_obj;
lean_object* v___y_1679_ = stack[8].m_obj;
lean_object* v___y_1680_ = stack[9].m_obj;
lean_object* v___y_1681_ = stack[10].m_obj;
lean_object* v___y_1682_ = stack[11].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1671_, v_post_1672_, v_usedLetOnly_1673_, v_skipConstInApp_1674_, v_skipInstances_1675_, v_fvars_1676_, v_e_1677_, v_a_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
stack->m_obj
 = v_res_1706_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1707_, lean_object* v_pre_1708_, lean_object* v_post_1709_, uint8_t v_usedLetOnly_1710_, uint8_t v_skipConstInApp_1711_, uint8_t v_skipInstances_1712_, lean_object* v_body_1713_, lean_object* v_x_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_array_push(v_fvars_1707_, v_x_1714_);
v___x_1722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1708_, v_post_1709_, v_usedLetOnly_1710_, v_skipConstInApp_1711_, v_skipInstances_1712_, v___x_1721_, v_body_1713_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v___x_1722_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1707_ = stack[0].m_obj;
lean_object* v_pre_1708_ = stack[1].m_obj;
lean_object* v_post_1709_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1710_ = stack[3].m_num;
uint8_t v_skipConstInApp_1711_ = stack[4].m_num;
uint8_t v_skipInstances_1712_ = stack[5].m_num;
lean_object* v_body_1713_ = stack[6].m_obj;
lean_object* v_x_1714_ = stack[7].m_obj;
lean_object* v___y_1715_ = stack[8].m_obj;
lean_object* v___y_1716_ = stack[9].m_obj;
lean_object* v___y_1717_ = stack[10].m_obj;
lean_object* v___y_1718_ = stack[11].m_obj;
lean_object* v___y_1719_ = stack[12].m_obj;
lean_object* v_res_1723_;
v_res_1723_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1707_, v_pre_1708_, v_post_1709_, v_usedLetOnly_1710_, v_skipConstInApp_1711_, v_skipInstances_1712_, v_body_1713_, v_x_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
stack->m_obj
 = v_res_1723_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1724_, lean_object* v_pre_1725_, lean_object* v_post_1726_, lean_object* v_usedLetOnly_1727_, lean_object* v_skipConstInApp_1728_, lean_object* v_skipInstances_1729_, lean_object* v_body_1730_, lean_object* v_x_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v_usedLetOnly_boxed_1738_; uint8_t v_skipConstInApp_boxed_1739_; uint8_t v_skipInstances_boxed_1740_; lean_object* v_res_1741_; 
v_usedLetOnly_boxed_1738_ = lean_unbox(v_usedLetOnly_1727_);
v_skipConstInApp_boxed_1739_ = lean_unbox(v_skipConstInApp_1728_);
v_skipInstances_boxed_1740_ = lean_unbox(v_skipInstances_1729_);
v_res_1741_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1724_, v_pre_1725_, v_post_1726_, v_usedLetOnly_boxed_1738_, v_skipConstInApp_boxed_1739_, v_skipInstances_boxed_1740_, v_body_1730_, v_x_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
return v_res_1741_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1742_, lean_object* v_post_1743_, uint8_t v_usedLetOnly_1744_, uint8_t v_skipConstInApp_1745_, uint8_t v_skipInstances_1746_, lean_object* v_fvars_1747_, lean_object* v_e_1748_, lean_object* v_a_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
if (lean_obj_tag(v_e_1748_) == 8)
{
lean_object* v_declName_1755_; lean_object* v_type_1756_; lean_object* v_value_1757_; lean_object* v_body_1758_; uint8_t v_nondep_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_declName_1755_ = lean_ctor_get(v_e_1748_, 0);
lean_inc(v_declName_1755_);
v_type_1756_ = lean_ctor_get(v_e_1748_, 1);
lean_inc_ref(v_type_1756_);
v_value_1757_ = lean_ctor_get(v_e_1748_, 2);
lean_inc_ref(v_value_1757_);
v_body_1758_ = lean_ctor_get(v_e_1748_, 3);
lean_inc_ref(v_body_1758_);
v_nondep_1759_ = lean_ctor_get_uint8(v_e_1748_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1748_, 4);
v___x_1760_ = lean_box(v_usedLetOnly_1744_);
v___x_1761_ = lean_box(v_skipConstInApp_1745_);
v___x_1762_ = lean_box(v_skipInstances_1746_);
lean_inc_ref_n(v_post_1743_, 2);
lean_inc_ref_n(v_pre_1742_, 2);
lean_inc_ref(v_fvars_1747_);
v___f_1763_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1763_, 0, v_fvars_1747_);
lean_closure_set(v___f_1763_, 1, v_pre_1742_);
lean_closure_set(v___f_1763_, 2, v_post_1743_);
lean_closure_set(v___f_1763_, 3, v___x_1760_);
lean_closure_set(v___f_1763_, 4, v___x_1761_);
lean_closure_set(v___f_1763_, 5, v___x_1762_);
lean_closure_set(v___f_1763_, 6, v_body_1758_);
v___x_1764_ = lean_expr_instantiate_rev(v_type_1756_, v_fvars_1747_);
lean_dec_ref(v_type_1756_);
v___x_1765_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1742_, v_post_1743_, v_usedLetOnly_1744_, v_skipConstInApp_1745_, v_skipInstances_1746_, v___x_1764_, v_a_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1767_ = lean_expr_instantiate_rev(v_value_1757_, v_fvars_1747_);
lean_dec_ref(v_fvars_1747_);
lean_dec_ref(v_value_1757_);
v___x_1768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1742_, v_post_1743_, v_usedLetOnly_1744_, v_skipConstInApp_1745_, v_skipInstances_1746_, v___x_1767_, v_a_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = 0;
v___x_1771_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1755_, v_a_1766_, v_a_1769_, v___f_1763_, v_nondep_1759_, v___x_1770_, v_a_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1771_;
}
else
{
lean_dec(v_a_1766_);
lean_dec_ref(v___f_1763_);
lean_dec(v_declName_1755_);
return v___x_1768_;
}
}
else
{
lean_dec_ref(v___f_1763_);
lean_dec_ref(v_value_1757_);
lean_dec(v_declName_1755_);
lean_dec_ref(v_fvars_1747_);
lean_dec_ref(v_post_1743_);
lean_dec_ref(v_pre_1742_);
return v___x_1765_;
}
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_expr_instantiate_rev(v_e_1748_, v_fvars_1747_);
lean_dec_ref(v_e_1748_);
lean_inc_ref(v_post_1743_);
lean_inc_ref(v_pre_1742_);
v___x_1773_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1742_, v_post_1743_, v_usedLetOnly_1744_, v_skipConstInApp_1745_, v_skipInstances_1746_, v___x_1772_, v_a_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; uint8_t v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = 0;
v___x_1776_ = 1;
v___x_1777_ = l_Lean_Meta_mkLetFVars(v_fvars_1747_, v_a_1774_, v_usedLetOnly_1744_, v___x_1775_, v___x_1776_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec_ref(v_fvars_1747_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1742_, v_post_1743_, v_usedLetOnly_1744_, v_skipConstInApp_1745_, v_skipInstances_1746_, v_a_1778_, v_a_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1779_;
}
else
{
lean_dec_ref(v_post_1743_);
lean_dec_ref(v_pre_1742_);
return v___x_1777_;
}
}
else
{
lean_dec_ref(v_fvars_1747_);
lean_dec_ref(v_post_1743_);
lean_dec_ref(v_pre_1742_);
return v___x_1773_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1742_ = stack[0].m_obj;
lean_object* v_post_1743_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1744_ = stack[2].m_num;
uint8_t v_skipConstInApp_1745_ = stack[3].m_num;
uint8_t v_skipInstances_1746_ = stack[4].m_num;
lean_object* v_fvars_1747_ = stack[5].m_obj;
lean_object* v_e_1748_ = stack[6].m_obj;
lean_object* v_a_1749_ = stack[7].m_obj;
lean_object* v___y_1750_ = stack[8].m_obj;
lean_object* v___y_1751_ = stack[9].m_obj;
lean_object* v___y_1752_ = stack[10].m_obj;
lean_object* v___y_1753_ = stack[11].m_obj;
lean_object* v_res_1780_;
v_res_1780_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1742_, v_post_1743_, v_usedLetOnly_1744_, v_skipConstInApp_1745_, v_skipInstances_1746_, v_fvars_1747_, v_e_1748_, v_a_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
stack->m_obj
 = v_res_1780_;
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1781_; lean_object* v_dummy_1782_; 
v___x_1781_ = lean_box(0);
v_dummy_1782_ = l_Lean_Expr_sort___override(v___x_1781_);
return v_dummy_1782_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1783_, lean_object* v_post_1784_, uint8_t v_usedLetOnly_1785_, uint8_t v_skipConstInApp_1786_, uint8_t v_skipInstances_1787_, size_t v_sz_1788_, size_t v_i_1789_, lean_object* v_bs_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_lt(v_i_1789_, v_sz_1788_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
lean_dec_ref(v_post_1784_);
lean_dec_ref(v_pre_1783_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v_bs_1790_);
return v___x_1798_;
}
else
{
lean_object* v_v_1799_; lean_object* v___x_1800_; lean_object* v_bs_x27_1801_; lean_object* v___x_1802_; 
v_v_1799_ = lean_array_uget(v_bs_1790_, v_i_1789_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v_bs_x27_1801_ = lean_array_uset(v_bs_1790_, v_i_1789_, v___x_1800_);
lean_inc_ref(v_post_1784_);
lean_inc_ref(v_pre_1783_);
v___x_1802_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1783_, v_post_1784_, v_usedLetOnly_1785_, v_skipConstInApp_1786_, v_skipInstances_1787_, v_v_1799_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1789_, v___x_1804_);
v___x_1806_ = lean_array_uset(v_bs_x27_1801_, v_i_1789_, v_a_1803_);
v_i_1789_ = v___x_1805_;
v_bs_1790_ = v___x_1806_;
goto _start;
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_bs_x27_1801_);
lean_dec_ref(v_post_1784_);
lean_dec_ref(v_pre_1783_);
v_a_1808_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1802_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1802_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1783_ = stack[0].m_obj;
lean_object* v_post_1784_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1785_ = stack[2].m_num;
uint8_t v_skipConstInApp_1786_ = stack[3].m_num;
uint8_t v_skipInstances_1787_ = stack[4].m_num;
size_t v_sz_1788_ = stack[5].m_num;
size_t v_i_1789_ = stack[6].m_num;
lean_object* v_bs_1790_ = stack[7].m_obj;
lean_object* v___y_1791_ = stack[8].m_obj;
lean_object* v___y_1792_ = stack[9].m_obj;
lean_object* v___y_1793_ = stack[10].m_obj;
lean_object* v___y_1794_ = stack[11].m_obj;
lean_object* v___y_1795_ = stack[12].m_obj;
lean_object* v_res_1816_;
v_res_1816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1783_, v_post_1784_, v_usedLetOnly_1785_, v_skipConstInApp_1786_, v_skipInstances_1787_, v_sz_1788_, v_i_1789_, v_bs_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
stack->m_obj
 = v_res_1816_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1817_, lean_object* v_post_1818_, uint8_t v_usedLetOnly_1819_, uint8_t v_skipConstInApp_1820_, uint8_t v_skipInstances_1821_, lean_object* v___x_1822_, lean_object* v___y_1823_, lean_object* v_b_1824_, lean_object* v_a_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1817_, v_post_1818_, v_usedLetOnly_1819_, v_skipConstInApp_1820_, v_skipInstances_1821_, v___x_1822_, v___y_1823_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1841_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1841_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1841_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1836_ = lean_array_fset(v_b_1824_, v_a_1825_, v_a_1832_);
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1837_);
v___x_1839_ = v___x_1834_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec_ref(v_b_1824_);
v_a_1842_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1831_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1831_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_1817_ = stack[0].m_obj;
lean_object* v_post_1818_ = stack[1].m_obj;
uint8_t v_usedLetOnly_1819_ = stack[2].m_num;
uint8_t v_skipConstInApp_1820_ = stack[3].m_num;
uint8_t v_skipInstances_1821_ = stack[4].m_num;
lean_object* v___x_1822_ = stack[5].m_obj;
lean_object* v___y_1823_ = stack[6].m_obj;
lean_object* v_b_1824_ = stack[7].m_obj;
lean_object* v_a_1825_ = stack[8].m_obj;
lean_object* v___y_1826_ = stack[9].m_obj;
lean_object* v___y_1827_ = stack[10].m_obj;
lean_object* v___y_1828_ = stack[11].m_obj;
lean_object* v___y_1829_ = stack[12].m_obj;
lean_object* v_res_1850_;
v_res_1850_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1817_, v_post_1818_, v_usedLetOnly_1819_, v_skipConstInApp_1820_, v_skipInstances_1821_, v___x_1822_, v___y_1823_, v_b_1824_, v_a_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
stack->m_obj
 = v_res_1850_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1851_, lean_object* v_post_1852_, lean_object* v_usedLetOnly_1853_, lean_object* v_skipConstInApp_1854_, lean_object* v_skipInstances_1855_, lean_object* v___x_1856_, lean_object* v___y_1857_, lean_object* v_b_1858_, lean_object* v_a_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
uint8_t v_usedLetOnly_boxed_1865_; uint8_t v_skipConstInApp_boxed_1866_; uint8_t v_skipInstances_boxed_1867_; lean_object* v_res_1868_; 
v_usedLetOnly_boxed_1865_ = lean_unbox(v_usedLetOnly_1853_);
v_skipConstInApp_boxed_1866_ = lean_unbox(v_skipConstInApp_1854_);
v_skipInstances_boxed_1867_ = lean_unbox(v_skipInstances_1855_);
v_res_1868_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1851_, v_post_1852_, v_usedLetOnly_boxed_1865_, v_skipConstInApp_boxed_1866_, v_skipInstances_boxed_1867_, v___x_1856_, v___y_1857_, v_b_1858_, v_a_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_a_1859_);
lean_dec(v___y_1857_);
return v_res_1868_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1869_, lean_object* v___x_1870_, lean_object* v_pre_1871_, lean_object* v_post_1872_, uint8_t v_usedLetOnly_1873_, uint8_t v_skipConstInApp_1874_, uint8_t v_skipInstances_1875_, lean_object* v_a_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___y_1885_; uint8_t v___x_1908_; 
v___x_1908_ = lean_nat_dec_lt(v_a_1876_, v_upperBound_1869_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
lean_dec(v_a_1876_);
lean_dec_ref(v_post_1872_);
lean_dec_ref(v_pre_1871_);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_b_1877_);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1910_ = lean_array_fget_borrowed(v_b_1877_, v_a_1876_);
v___x_1911_ = lean_array_get_size(v___x_1870_);
v___x_1912_ = lean_nat_dec_lt(v_a_1876_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___f_1916_; 
lean_inc(v___x_1910_);
v___x_1913_ = lean_box(v_usedLetOnly_1873_);
v___x_1914_ = lean_box(v_skipConstInApp_1874_);
v___x_1915_ = lean_box(v_skipInstances_1875_);
lean_inc(v_a_1876_);
lean_inc(v___y_1878_);
lean_inc_ref(v_post_1872_);
lean_inc_ref(v_pre_1871_);
v___f_1916_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1916_, 0, v_pre_1871_);
lean_closure_set(v___f_1916_, 1, v_post_1872_);
lean_closure_set(v___f_1916_, 2, v___x_1913_);
lean_closure_set(v___f_1916_, 3, v___x_1914_);
lean_closure_set(v___f_1916_, 4, v___x_1915_);
lean_closure_set(v___f_1916_, 5, v___x_1910_);
lean_closure_set(v___f_1916_, 6, v___y_1878_);
lean_closure_set(v___f_1916_, 7, v_b_1877_);
lean_closure_set(v___f_1916_, 8, v_a_1876_);
v___y_1885_ = v___f_1916_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1917_; uint8_t v_isInstance_1918_; 
v___x_1917_ = lean_array_fget_borrowed(v___x_1870_, v_a_1876_);
v_isInstance_1918_ = lean_ctor_get_uint8(v___x_1917_, sizeof(void*)*1 + 4);
if (v_isInstance_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___f_1922_; 
lean_inc(v___x_1910_);
v___x_1919_ = lean_box(v_usedLetOnly_1873_);
v___x_1920_ = lean_box(v_skipConstInApp_1874_);
v___x_1921_ = lean_box(v_skipInstances_1875_);
lean_inc(v_a_1876_);
lean_inc(v___y_1878_);
lean_inc_ref(v_post_1872_);
lean_inc_ref(v_pre_1871_);
v___f_1922_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1922_, 0, v_pre_1871_);
lean_closure_set(v___f_1922_, 1, v_post_1872_);
lean_closure_set(v___f_1922_, 2, v___x_1919_);
lean_closure_set(v___f_1922_, 3, v___x_1920_);
lean_closure_set(v___f_1922_, 4, v___x_1921_);
lean_closure_set(v___f_1922_, 5, v___x_1910_);
lean_closure_set(v___f_1922_, 6, v___y_1878_);
lean_closure_set(v___f_1922_, 7, v_b_1877_);
lean_closure_set(v___f_1922_, 8, v_a_1876_);
v___y_1885_ = v___f_1922_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1923_; lean_object* v___f_1924_; 
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_b_1877_);
v___f_1924_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1924_, 0, v___x_1923_);
v___y_1885_ = v___f_1924_;
goto v___jp_1884_;
}
}
}
v___jp_1884_:
{
lean_object* v___x_1886_; 
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v___y_1880_);
lean_inc_ref(v___y_1879_);
v___x_1886_ = lean_apply_5(v___y_1885_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, lean_box(0));
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1899_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1899_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1899_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
if (lean_obj_tag(v_a_1887_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; 
lean_dec(v_a_1876_);
lean_dec_ref(v_post_1872_);
lean_dec_ref(v_pre_1871_);
v_a_1891_ = lean_ctor_get(v_a_1887_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v_a_1887_, 1);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_a_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_del_object(v___x_1889_);
v_a_1895_ = lean_ctor_get(v_a_1887_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v_a_1887_, 1);
v___x_1896_ = lean_unsigned_to_nat(1u);
v___x_1897_ = lean_nat_add(v_a_1876_, v___x_1896_);
lean_dec(v_a_1876_);
v_a_1876_ = v___x_1897_;
v_b_1877_ = v_a_1895_;
goto _start;
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
lean_dec(v_a_1876_);
lean_dec_ref(v_post_1872_);
lean_dec_ref(v_pre_1871_);
v_a_1900_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1886_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1886_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1869_ = stack[0].m_obj;
lean_object* v___x_1870_ = stack[1].m_obj;
lean_object* v_pre_1871_ = stack[2].m_obj;
lean_object* v_post_1872_ = stack[3].m_obj;
uint8_t v_usedLetOnly_1873_ = stack[4].m_num;
uint8_t v_skipConstInApp_1874_ = stack[5].m_num;
uint8_t v_skipInstances_1875_ = stack[6].m_num;
lean_object* v_a_1876_ = stack[7].m_obj;
lean_object* v_b_1877_ = stack[8].m_obj;
lean_object* v___y_1878_ = stack[9].m_obj;
lean_object* v___y_1879_ = stack[10].m_obj;
lean_object* v___y_1880_ = stack[11].m_obj;
lean_object* v___y_1881_ = stack[12].m_obj;
lean_object* v___y_1882_ = stack[13].m_obj;
lean_object* v_res_1925_;
v_res_1925_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_1869_, v___x_1870_, v_pre_1871_, v_post_1872_, v_usedLetOnly_1873_, v_skipConstInApp_1874_, v_skipInstances_1875_, v_a_1876_, v_b_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
stack->m_obj
 = v_res_1925_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1926_, lean_object* v_pre_1927_, lean_object* v_post_1928_, uint8_t v_usedLetOnly_1929_, uint8_t v_skipConstInApp_1930_, lean_object* v_x_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_f_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; 
if (lean_obj_tag(v_x_1931_) == 5)
{
lean_object* v_fn_1989_; lean_object* v_arg_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_fn_1989_ = lean_ctor_get(v_x_1931_, 0);
lean_inc_ref(v_fn_1989_);
v_arg_1990_ = lean_ctor_get(v_x_1931_, 1);
lean_inc_ref(v_arg_1990_);
lean_dec_ref_known(v_x_1931_, 2);
v___x_1991_ = lean_array_set(v_x_1932_, v_x_1933_, v_arg_1990_);
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = lean_nat_sub(v_x_1933_, v___x_1992_);
lean_dec(v_x_1933_);
v_x_1931_ = v_fn_1989_;
v_x_1932_ = v___x_1991_;
v_x_1933_ = v___x_1993_;
goto _start;
}
else
{
lean_dec(v_x_1933_);
if (v_skipConstInApp_1930_ == 0)
{
goto v___jp_1986_;
}
else
{
uint8_t v___x_1995_; 
v___x_1995_ = l_Lean_Expr_isConst(v_x_1931_);
if (v___x_1995_ == 0)
{
goto v___jp_1986_;
}
else
{
v_f_1941_ = v_x_1931_;
v___y_1942_ = v___y_1934_;
v___y_1943_ = v___y_1935_;
v___y_1944_ = v___y_1936_;
v___y_1945_ = v___y_1937_;
v___y_1946_ = v___y_1938_;
goto v___jp_1940_;
}
}
}
v___jp_1940_:
{
if (v_skipInstances_1926_ == 0)
{
size_t v_sz_1947_; size_t v___x_1948_; lean_object* v___x_1949_; 
v_sz_1947_ = lean_array_size(v_x_1932_);
v___x_1948_ = ((size_t)0ULL);
lean_inc_ref(v_post_1928_);
lean_inc_ref(v_pre_1927_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1927_, v_post_1928_, v_usedLetOnly_1929_, v_skipConstInApp_1930_, v_skipInstances_1926_, v_sz_1947_, v___x_1948_, v_x_1932_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1951_ = l_Lean_mkAppN(v_f_1941_, v_a_1950_);
lean_dec(v_a_1950_);
v___x_1952_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1927_, v_post_1928_, v_usedLetOnly_1929_, v_skipConstInApp_1930_, v_skipInstances_1926_, v___x_1951_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
return v___x_1952_;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_f_1941_);
lean_dec_ref(v_post_1928_);
lean_dec_ref(v_pre_1927_);
v_a_1953_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1949_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1949_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_array_get_size(v_x_1932_);
lean_inc_ref(v_f_1941_);
v___x_1962_ = l_Lean_Meta_getFunInfoNArgs(v_f_1941_, v___x_1961_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v_paramInfo_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v_paramInfo_1964_ = lean_ctor_get(v_a_1963_, 0);
lean_inc_ref(v_paramInfo_1964_);
lean_dec(v_a_1963_);
v___x_1965_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1928_);
lean_inc_ref(v_pre_1927_);
v___x_1966_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1961_, v_paramInfo_1964_, v_pre_1927_, v_post_1928_, v_usedLetOnly_1929_, v_skipConstInApp_1930_, v_skipInstances_1926_, v___x_1965_, v_x_1932_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec_ref(v_paramInfo_1964_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v___x_1968_ = l_Lean_mkAppN(v_f_1941_, v_a_1967_);
lean_dec(v_a_1967_);
v___x_1969_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1927_, v_post_1928_, v_usedLetOnly_1929_, v_skipConstInApp_1930_, v_skipInstances_1926_, v___x_1968_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
return v___x_1969_;
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_f_1941_);
lean_dec_ref(v_post_1928_);
lean_dec_ref(v_pre_1927_);
v_a_1970_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1966_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1966_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_f_1941_);
lean_dec_ref(v_x_1932_);
lean_dec_ref(v_post_1928_);
lean_dec_ref(v_pre_1927_);
v_a_1978_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1962_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1962_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
v___jp_1986_:
{
lean_object* v___x_1987_; 
lean_inc_ref(v_post_1928_);
lean_inc_ref(v_pre_1927_);
v___x_1987_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1927_, v_post_1928_, v_usedLetOnly_1929_, v_skipConstInApp_1930_, v_skipInstances_1926_, v_x_1931_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v_f_1941_ = v_a_1988_;
v___y_1942_ = v___y_1934_;
v___y_1943_ = v___y_1935_;
v___y_1944_ = v___y_1936_;
v___y_1945_ = v___y_1937_;
v___y_1946_ = v___y_1938_;
goto v___jp_1940_;
}
else
{
lean_dec_ref(v_x_1932_);
lean_dec_ref(v_post_1928_);
lean_dec_ref(v_pre_1927_);
return v___x_1987_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_1926_ = stack[0].m_num;
lean_object* v_pre_1927_ = stack[1].m_obj;
lean_object* v_post_1928_ = stack[2].m_obj;
uint8_t v_usedLetOnly_1929_ = stack[3].m_num;
uint8_t v_skipConstInApp_1930_ = stack[4].m_num;
lean_object* v_x_1931_ = stack[5].m_obj;
lean_object* v_x_1932_ = stack[6].m_obj;
lean_object* v_x_1933_ = stack[7].m_obj;
lean_object* v___y_1934_ = stack[8].m_obj;
lean_object* v___y_1935_ = stack[9].m_obj;
lean_object* v___y_1936_ = stack[10].m_obj;
lean_object* v___y_1937_ = stack[11].m_obj;
lean_object* v___y_1938_ = stack[12].m_obj;
lean_object* v_res_1996_;
v_res_1996_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1926_, v_pre_1927_, v_post_1928_, v_usedLetOnly_1929_, v_skipConstInApp_1930_, v_x_1931_, v_x_1932_, v_x_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
stack->m_obj
 = v_res_1996_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1997_, lean_object* v_pre_1998_, lean_object* v_e_1999_, lean_object* v_post_2000_, uint8_t v_usedLetOnly_2001_, uint8_t v_skipConstInApp_2002_, uint8_t v_skipInstances_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Core_checkSystem(v___x_1997_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v___x_2011_; 
lean_dec_ref_known(v___x_2010_, 1);
lean_inc_ref(v_pre_1998_);
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2007_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc_ref(v_e_1999_);
v___x_2011_ = lean_apply_6(v_pre_1998_, v_e_1999_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, lean_box(0));
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2060_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2060_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2060_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___y_2017_; 
switch(lean_obj_tag(v_a_2012_))
{
case 0:
{
lean_object* v_e_2052_; lean_object* v___x_2054_; 
lean_dec_ref(v_post_2000_);
lean_dec_ref(v_e_1999_);
lean_dec_ref(v_pre_1998_);
v_e_2052_ = lean_ctor_get(v_a_2012_, 0);
lean_inc_ref(v_e_2052_);
lean_dec_ref_known(v_a_2012_, 1);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v_e_2052_);
v___x_2054_ = v___x_2014_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_e_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
case 1:
{
lean_object* v_e_2056_; lean_object* v___x_2057_; 
lean_del_object(v___x_2014_);
lean_dec_ref(v_e_1999_);
v_e_2056_ = lean_ctor_get(v_a_2012_, 0);
lean_inc_ref(v_e_2056_);
lean_dec_ref_known(v_a_2012_, 1);
v___x_2057_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v_e_2056_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2057_;
}
default: 
{
lean_object* v_e_x3f_2058_; 
lean_del_object(v___x_2014_);
v_e_x3f_2058_ = lean_ctor_get(v_a_2012_, 0);
lean_inc(v_e_x3f_2058_);
lean_dec_ref_known(v_a_2012_, 1);
if (lean_obj_tag(v_e_x3f_2058_) == 0)
{
v___y_2017_ = v_e_1999_;
goto v___jp_2016_;
}
else
{
lean_object* v_val_2059_; 
lean_dec_ref(v_e_1999_);
v_val_2059_ = lean_ctor_get(v_e_x3f_2058_, 0);
lean_inc(v_val_2059_);
lean_dec_ref_known(v_e_x3f_2058_, 1);
v___y_2017_ = v_val_2059_;
goto v___jp_2016_;
}
}
}
v___jp_2016_:
{
switch(lean_obj_tag(v___y_2017_))
{
case 7:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2019_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___x_2018_, v___y_2017_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2019_;
}
case 6:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___x_2020_, v___y_2017_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2021_;
}
case 8:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2023_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___x_2022_, v___y_2017_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2023_;
}
case 5:
{
lean_object* v_dummy_2024_; lean_object* v_nargs_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_dummy_2024_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2025_ = l_Lean_Expr_getAppNumArgs(v___y_2017_);
lean_inc(v_nargs_2025_);
v___x_2026_ = lean_mk_array(v_nargs_2025_, v_dummy_2024_);
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_sub(v_nargs_2025_, v___x_2027_);
lean_dec(v_nargs_2025_);
v___x_2029_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_2003_, v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v___y_2017_, v___x_2026_, v___x_2028_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2029_;
}
case 10:
{
lean_object* v_data_2030_; lean_object* v_expr_2031_; lean_object* v___x_2032_; 
v_data_2030_ = lean_ctor_get(v___y_2017_, 0);
v_expr_2031_ = lean_ctor_get(v___y_2017_, 1);
lean_inc_ref(v_expr_2031_);
lean_inc_ref(v_post_2000_);
lean_inc_ref(v_pre_1998_);
v___x_2032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v_expr_2031_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; size_t v___x_2034_; size_t v___x_2035_; uint8_t v___x_2036_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = lean_ptr_addr(v_expr_2031_);
v___x_2035_ = lean_ptr_addr(v_a_2033_);
v___x_2036_ = lean_usize_dec_eq(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_inc(v_data_2030_);
lean_dec_ref_known(v___y_2017_, 2);
v___x_2037_ = l_Lean_Expr_mdata___override(v_data_2030_, v_a_2033_);
v___x_2038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___x_2037_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; 
lean_dec(v_a_2033_);
v___x_2039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___y_2017_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2039_;
}
}
else
{
lean_dec_ref_known(v___y_2017_, 2);
lean_dec_ref(v_post_2000_);
lean_dec_ref(v_pre_1998_);
return v___x_2032_;
}
}
case 11:
{
lean_object* v_typeName_2040_; lean_object* v_idx_2041_; lean_object* v_struct_2042_; lean_object* v___x_2043_; 
v_typeName_2040_ = lean_ctor_get(v___y_2017_, 0);
v_idx_2041_ = lean_ctor_get(v___y_2017_, 1);
v_struct_2042_ = lean_ctor_get(v___y_2017_, 2);
lean_inc_ref(v_struct_2042_);
lean_inc_ref(v_post_2000_);
lean_inc_ref(v_pre_1998_);
v___x_2043_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v_struct_2042_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; size_t v___x_2045_; size_t v___x_2046_; uint8_t v___x_2047_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = lean_ptr_addr(v_struct_2042_);
v___x_2046_ = lean_ptr_addr(v_a_2044_);
v___x_2047_ = lean_usize_dec_eq(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_inc(v_idx_2041_);
lean_inc(v_typeName_2040_);
lean_dec_ref_known(v___y_2017_, 3);
v___x_2048_ = l_Lean_Expr_proj___override(v_typeName_2040_, v_idx_2041_, v_a_2044_);
v___x_2049_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___x_2048_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2049_;
}
else
{
lean_object* v___x_2050_; 
lean_dec(v_a_2044_);
v___x_2050_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___y_2017_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2050_;
}
}
else
{
lean_dec_ref_known(v___y_2017_, 3);
lean_dec_ref(v_post_2000_);
lean_dec_ref(v_pre_1998_);
return v___x_2043_;
}
}
default: 
{
lean_object* v___x_2051_; 
v___x_2051_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1998_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___y_2017_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2051_;
}
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v_post_2000_);
lean_dec_ref(v_e_1999_);
lean_dec_ref(v_pre_1998_);
v_a_2061_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2011_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2011_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v_post_2000_);
lean_dec_ref(v_e_1999_);
lean_dec_ref(v_pre_1998_);
v_a_2069_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2010_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2010_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1997_ = stack[0].m_obj;
lean_object* v_pre_1998_ = stack[1].m_obj;
lean_object* v_e_1999_ = stack[2].m_obj;
lean_object* v_post_2000_ = stack[3].m_obj;
uint8_t v_usedLetOnly_2001_ = stack[4].m_num;
uint8_t v_skipConstInApp_2002_ = stack[5].m_num;
uint8_t v_skipInstances_2003_ = stack[6].m_num;
lean_object* v___y_2004_ = stack[7].m_obj;
lean_object* v___y_2005_ = stack[8].m_obj;
lean_object* v___y_2006_ = stack[9].m_obj;
lean_object* v___y_2007_ = stack[10].m_obj;
lean_object* v___y_2008_ = stack[11].m_obj;
lean_object* v_res_2077_;
v_res_2077_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_1997_, v_pre_1998_, v_e_1999_, v_post_2000_, v_usedLetOnly_2001_, v_skipConstInApp_2002_, v_skipInstances_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
stack->m_obj
 = v_res_2077_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2078_, lean_object* v_pre_2079_, lean_object* v_e_2080_, lean_object* v_post_2081_, lean_object* v_usedLetOnly_2082_, lean_object* v_skipConstInApp_2083_, lean_object* v_skipInstances_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v_usedLetOnly_boxed_2091_; uint8_t v_skipConstInApp_boxed_2092_; uint8_t v_skipInstances_boxed_2093_; lean_object* v_res_2094_; 
v_usedLetOnly_boxed_2091_ = lean_unbox(v_usedLetOnly_2082_);
v_skipConstInApp_boxed_2092_ = lean_unbox(v_skipConstInApp_2083_);
v_skipInstances_boxed_2093_ = lean_unbox(v_skipInstances_2084_);
v_res_2094_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2078_, v_pre_2079_, v_e_2080_, v_post_2081_, v_usedLetOnly_boxed_2091_, v_skipConstInApp_boxed_2092_, v_skipInstances_boxed_2093_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
return v_res_2094_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2095_, lean_object* v_post_2096_, uint8_t v_usedLetOnly_2097_, uint8_t v_skipConstInApp_2098_, uint8_t v_skipInstances_2099_, lean_object* v_e_2100_, lean_object* v_a_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_inc(v_a_2101_);
v___x_2107_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2107_, 0, lean_box(0));
lean_closure_set(v___x_2107_, 1, lean_box(0));
lean_closure_set(v___x_2107_, 2, v_a_2101_);
v___x_2108_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2107_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2143_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2143_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2143_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2109_, v_e_2100_);
lean_dec(v_a_2109_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___f_2118_; lean_object* v___x_2119_; 
lean_del_object(v___x_2111_);
v___x_2114_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2115_ = lean_box(v_usedLetOnly_2097_);
v___x_2116_ = lean_box(v_skipConstInApp_2098_);
v___x_2117_ = lean_box(v_skipInstances_2099_);
lean_inc_ref(v_e_2100_);
v___f_2118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2118_, 0, v___x_2114_);
lean_closure_set(v___f_2118_, 1, v_pre_2095_);
lean_closure_set(v___f_2118_, 2, v_e_2100_);
lean_closure_set(v___f_2118_, 3, v_post_2096_);
lean_closure_set(v___f_2118_, 4, v___x_2115_);
lean_closure_set(v___f_2118_, 5, v___x_2116_);
lean_closure_set(v___f_2118_, 6, v___x_2117_);
v___x_2119_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2118_, v_a_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___f_2121_; lean_object* v___x_2122_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc_n(v_a_2120_, 2);
lean_dec_ref_known(v___x_2119_, 1);
lean_inc(v_a_2101_);
v___f_2121_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2121_, 0, v_a_2101_);
lean_closure_set(v___f_2121_, 1, v_e_2100_);
lean_closure_set(v___f_2121_, 2, v_a_2120_);
v___x_2122_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2121_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2122_, 0);
lean_dec(v_unused_2130_);
v___x_2124_ = v___x_2122_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2122_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_a_2120_);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2120_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v_a_2120_);
v_a_2131_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2122_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2122_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_dec_ref(v_e_2100_);
return v___x_2119_;
}
}
else
{
lean_object* v_val_2139_; lean_object* v___x_2141_; 
lean_dec_ref(v_e_2100_);
lean_dec_ref(v_post_2096_);
lean_dec_ref(v_pre_2095_);
v_val_2139_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v___x_2113_, 1);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v_val_2139_);
v___x_2141_ = v___x_2111_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_val_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v_e_2100_);
lean_dec_ref(v_post_2096_);
lean_dec_ref(v_pre_2095_);
v_a_2144_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2108_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2108_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2095_ = stack[0].m_obj;
lean_object* v_post_2096_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2097_ = stack[2].m_num;
uint8_t v_skipConstInApp_2098_ = stack[3].m_num;
uint8_t v_skipInstances_2099_ = stack[4].m_num;
lean_object* v_e_2100_ = stack[5].m_obj;
lean_object* v_a_2101_ = stack[6].m_obj;
lean_object* v___y_2102_ = stack[7].m_obj;
lean_object* v___y_2103_ = stack[8].m_obj;
lean_object* v___y_2104_ = stack[9].m_obj;
lean_object* v___y_2105_ = stack[10].m_obj;
lean_object* v_res_2152_;
v_res_2152_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2095_, v_post_2096_, v_usedLetOnly_2097_, v_skipConstInApp_2098_, v_skipInstances_2099_, v_e_2100_, v_a_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
stack->m_obj
 = v_res_2152_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2153_, lean_object* v_post_2154_, uint8_t v_usedLetOnly_2155_, uint8_t v_skipConstInApp_2156_, uint8_t v_skipInstances_2157_, lean_object* v_fvars_2158_, lean_object* v_e_2159_, lean_object* v_a_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
if (lean_obj_tag(v_e_2159_) == 7)
{
lean_object* v_binderName_2166_; lean_object* v_binderType_2167_; lean_object* v_body_2168_; uint8_t v_binderInfo_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_binderName_2166_ = lean_ctor_get(v_e_2159_, 0);
lean_inc(v_binderName_2166_);
v_binderType_2167_ = lean_ctor_get(v_e_2159_, 1);
lean_inc_ref(v_binderType_2167_);
v_body_2168_ = lean_ctor_get(v_e_2159_, 2);
lean_inc_ref(v_body_2168_);
v_binderInfo_2169_ = lean_ctor_get_uint8(v_e_2159_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2159_, 3);
v___x_2170_ = lean_box(v_usedLetOnly_2155_);
v___x_2171_ = lean_box(v_skipConstInApp_2156_);
v___x_2172_ = lean_box(v_skipInstances_2157_);
lean_inc_ref(v_post_2154_);
lean_inc_ref(v_pre_2153_);
lean_inc_ref(v_fvars_2158_);
v___f_2173_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2173_, 0, v_fvars_2158_);
lean_closure_set(v___f_2173_, 1, v_pre_2153_);
lean_closure_set(v___f_2173_, 2, v_post_2154_);
lean_closure_set(v___f_2173_, 3, v___x_2170_);
lean_closure_set(v___f_2173_, 4, v___x_2171_);
lean_closure_set(v___f_2173_, 5, v___x_2172_);
lean_closure_set(v___f_2173_, 6, v_body_2168_);
v___x_2174_ = lean_expr_instantiate_rev(v_binderType_2167_, v_fvars_2158_);
lean_dec_ref(v_fvars_2158_);
lean_dec_ref(v_binderType_2167_);
v___x_2175_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2153_, v_post_2154_, v_usedLetOnly_2155_, v_skipConstInApp_2156_, v_skipInstances_2157_, v___x_2174_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = 0;
v___x_2178_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2166_, v_binderInfo_2169_, v_a_2176_, v___f_2173_, v___x_2177_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2178_;
}
else
{
lean_dec_ref(v___f_2173_);
lean_dec(v_binderName_2166_);
return v___x_2175_;
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_expr_instantiate_rev(v_e_2159_, v_fvars_2158_);
lean_dec_ref(v_e_2159_);
lean_inc_ref(v_post_2154_);
lean_inc_ref(v_pre_2153_);
v___x_2180_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2153_, v_post_2154_, v_usedLetOnly_2155_, v_skipConstInApp_2156_, v_skipInstances_2157_, v___x_2179_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; uint8_t v___x_2182_; uint8_t v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = 0;
v___x_2183_ = 1;
v___x_2184_ = 1;
v___x_2185_ = l_Lean_Meta_mkForallFVars(v_fvars_2158_, v_a_2181_, v___x_2182_, v_usedLetOnly_2155_, v___x_2183_, v___x_2184_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec_ref(v_fvars_2158_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2153_, v_post_2154_, v_usedLetOnly_2155_, v_skipConstInApp_2156_, v_skipInstances_2157_, v_a_2186_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2187_;
}
else
{
lean_dec_ref(v_post_2154_);
lean_dec_ref(v_pre_2153_);
return v___x_2185_;
}
}
else
{
lean_dec_ref(v_fvars_2158_);
lean_dec_ref(v_post_2154_);
lean_dec_ref(v_pre_2153_);
return v___x_2180_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2153_ = stack[0].m_obj;
lean_object* v_post_2154_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2155_ = stack[2].m_num;
uint8_t v_skipConstInApp_2156_ = stack[3].m_num;
uint8_t v_skipInstances_2157_ = stack[4].m_num;
lean_object* v_fvars_2158_ = stack[5].m_obj;
lean_object* v_e_2159_ = stack[6].m_obj;
lean_object* v_a_2160_ = stack[7].m_obj;
lean_object* v___y_2161_ = stack[8].m_obj;
lean_object* v___y_2162_ = stack[9].m_obj;
lean_object* v___y_2163_ = stack[10].m_obj;
lean_object* v___y_2164_ = stack[11].m_obj;
lean_object* v_res_2188_;
v_res_2188_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2153_, v_post_2154_, v_usedLetOnly_2155_, v_skipConstInApp_2156_, v_skipInstances_2157_, v_fvars_2158_, v_e_2159_, v_a_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
stack->m_obj
 = v_res_2188_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2189_, lean_object* v_pre_2190_, lean_object* v_post_2191_, uint8_t v_usedLetOnly_2192_, uint8_t v_skipConstInApp_2193_, uint8_t v_skipInstances_2194_, lean_object* v_body_2195_, lean_object* v_x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_array_push(v_fvars_2189_, v_x_2196_);
v___x_2204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2190_, v_post_2191_, v_usedLetOnly_2192_, v_skipConstInApp_2193_, v_skipInstances_2194_, v___x_2203_, v_body_2195_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
return v___x_2204_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2189_ = stack[0].m_obj;
lean_object* v_pre_2190_ = stack[1].m_obj;
lean_object* v_post_2191_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2192_ = stack[3].m_num;
uint8_t v_skipConstInApp_2193_ = stack[4].m_num;
uint8_t v_skipInstances_2194_ = stack[5].m_num;
lean_object* v_body_2195_ = stack[6].m_obj;
lean_object* v_x_2196_ = stack[7].m_obj;
lean_object* v___y_2197_ = stack[8].m_obj;
lean_object* v___y_2198_ = stack[9].m_obj;
lean_object* v___y_2199_ = stack[10].m_obj;
lean_object* v___y_2200_ = stack[11].m_obj;
lean_object* v___y_2201_ = stack[12].m_obj;
lean_object* v_res_2205_;
v_res_2205_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_2189_, v_pre_2190_, v_post_2191_, v_usedLetOnly_2192_, v_skipConstInApp_2193_, v_skipInstances_2194_, v_body_2195_, v_x_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
stack->m_obj
 = v_res_2205_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2206_, lean_object* v_post_2207_, lean_object* v_usedLetOnly_2208_, lean_object* v_skipConstInApp_2209_, lean_object* v_skipInstances_2210_, lean_object* v_e_2211_, lean_object* v_a_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
uint8_t v_usedLetOnly_boxed_2218_; uint8_t v_skipConstInApp_boxed_2219_; uint8_t v_skipInstances_boxed_2220_; lean_object* v_res_2221_; 
v_usedLetOnly_boxed_2218_ = lean_unbox(v_usedLetOnly_2208_);
v_skipConstInApp_boxed_2219_ = lean_unbox(v_skipConstInApp_2209_);
v_skipInstances_boxed_2220_ = lean_unbox(v_skipInstances_2210_);
v_res_2221_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2206_, v_post_2207_, v_usedLetOnly_boxed_2218_, v_skipConstInApp_boxed_2219_, v_skipInstances_boxed_2220_, v_e_2211_, v_a_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v_a_2212_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2222_, lean_object* v_post_2223_, lean_object* v_usedLetOnly_2224_, lean_object* v_skipConstInApp_2225_, lean_object* v_skipInstances_2226_, lean_object* v_sz_2227_, lean_object* v_i_2228_, lean_object* v_bs_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
uint8_t v_usedLetOnly_boxed_2236_; uint8_t v_skipConstInApp_boxed_2237_; uint8_t v_skipInstances_boxed_2238_; size_t v_sz_boxed_2239_; size_t v_i_boxed_2240_; lean_object* v_res_2241_; 
v_usedLetOnly_boxed_2236_ = lean_unbox(v_usedLetOnly_2224_);
v_skipConstInApp_boxed_2237_ = lean_unbox(v_skipConstInApp_2225_);
v_skipInstances_boxed_2238_ = lean_unbox(v_skipInstances_2226_);
v_sz_boxed_2239_ = lean_unbox_usize(v_sz_2227_);
lean_dec(v_sz_2227_);
v_i_boxed_2240_ = lean_unbox_usize(v_i_2228_);
lean_dec(v_i_2228_);
v_res_2241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2222_, v_post_2223_, v_usedLetOnly_boxed_2236_, v_skipConstInApp_boxed_2237_, v_skipInstances_boxed_2238_, v_sz_boxed_2239_, v_i_boxed_2240_, v_bs_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2242_, lean_object* v_post_2243_, lean_object* v_usedLetOnly_2244_, lean_object* v_skipConstInApp_2245_, lean_object* v_skipInstances_2246_, lean_object* v_e_2247_, lean_object* v_a_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
uint8_t v_usedLetOnly_boxed_2254_; uint8_t v_skipConstInApp_boxed_2255_; uint8_t v_skipInstances_boxed_2256_; lean_object* v_res_2257_; 
v_usedLetOnly_boxed_2254_ = lean_unbox(v_usedLetOnly_2244_);
v_skipConstInApp_boxed_2255_ = lean_unbox(v_skipConstInApp_2245_);
v_skipInstances_boxed_2256_ = lean_unbox(v_skipInstances_2246_);
v_res_2257_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2242_, v_post_2243_, v_usedLetOnly_boxed_2254_, v_skipConstInApp_boxed_2255_, v_skipInstances_boxed_2256_, v_e_2247_, v_a_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v_a_2248_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2258_, lean_object* v_post_2259_, lean_object* v_usedLetOnly_2260_, lean_object* v_skipConstInApp_2261_, lean_object* v_skipInstances_2262_, lean_object* v_fvars_2263_, lean_object* v_e_2264_, lean_object* v_a_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v_usedLetOnly_boxed_2271_; uint8_t v_skipConstInApp_boxed_2272_; uint8_t v_skipInstances_boxed_2273_; lean_object* v_res_2274_; 
v_usedLetOnly_boxed_2271_ = lean_unbox(v_usedLetOnly_2260_);
v_skipConstInApp_boxed_2272_ = lean_unbox(v_skipConstInApp_2261_);
v_skipInstances_boxed_2273_ = lean_unbox(v_skipInstances_2262_);
v_res_2274_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2258_, v_post_2259_, v_usedLetOnly_boxed_2271_, v_skipConstInApp_boxed_2272_, v_skipInstances_boxed_2273_, v_fvars_2263_, v_e_2264_, v_a_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v_a_2265_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2275_, lean_object* v_post_2276_, lean_object* v_usedLetOnly_2277_, lean_object* v_skipConstInApp_2278_, lean_object* v_skipInstances_2279_, lean_object* v_fvars_2280_, lean_object* v_e_2281_, lean_object* v_a_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v_usedLetOnly_boxed_2288_; uint8_t v_skipConstInApp_boxed_2289_; uint8_t v_skipInstances_boxed_2290_; lean_object* v_res_2291_; 
v_usedLetOnly_boxed_2288_ = lean_unbox(v_usedLetOnly_2277_);
v_skipConstInApp_boxed_2289_ = lean_unbox(v_skipConstInApp_2278_);
v_skipInstances_boxed_2290_ = lean_unbox(v_skipInstances_2279_);
v_res_2291_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2275_, v_post_2276_, v_usedLetOnly_boxed_2288_, v_skipConstInApp_boxed_2289_, v_skipInstances_boxed_2290_, v_fvars_2280_, v_e_2281_, v_a_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v_a_2282_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2292_, lean_object* v_post_2293_, lean_object* v_usedLetOnly_2294_, lean_object* v_skipConstInApp_2295_, lean_object* v_skipInstances_2296_, lean_object* v_fvars_2297_, lean_object* v_e_2298_, lean_object* v_a_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v_usedLetOnly_boxed_2305_; uint8_t v_skipConstInApp_boxed_2306_; uint8_t v_skipInstances_boxed_2307_; lean_object* v_res_2308_; 
v_usedLetOnly_boxed_2305_ = lean_unbox(v_usedLetOnly_2294_);
v_skipConstInApp_boxed_2306_ = lean_unbox(v_skipConstInApp_2295_);
v_skipInstances_boxed_2307_ = lean_unbox(v_skipInstances_2296_);
v_res_2308_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2292_, v_post_2293_, v_usedLetOnly_boxed_2305_, v_skipConstInApp_boxed_2306_, v_skipInstances_boxed_2307_, v_fvars_2297_, v_e_2298_, v_a_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v_a_2299_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2309_, lean_object* v___x_2310_, lean_object* v_pre_2311_, lean_object* v_post_2312_, lean_object* v_usedLetOnly_2313_, lean_object* v_skipConstInApp_2314_, lean_object* v_skipInstances_2315_, lean_object* v_a_2316_, lean_object* v_b_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
uint8_t v_usedLetOnly_boxed_2324_; uint8_t v_skipConstInApp_boxed_2325_; uint8_t v_skipInstances_boxed_2326_; lean_object* v_res_2327_; 
v_usedLetOnly_boxed_2324_ = lean_unbox(v_usedLetOnly_2313_);
v_skipConstInApp_boxed_2325_ = lean_unbox(v_skipConstInApp_2314_);
v_skipInstances_boxed_2326_ = lean_unbox(v_skipInstances_2315_);
v_res_2327_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2309_, v___x_2310_, v_pre_2311_, v_post_2312_, v_usedLetOnly_boxed_2324_, v_skipConstInApp_boxed_2325_, v_skipInstances_boxed_2326_, v_a_2316_, v_b_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___x_2310_);
lean_dec(v_upperBound_2309_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2328_, lean_object* v_pre_2329_, lean_object* v_post_2330_, lean_object* v_usedLetOnly_2331_, lean_object* v_skipConstInApp_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
uint8_t v_skipInstances_boxed_2342_; uint8_t v_usedLetOnly_boxed_2343_; uint8_t v_skipConstInApp_boxed_2344_; lean_object* v_res_2345_; 
v_skipInstances_boxed_2342_ = lean_unbox(v_skipInstances_2328_);
v_usedLetOnly_boxed_2343_ = lean_unbox(v_usedLetOnly_2331_);
v_skipConstInApp_boxed_2344_ = lean_unbox(v_skipConstInApp_2332_);
v_res_2345_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2342_, v_pre_2329_, v_post_2330_, v_usedLetOnly_boxed_2343_, v_skipConstInApp_boxed_2344_, v_x_2333_, v_x_2334_, v_x_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
return v_res_2345_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2347_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2347_, 0, lean_box(0));
lean_closure_set(v___x_2347_, 1, lean_box(0));
lean_closure_set(v___x_2347_, 2, v___x_2346_);
return v___x_2347_;
}
}
lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2348_, lean_object* v_pre_2349_, lean_object* v_post_2350_, uint8_t v_usedLetOnly_2351_, uint8_t v_skipConstInApp_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v_a_2361_; lean_object* v___x_2362_; 
v___x_2358_ = 0;
v___x_2359_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2360_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2359_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref(v___x_2360_);
v___x_2362_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2349_, v_post_2350_, v_usedLetOnly_2351_, v_skipConstInApp_2352_, v___x_2358_, v_input_2348_, v_a_2361_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2364_, 0, lean_box(0));
lean_closure_set(v___x_2364_, 1, lean_box(0));
lean_closure_set(v___x_2364_, 2, v_a_2361_);
v___x_2365_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2364_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v___x_2365_, 0);
lean_dec(v_unused_2373_);
v___x_2367_ = v___x_2365_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_dec(v___x_2365_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v_a_2363_);
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2363_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
else
{
lean_dec(v_a_2361_);
return v___x_2362_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_2348_ = stack[0].m_obj;
lean_object* v_pre_2349_ = stack[1].m_obj;
lean_object* v_post_2350_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2351_ = stack[3].m_num;
uint8_t v_skipConstInApp_2352_ = stack[4].m_num;
lean_object* v___y_2353_ = stack[5].m_obj;
lean_object* v___y_2354_ = stack[6].m_obj;
lean_object* v___y_2355_ = stack[7].m_obj;
lean_object* v___y_2356_ = stack[8].m_obj;
lean_object* v_res_2374_;
v_res_2374_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2348_, v_pre_2349_, v_post_2350_, v_usedLetOnly_2351_, v_skipConstInApp_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
stack->m_obj
 = v_res_2374_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2375_, lean_object* v_pre_2376_, lean_object* v_post_2377_, lean_object* v_usedLetOnly_2378_, lean_object* v_skipConstInApp_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
uint8_t v_usedLetOnly_boxed_2385_; uint8_t v_skipConstInApp_boxed_2386_; lean_object* v_res_2387_; 
v_usedLetOnly_boxed_2385_ = lean_unbox(v_usedLetOnly_2378_);
v_skipConstInApp_boxed_2386_ = lean_unbox(v_skipConstInApp_2379_);
v_res_2387_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2375_, v_pre_2376_, v_post_2377_, v_usedLetOnly_boxed_2385_, v_skipConstInApp_boxed_2386_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2388_, lean_object* v_as_2389_, lean_object* v_j_2390_){
_start:
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = lean_array_get_size(v_as_2389_);
v___x_2392_ = lean_nat_dec_lt(v_j_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec(v_j_2390_);
v___x_2393_ = lean_box(0);
return v___x_2393_;
}
else
{
lean_object* v___x_2394_; lean_object* v_declName_2395_; uint8_t v___x_2396_; 
v___x_2394_ = lean_array_fget_borrowed(v_as_2389_, v_j_2390_);
v_declName_2395_ = lean_ctor_get(v___x_2394_, 3);
v___x_2396_ = lean_name_eq(v_declName_2395_, v___x_2388_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_add(v_j_2390_, v___x_2397_);
lean_dec(v_j_2390_);
v_j_2390_ = v___x_2398_;
goto _start;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_j_2390_);
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2401_, lean_object* v_as_2402_, lean_object* v_j_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2401_, v_as_2402_, v_j_2403_);
lean_dec_ref(v_as_2402_);
lean_dec(v___x_2401_);
return v_res_2404_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_st_ref_get(v_val_2405_);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2405_ = stack[0].m_obj;
lean_object* v___y_2406_ = stack[1].m_obj;
lean_object* v___y_2407_ = stack[2].m_obj;
lean_object* v___y_2408_ = stack[3].m_obj;
lean_object* v___y_2409_ = stack[4].m_obj;
lean_object* v_res_2413_;
v_res_2413_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
stack->m_obj
 = v_res_2413_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v_val_2414_);
return v_res_2420_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2421_, lean_object* v_val_2422_, lean_object* v_a_2423_, lean_object* v___x_2424_, lean_object* v_____r_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2431_ = lean_st_ref_take(v_val_2421_);
v___x_2432_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2422_, v_a_2423_, v___x_2431_);
v___x_2433_ = lean_st_ref_put(v_val_2421_, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2424_);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2421_ = stack[0].m_obj;
lean_object* v_val_2422_ = stack[1].m_obj;
lean_object* v_a_2423_ = stack[2].m_obj;
lean_object* v___x_2424_ = stack[3].m_obj;
lean_object* v_____r_2425_ = stack[4].m_obj;
lean_object* v___y_2426_ = stack[5].m_obj;
lean_object* v___y_2427_ = stack[6].m_obj;
lean_object* v___y_2428_ = stack[7].m_obj;
lean_object* v___y_2429_ = stack[8].m_obj;
lean_object* v_res_2436_;
v_res_2436_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2421_, v_val_2422_, v_a_2423_, v___x_2424_, v_____r_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
stack->m_obj
 = v_res_2436_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2437_, lean_object* v_val_2438_, lean_object* v_a_2439_, lean_object* v___x_2440_, lean_object* v_____r_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2437_, v_val_2438_, v_a_2439_, v___x_2440_, v_____r_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v_val_2438_);
lean_dec(v_val_2437_);
return v_res_2447_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2448_, lean_object* v_val_2449_, lean_object* v_next_2450_, lean_object* v_next_2451_, lean_object* v___x_2452_, lean_object* v___x_2453_, lean_object* v_upperBound_2454_, lean_object* v_params_2455_, lean_object* v___x_2456_, lean_object* v_a_2457_, uint8_t v_b_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
uint8_t v_a_2465_; uint8_t v___x_2469_; 
v___x_2469_ = lean_nat_dec_lt(v_a_2457_, v_upperBound_2454_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
lean_dec(v_a_2457_);
lean_dec_ref(v___x_2456_);
lean_dec(v_next_2450_);
v___x_2470_ = lean_box(v_b_2458_);
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
else
{
uint8_t v___x_2472_; lean_object* v___y_2474_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2472_ = lean_nat_dec_eq(v___x_2452_, v___x_2453_);
v___x_2488_ = lean_st_ref_get(v_val_2448_);
v___x_2489_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2451_, v_a_2457_, v___x_2488_);
lean_dec(v___x_2488_);
if (v___x_2489_ == 0)
{
v_a_2465_ = v_b_2458_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2490_; uint8_t v_foApprox_2491_; uint8_t v_ctxApprox_2492_; uint8_t v_quasiPatternApprox_2493_; uint8_t v_constApprox_2494_; uint8_t v_isDefEqStuckEx_2495_; uint8_t v_unificationHints_2496_; uint8_t v_assignSyntheticOpaque_2497_; uint8_t v_offsetCnstrs_2498_; uint8_t v_transparency_2499_; uint8_t v_etaStruct_2500_; uint8_t v_univApprox_2501_; uint8_t v_iota_2502_; uint8_t v_beta_2503_; uint8_t v_proj_2504_; uint8_t v_zeta_2505_; uint8_t v_zetaDelta_2506_; uint8_t v_zetaUnused_2507_; uint8_t v_zetaHave_2508_; uint8_t v_canUnfoldPredicateConfig_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2539_; 
v___x_2490_ = l_Lean_Meta_Context_config(v___y_2459_);
v_foApprox_2491_ = lean_ctor_get_uint8(v___x_2490_, 0);
v_ctxApprox_2492_ = lean_ctor_get_uint8(v___x_2490_, 1);
v_quasiPatternApprox_2493_ = lean_ctor_get_uint8(v___x_2490_, 2);
v_constApprox_2494_ = lean_ctor_get_uint8(v___x_2490_, 3);
v_isDefEqStuckEx_2495_ = lean_ctor_get_uint8(v___x_2490_, 4);
v_unificationHints_2496_ = lean_ctor_get_uint8(v___x_2490_, 5);
v_assignSyntheticOpaque_2497_ = lean_ctor_get_uint8(v___x_2490_, 7);
v_offsetCnstrs_2498_ = lean_ctor_get_uint8(v___x_2490_, 8);
v_transparency_2499_ = lean_ctor_get_uint8(v___x_2490_, 9);
v_etaStruct_2500_ = lean_ctor_get_uint8(v___x_2490_, 10);
v_univApprox_2501_ = lean_ctor_get_uint8(v___x_2490_, 11);
v_iota_2502_ = lean_ctor_get_uint8(v___x_2490_, 12);
v_beta_2503_ = lean_ctor_get_uint8(v___x_2490_, 13);
v_proj_2504_ = lean_ctor_get_uint8(v___x_2490_, 14);
v_zeta_2505_ = lean_ctor_get_uint8(v___x_2490_, 15);
v_zetaDelta_2506_ = lean_ctor_get_uint8(v___x_2490_, 16);
v_zetaUnused_2507_ = lean_ctor_get_uint8(v___x_2490_, 17);
v_zetaHave_2508_ = lean_ctor_get_uint8(v___x_2490_, 18);
v_canUnfoldPredicateConfig_2509_ = lean_ctor_get_uint8(v___x_2490_, 19);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2511_ = v___x_2490_;
v_isShared_2512_ = v_isSharedCheck_2539_;
goto v_resetjp_2510_;
}
else
{
lean_dec(v___x_2490_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2539_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
uint8_t v_trackZetaDelta_2513_; lean_object* v_zetaDeltaSet_2514_; lean_object* v_lctx_2515_; lean_object* v_localInstances_2516_; lean_object* v_defEqCtx_x3f_2517_; lean_object* v_synthPendingDepth_2518_; lean_object* v_customCanUnfoldPredicate_x3f_2519_; uint8_t v_univApprox_2520_; uint8_t v_inTypeClassResolution_2521_; uint8_t v_cacheInferType_2522_; uint8_t v___x_2523_; lean_object* v___x_2525_; 
v_trackZetaDelta_2513_ = lean_ctor_get_uint8(v___y_2459_, sizeof(void*)*7);
v_zetaDeltaSet_2514_ = lean_ctor_get(v___y_2459_, 1);
v_lctx_2515_ = lean_ctor_get(v___y_2459_, 2);
v_localInstances_2516_ = lean_ctor_get(v___y_2459_, 3);
v_defEqCtx_x3f_2517_ = lean_ctor_get(v___y_2459_, 4);
v_synthPendingDepth_2518_ = lean_ctor_get(v___y_2459_, 5);
v_customCanUnfoldPredicate_x3f_2519_ = lean_ctor_get(v___y_2459_, 6);
v_univApprox_2520_ = lean_ctor_get_uint8(v___y_2459_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2521_ = lean_ctor_get_uint8(v___y_2459_, sizeof(void*)*7 + 2);
v_cacheInferType_2522_ = lean_ctor_get_uint8(v___y_2459_, sizeof(void*)*7 + 3);
v___x_2523_ = 0;
if (v_isShared_2512_ == 0)
{
v___x_2525_ = v___x_2511_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 0, v_foApprox_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 1, v_ctxApprox_2492_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 2, v_quasiPatternApprox_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 3, v_constApprox_2494_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 4, v_isDefEqStuckEx_2495_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 5, v_unificationHints_2496_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 7, v_assignSyntheticOpaque_2497_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 8, v_offsetCnstrs_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 9, v_transparency_2499_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 10, v_etaStruct_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 11, v_univApprox_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 12, v_iota_2502_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 13, v_beta_2503_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 14, v_proj_2504_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 15, v_zeta_2505_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 16, v_zetaDelta_2506_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 17, v_zetaUnused_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 18, v_zetaHave_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2538_, 19, v_canUnfoldPredicateConfig_2509_);
v___x_2525_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
uint64_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v_transparency_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; uint8_t v___x_2533_; 
lean_ctor_set_uint8(v___x_2525_, 6, v___x_2523_);
v___x_2526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2525_);
v___x_2527_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set_uint64(v___x_2527_, sizeof(void*)*1, v___x_2526_);
lean_inc(v_customCanUnfoldPredicate_x3f_2519_);
lean_inc(v_synthPendingDepth_2518_);
lean_inc(v_defEqCtx_x3f_2517_);
lean_inc_ref(v_localInstances_2516_);
lean_inc_ref(v_lctx_2515_);
lean_inc(v_zetaDeltaSet_2514_);
lean_inc_ref(v___x_2527_);
v___x_2528_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v_zetaDeltaSet_2514_);
lean_ctor_set(v___x_2528_, 2, v_lctx_2515_);
lean_ctor_set(v___x_2528_, 3, v_localInstances_2516_);
lean_ctor_set(v___x_2528_, 4, v_defEqCtx_x3f_2517_);
lean_ctor_set(v___x_2528_, 5, v_synthPendingDepth_2518_);
lean_ctor_set(v___x_2528_, 6, v_customCanUnfoldPredicate_x3f_2519_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*7, v_trackZetaDelta_2513_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*7 + 1, v_univApprox_2520_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2521_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*7 + 3, v_cacheInferType_2522_);
v___x_2529_ = l_Lean_Meta_Context_config(v___x_2528_);
v_transparency_2530_ = lean_ctor_get_uint8(v___x_2529_, 9);
lean_dec_ref(v___x_2529_);
v___x_2531_ = lean_array_fget_borrowed(v_params_2455_, v_a_2457_);
v___x_2532_ = 2;
v___x_2533_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2530_, v___x_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref_known(v___x_2528_, 7);
v___x_2534_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2532_, v___x_2527_);
lean_inc(v_customCanUnfoldPredicate_x3f_2519_);
lean_inc(v_synthPendingDepth_2518_);
lean_inc(v_defEqCtx_x3f_2517_);
lean_inc_ref(v_localInstances_2516_);
lean_inc_ref(v_lctx_2515_);
lean_inc(v_zetaDeltaSet_2514_);
v___x_2535_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v_zetaDeltaSet_2514_);
lean_ctor_set(v___x_2535_, 2, v_lctx_2515_);
lean_ctor_set(v___x_2535_, 3, v_localInstances_2516_);
lean_ctor_set(v___x_2535_, 4, v_defEqCtx_x3f_2517_);
lean_ctor_set(v___x_2535_, 5, v_synthPendingDepth_2518_);
lean_ctor_set(v___x_2535_, 6, v_customCanUnfoldPredicate_x3f_2519_);
lean_ctor_set_uint8(v___x_2535_, sizeof(void*)*7, v_trackZetaDelta_2513_);
lean_ctor_set_uint8(v___x_2535_, sizeof(void*)*7 + 1, v_univApprox_2520_);
lean_ctor_set_uint8(v___x_2535_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2521_);
lean_ctor_set_uint8(v___x_2535_, sizeof(void*)*7 + 3, v_cacheInferType_2522_);
lean_inc_ref(v___x_2456_);
lean_inc(v___x_2531_);
v___x_2536_ = l_Lean_Meta_isExprDefEq(v___x_2531_, v___x_2456_, v___x_2535_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec_ref_known(v___x_2535_, 7);
v___y_2474_ = v___x_2536_;
goto v___jp_2473_;
}
else
{
lean_object* v___x_2537_; 
lean_dec_ref_known(v___x_2527_, 1);
lean_inc_ref(v___x_2456_);
lean_inc(v___x_2531_);
v___x_2537_ = l_Lean_Meta_isExprDefEq(v___x_2531_, v___x_2456_, v___x_2528_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec_ref_known(v___x_2528_, 7);
v___y_2474_ = v___x_2537_;
goto v___jp_2473_;
}
}
}
}
v___jp_2473_:
{
if (lean_obj_tag(v___y_2474_) == 0)
{
lean_object* v_a_2475_; uint8_t v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___y_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___y_2474_, 1);
v___x_2476_ = lean_unbox(v_a_2475_);
lean_dec(v_a_2475_);
if (v___x_2476_ == 0)
{
v_a_2465_ = v_b_2458_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_st_ref_take(v_val_2448_);
lean_inc(v_a_2457_);
lean_inc(v_next_2450_);
v___x_2478_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2449_, v_next_2450_, v_next_2451_, v_a_2457_, v___x_2477_);
v___x_2479_ = lean_st_ref_put(v_val_2448_, v___x_2478_);
v_a_2465_ = v___x_2472_;
goto v___jp_2464_;
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec(v_a_2457_);
lean_dec_ref(v___x_2456_);
lean_dec(v_next_2450_);
v_a_2480_ = lean_ctor_get(v___y_2474_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___y_2474_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___y_2474_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___y_2474_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
v___jp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = lean_nat_add(v_a_2457_, v___x_2466_);
lean_dec(v_a_2457_);
v_a_2457_ = v___x_2467_;
v_b_2458_ = v_a_2465_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2448_ = stack[0].m_obj;
lean_object* v_val_2449_ = stack[1].m_obj;
lean_object* v_next_2450_ = stack[2].m_obj;
lean_object* v_next_2451_ = stack[3].m_obj;
lean_object* v___x_2452_ = stack[4].m_obj;
lean_object* v___x_2453_ = stack[5].m_obj;
lean_object* v_upperBound_2454_ = stack[6].m_obj;
lean_object* v_params_2455_ = stack[7].m_obj;
lean_object* v___x_2456_ = stack[8].m_obj;
lean_object* v_a_2457_ = stack[9].m_obj;
uint8_t v_b_2458_ = stack[10].m_num;
lean_object* v___y_2459_ = stack[11].m_obj;
lean_object* v___y_2460_ = stack[12].m_obj;
lean_object* v___y_2461_ = stack[13].m_obj;
lean_object* v___y_2462_ = stack[14].m_obj;
lean_object* v_res_2540_;
v_res_2540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2448_, v_val_2449_, v_next_2450_, v_next_2451_, v___x_2452_, v___x_2453_, v_upperBound_2454_, v_params_2455_, v___x_2456_, v_a_2457_, v_b_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
stack->m_obj
 = v_res_2540_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2541_, lean_object* v_val_2542_, lean_object* v_next_2543_, lean_object* v_next_2544_, lean_object* v___x_2545_, lean_object* v___x_2546_, lean_object* v_upperBound_2547_, lean_object* v_params_2548_, lean_object* v___x_2549_, lean_object* v_a_2550_, lean_object* v_b_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
uint8_t v_b_boxed_2557_; lean_object* v_res_2558_; 
v_b_boxed_2557_ = lean_unbox(v_b_2551_);
v_res_2558_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2541_, v_val_2542_, v_next_2543_, v_next_2544_, v___x_2545_, v___x_2546_, v_upperBound_2547_, v_params_2548_, v___x_2549_, v_a_2550_, v_b_boxed_2557_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v_params_2548_);
lean_dec(v_upperBound_2547_);
lean_dec(v___x_2546_);
lean_dec(v___x_2545_);
lean_dec(v_next_2544_);
lean_dec(v_val_2542_);
lean_dec(v_val_2541_);
return v_res_2558_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2570_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2571_ = l_Lean_Name_append(v___x_2570_, v___x_2569_);
return v___x_2571_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
return v___x_2574_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2576_ = l_Lean_stringToMessageData(v___x_2575_);
return v___x_2576_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2579_ = l_Lean_stringToMessageData(v___x_2578_);
return v___x_2579_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2582_ = l_Lean_stringToMessageData(v___x_2581_);
return v___x_2582_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2585_ = l_Lean_stringToMessageData(v___x_2584_);
return v___x_2585_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2588_ = l_Lean_stringToMessageData(v___x_2587_);
return v___x_2588_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2591_ = l_Lean_stringToMessageData(v___x_2590_);
return v___x_2591_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2592_, lean_object* v_val_2593_, lean_object* v_upperBound_2594_, lean_object* v_args_2595_, lean_object* v_e_2596_, lean_object* v_next_2597_, lean_object* v_params_2598_, lean_object* v___x_2599_, lean_object* v___x_2600_, lean_object* v_a_2601_, lean_object* v_b_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_a_2609_; lean_object* v___y_2614_; uint8_t v___x_2633_; 
v___x_2633_ = lean_nat_dec_lt(v_a_2601_, v_upperBound_2594_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_b_2602_);
return v___x_2634_;
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2635_ = lean_box(0);
v___x_2642_ = l_Lean_instInhabitedExpr;
v___x_2643_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2592_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; uint8_t v___x_2645_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2593_, v_a_2601_, v_a_2644_);
lean_dec(v_a_2644_);
if (v___x_2645_ == 0)
{
v_a_2609_ = v___x_2635_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2646_ = lean_array_get_size(v_args_2595_);
v___x_2647_ = lean_nat_dec_lt(v_a_2601_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v_toCold_2648_; lean_object* v_options_2649_; uint8_t v_hasTrace_2650_; 
v_toCold_2648_ = lean_ctor_get(v___y_2605_, 0);
v_options_2649_ = lean_ctor_get(v_toCold_2648_, 2);
v_hasTrace_2650_ = lean_ctor_get_uint8(v_options_2649_, sizeof(void*)*1);
if (v_hasTrace_2650_ == 0)
{
goto v___jp_2638_;
}
else
{
lean_object* v_inheritedTraceOptions_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v_inheritedTraceOptions_2651_ = lean_ctor_get(v_toCold_2648_, 11);
v___x_2652_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2653_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2654_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2651_, v_options_2649_, v___x_2653_);
if (v___x_2654_ == 0)
{
goto v___jp_2638_;
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2655_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2593_);
v___x_2656_ = l_Nat_reprFast(v_val_2593_);
v___x_2657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
v___x_2658_ = l_Lean_MessageData_ofFormat(v___x_2657_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2655_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
lean_inc(v_a_2601_);
v___x_2662_ = l_Nat_reprFast(v_a_2601_);
v___x_2663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
v___x_2664_ = l_Lean_MessageData_ofFormat(v___x_2663_);
lean_inc_ref(v___x_2664_);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2661_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
lean_inc_ref(v_e_2596_);
v___x_2668_ = l_Lean_MessageData_ofExpr(v_e_2596_);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v___x_2664_);
v___x_2673_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2652_, v___x_2672_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
lean_inc(v_a_2601_);
v___x_2675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2592_, v_val_2593_, v_a_2601_, v___x_2635_, v_a_2674_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
v___y_2614_ = v___x_2675_;
goto v___jp_2613_;
}
else
{
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
return v___x_2673_;
}
}
}
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = lean_array_fget_borrowed(v_args_2595_, v_a_2601_);
v___x_2677_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2592_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
v___x_2679_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2593_, v_a_2601_, v_next_2597_, v_a_2678_);
lean_dec(v_a_2678_);
if (lean_obj_tag(v___x_2679_) == 1)
{
lean_object* v_val_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2781_; 
v_val_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2781_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_val_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2781_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; uint8_t v_foApprox_2685_; uint8_t v_ctxApprox_2686_; uint8_t v_quasiPatternApprox_2687_; uint8_t v_constApprox_2688_; uint8_t v_isDefEqStuckEx_2689_; uint8_t v_unificationHints_2690_; uint8_t v_assignSyntheticOpaque_2691_; uint8_t v_offsetCnstrs_2692_; uint8_t v_transparency_2693_; uint8_t v_etaStruct_2694_; uint8_t v_univApprox_2695_; uint8_t v_iota_2696_; uint8_t v_beta_2697_; uint8_t v_proj_2698_; uint8_t v_zeta_2699_; uint8_t v_zetaDelta_2700_; uint8_t v_zetaUnused_2701_; uint8_t v_zetaHave_2702_; uint8_t v_canUnfoldPredicateConfig_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2780_; 
v___x_2684_ = l_Lean_Meta_Context_config(v___y_2603_);
v_foApprox_2685_ = lean_ctor_get_uint8(v___x_2684_, 0);
v_ctxApprox_2686_ = lean_ctor_get_uint8(v___x_2684_, 1);
v_quasiPatternApprox_2687_ = lean_ctor_get_uint8(v___x_2684_, 2);
v_constApprox_2688_ = lean_ctor_get_uint8(v___x_2684_, 3);
v_isDefEqStuckEx_2689_ = lean_ctor_get_uint8(v___x_2684_, 4);
v_unificationHints_2690_ = lean_ctor_get_uint8(v___x_2684_, 5);
v_assignSyntheticOpaque_2691_ = lean_ctor_get_uint8(v___x_2684_, 7);
v_offsetCnstrs_2692_ = lean_ctor_get_uint8(v___x_2684_, 8);
v_transparency_2693_ = lean_ctor_get_uint8(v___x_2684_, 9);
v_etaStruct_2694_ = lean_ctor_get_uint8(v___x_2684_, 10);
v_univApprox_2695_ = lean_ctor_get_uint8(v___x_2684_, 11);
v_iota_2696_ = lean_ctor_get_uint8(v___x_2684_, 12);
v_beta_2697_ = lean_ctor_get_uint8(v___x_2684_, 13);
v_proj_2698_ = lean_ctor_get_uint8(v___x_2684_, 14);
v_zeta_2699_ = lean_ctor_get_uint8(v___x_2684_, 15);
v_zetaDelta_2700_ = lean_ctor_get_uint8(v___x_2684_, 16);
v_zetaUnused_2701_ = lean_ctor_get_uint8(v___x_2684_, 17);
v_zetaHave_2702_ = lean_ctor_get_uint8(v___x_2684_, 18);
v_canUnfoldPredicateConfig_2703_ = lean_ctor_get_uint8(v___x_2684_, 19);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2705_ = v___x_2684_;
v_isShared_2706_ = v_isSharedCheck_2780_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v___x_2684_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2780_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
uint8_t v_trackZetaDelta_2707_; lean_object* v_zetaDeltaSet_2708_; lean_object* v_lctx_2709_; lean_object* v_localInstances_2710_; lean_object* v_defEqCtx_x3f_2711_; lean_object* v_synthPendingDepth_2712_; lean_object* v_customCanUnfoldPredicate_x3f_2713_; uint8_t v_univApprox_2714_; uint8_t v_inTypeClassResolution_2715_; uint8_t v_cacheInferType_2716_; uint8_t v___x_2717_; lean_object* v___x_2719_; 
v_trackZetaDelta_2707_ = lean_ctor_get_uint8(v___y_2603_, sizeof(void*)*7);
v_zetaDeltaSet_2708_ = lean_ctor_get(v___y_2603_, 1);
v_lctx_2709_ = lean_ctor_get(v___y_2603_, 2);
v_localInstances_2710_ = lean_ctor_get(v___y_2603_, 3);
v_defEqCtx_x3f_2711_ = lean_ctor_get(v___y_2603_, 4);
v_synthPendingDepth_2712_ = lean_ctor_get(v___y_2603_, 5);
v_customCanUnfoldPredicate_x3f_2713_ = lean_ctor_get(v___y_2603_, 6);
v_univApprox_2714_ = lean_ctor_get_uint8(v___y_2603_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2715_ = lean_ctor_get_uint8(v___y_2603_, sizeof(void*)*7 + 2);
v_cacheInferType_2716_ = lean_ctor_get_uint8(v___y_2603_, sizeof(void*)*7 + 3);
v___x_2717_ = 0;
if (v_isShared_2706_ == 0)
{
v___x_2719_ = v___x_2705_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 0, v_foApprox_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 1, v_ctxApprox_2686_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 2, v_quasiPatternApprox_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 3, v_constApprox_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 4, v_isDefEqStuckEx_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 5, v_unificationHints_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 7, v_assignSyntheticOpaque_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 8, v_offsetCnstrs_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 9, v_transparency_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 10, v_etaStruct_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 11, v_univApprox_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 12, v_iota_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 13, v_beta_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 14, v_proj_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 15, v_zeta_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 16, v_zetaDelta_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 17, v_zetaUnused_2701_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 18, v_zetaHave_2702_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, 19, v_canUnfoldPredicateConfig_2703_);
v___x_2719_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
uint64_t v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v_transparency_2724_; lean_object* v___x_2725_; lean_object* v___y_2727_; uint8_t v___x_2773_; uint8_t v___x_2774_; 
lean_ctor_set_uint8(v___x_2719_, 6, v___x_2717_);
v___x_2720_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2719_);
v___x_2721_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set_uint64(v___x_2721_, sizeof(void*)*1, v___x_2720_);
lean_inc(v_customCanUnfoldPredicate_x3f_2713_);
lean_inc(v_synthPendingDepth_2712_);
lean_inc(v_defEqCtx_x3f_2711_);
lean_inc_ref(v_localInstances_2710_);
lean_inc_ref(v_lctx_2709_);
lean_inc(v_zetaDeltaSet_2708_);
lean_inc_ref(v___x_2721_);
v___x_2722_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_zetaDeltaSet_2708_);
lean_ctor_set(v___x_2722_, 2, v_lctx_2709_);
lean_ctor_set(v___x_2722_, 3, v_localInstances_2710_);
lean_ctor_set(v___x_2722_, 4, v_defEqCtx_x3f_2711_);
lean_ctor_set(v___x_2722_, 5, v_synthPendingDepth_2712_);
lean_ctor_set(v___x_2722_, 6, v_customCanUnfoldPredicate_x3f_2713_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7, v_trackZetaDelta_2707_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 1, v_univApprox_2714_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2715_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 3, v_cacheInferType_2716_);
v___x_2723_ = l_Lean_Meta_Context_config(v___x_2722_);
v_transparency_2724_ = lean_ctor_get_uint8(v___x_2723_, 9);
lean_dec_ref(v___x_2723_);
v___x_2725_ = lean_array_get_borrowed(v___x_2642_, v_params_2598_, v_val_2680_);
lean_dec(v_val_2680_);
v___x_2773_ = 2;
v___x_2774_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2724_, v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec_ref_known(v___x_2722_, 7);
v___x_2775_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2773_, v___x_2721_);
lean_inc(v_customCanUnfoldPredicate_x3f_2713_);
lean_inc(v_synthPendingDepth_2712_);
lean_inc(v_defEqCtx_x3f_2711_);
lean_inc_ref(v_localInstances_2710_);
lean_inc_ref(v_lctx_2709_);
lean_inc(v_zetaDeltaSet_2708_);
v___x_2776_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
lean_ctor_set(v___x_2776_, 1, v_zetaDeltaSet_2708_);
lean_ctor_set(v___x_2776_, 2, v_lctx_2709_);
lean_ctor_set(v___x_2776_, 3, v_localInstances_2710_);
lean_ctor_set(v___x_2776_, 4, v_defEqCtx_x3f_2711_);
lean_ctor_set(v___x_2776_, 5, v_synthPendingDepth_2712_);
lean_ctor_set(v___x_2776_, 6, v_customCanUnfoldPredicate_x3f_2713_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*7, v_trackZetaDelta_2707_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*7 + 1, v_univApprox_2714_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2715_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*7 + 3, v_cacheInferType_2716_);
lean_inc(v___x_2676_);
lean_inc(v___x_2725_);
v___x_2777_ = l_Lean_Meta_isExprDefEq(v___x_2725_, v___x_2676_, v___x_2776_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref_known(v___x_2776_, 7);
v___y_2727_ = v___x_2777_;
goto v___jp_2726_;
}
else
{
lean_object* v___x_2778_; 
lean_dec_ref_known(v___x_2721_, 1);
lean_inc(v___x_2676_);
lean_inc(v___x_2725_);
v___x_2778_ = l_Lean_Meta_isExprDefEq(v___x_2725_, v___x_2676_, v___x_2722_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec_ref_known(v___x_2722_, 7);
v___y_2727_ = v___x_2778_;
goto v___jp_2726_;
}
v___jp_2726_:
{
if (lean_obj_tag(v___y_2727_) == 0)
{
lean_object* v_a_2728_; uint8_t v___x_2729_; 
v_a_2728_ = lean_ctor_get(v___y_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___y_2727_, 1);
v___x_2729_ = lean_unbox(v_a_2728_);
lean_dec(v_a_2728_);
if (v___x_2729_ == 0)
{
lean_object* v_toCold_2730_; lean_object* v_options_2731_; uint8_t v_hasTrace_2732_; 
v_toCold_2730_ = lean_ctor_get(v___y_2605_, 0);
v_options_2731_ = lean_ctor_get(v_toCold_2730_, 2);
v_hasTrace_2732_ = lean_ctor_get_uint8(v_options_2731_, sizeof(void*)*1);
if (v_hasTrace_2732_ == 0)
{
lean_del_object(v___x_2682_);
goto v___jp_2640_;
}
else
{
lean_object* v_inheritedTraceOptions_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v_inheritedTraceOptions_2733_ = lean_ctor_get(v_toCold_2730_, 11);
v___x_2734_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2735_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2733_, v_options_2731_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_del_object(v___x_2682_);
goto v___jp_2640_;
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2737_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2593_);
v___x_2738_ = l_Nat_reprFast(v_val_2593_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set_tag(v___x_2682_, 3);
lean_ctor_set(v___x_2682_, 0, v___x_2738_);
v___x_2740_ = v___x_2682_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2741_ = l_Lean_MessageData_ofFormat(v___x_2740_);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2737_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
lean_inc(v_a_2601_);
v___x_2745_ = l_Nat_reprFast(v_a_2601_);
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
lean_inc_ref(v_e_2596_);
v___x_2751_ = l_Lean_MessageData_ofExpr(v_e_2596_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
lean_inc(v___x_2725_);
v___x_2755_ = l_Lean_MessageData_ofExpr(v___x_2725_);
v___x_2756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_inc(v___x_2676_);
v___x_2759_ = l_Lean_MessageData_ofExpr(v___x_2676_);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2734_, v___x_2760_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
lean_inc(v_a_2601_);
v___x_2763_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2592_, v_val_2593_, v_a_2601_, v___x_2635_, v_a_2762_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
v___y_2614_ = v___x_2763_;
goto v___jp_2613_;
}
else
{
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
return v___x_2761_;
}
}
}
}
}
else
{
lean_del_object(v___x_2682_);
v_a_2609_ = v___x_2635_;
goto v___jp_2608_;
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_del_object(v___x_2682_);
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
v_a_2765_ = lean_ctor_get(v___y_2727_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___y_2727_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___y_2727_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___y_2727_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
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
lean_object* v___x_2782_; uint8_t v___x_2783_; lean_object* v___x_2784_; 
lean_dec(v___x_2679_);
v___x_2782_ = lean_unsigned_to_nat(0u);
v___x_2783_ = 0;
lean_inc(v___x_2676_);
lean_inc(v_a_2601_);
v___x_2784_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2592_, v_val_2593_, v_a_2601_, v_next_2597_, v___x_2599_, v___x_2600_, v___x_2599_, v_params_2598_, v___x_2676_, v___x_2782_, v___x_2783_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; uint8_t v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = lean_unbox(v_a_2785_);
lean_dec(v_a_2785_);
if (v___x_2786_ == 0)
{
lean_object* v_toCold_2787_; lean_object* v_options_2788_; uint8_t v_hasTrace_2789_; 
v_toCold_2787_ = lean_ctor_get(v___y_2605_, 0);
v_options_2788_ = lean_ctor_get(v_toCold_2787_, 2);
v_hasTrace_2789_ = lean_ctor_get_uint8(v_options_2788_, sizeof(void*)*1);
if (v_hasTrace_2789_ == 0)
{
goto v___jp_2636_;
}
else
{
lean_object* v_inheritedTraceOptions_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v_inheritedTraceOptions_2790_ = lean_ctor_get(v_toCold_2787_, 11);
v___x_2791_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2792_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2790_, v_options_2788_, v___x_2792_);
if (v___x_2793_ == 0)
{
goto v___jp_2636_;
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2794_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2593_);
v___x_2795_ = l_Nat_reprFast(v_val_2593_);
v___x_2796_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
v___x_2797_ = l_Lean_MessageData_ofFormat(v___x_2796_);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2794_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
lean_inc(v_a_2601_);
v___x_2801_ = l_Nat_reprFast(v_a_2601_);
v___x_2802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
v___x_2803_ = l_Lean_MessageData_ofFormat(v___x_2802_);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2800_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
v___x_2805_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
lean_inc_ref(v_e_2596_);
v___x_2807_ = l_Lean_MessageData_ofExpr(v_e_2596_);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
lean_inc(v___x_2676_);
v___x_2811_ = l_Lean_MessageData_ofExpr(v___x_2676_);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2812_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
v___x_2815_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2791_, v___x_2814_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
lean_inc(v_a_2601_);
v___x_2817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2592_, v_val_2593_, v_a_2601_, v___x_2635_, v_a_2816_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
v___y_2614_ = v___x_2817_;
goto v___jp_2613_;
}
else
{
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
return v___x_2815_;
}
}
}
}
else
{
v_a_2609_ = v___x_2635_;
goto v___jp_2608_;
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
v_a_2818_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2784_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2784_);
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
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
v_a_2826_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2677_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2677_);
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
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
v_a_2834_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2643_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2643_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
v___jp_2636_:
{
lean_object* v___x_2637_; 
lean_inc(v_a_2601_);
v___x_2637_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2592_, v_val_2593_, v_a_2601_, v___x_2635_, v___x_2635_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
v___y_2614_ = v___x_2637_;
goto v___jp_2613_;
}
v___jp_2638_:
{
lean_object* v___x_2639_; 
lean_inc(v_a_2601_);
v___x_2639_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2592_, v_val_2593_, v_a_2601_, v___x_2635_, v___x_2635_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
v___y_2614_ = v___x_2639_;
goto v___jp_2613_;
}
v___jp_2640_:
{
lean_object* v___x_2641_; 
lean_inc(v_a_2601_);
v___x_2641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2592_, v_val_2593_, v_a_2601_, v___x_2635_, v___x_2635_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
v___y_2614_ = v___x_2641_;
goto v___jp_2613_;
}
}
v___jp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_unsigned_to_nat(1u);
v___x_2611_ = lean_nat_add(v_a_2601_, v___x_2610_);
lean_dec(v_a_2601_);
v_a_2601_ = v___x_2611_;
v_b_2602_ = v_a_2609_;
goto _start;
}
v___jp_2613_:
{
if (lean_obj_tag(v___y_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2624_; 
v_a_2615_ = lean_ctor_get(v___y_2614_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___y_2614_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2617_ = v___y_2614_;
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___y_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
if (lean_obj_tag(v_a_2615_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
v_a_2619_ = lean_ctor_get(v_a_2615_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v_a_2615_, 1);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v_a_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v_a_2623_; 
lean_del_object(v___x_2617_);
v_a_2623_ = lean_ctor_get(v_a_2615_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v_a_2615_, 1);
v_a_2609_ = v_a_2623_;
goto v___jp_2608_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2596_);
lean_dec(v_val_2593_);
v_a_2625_ = lean_ctor_get(v___y_2614_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___y_2614_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___y_2614_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___y_2614_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2592_ = stack[0].m_obj;
lean_object* v_val_2593_ = stack[1].m_obj;
lean_object* v_upperBound_2594_ = stack[2].m_obj;
lean_object* v_args_2595_ = stack[3].m_obj;
lean_object* v_e_2596_ = stack[4].m_obj;
lean_object* v_next_2597_ = stack[5].m_obj;
lean_object* v_params_2598_ = stack[6].m_obj;
lean_object* v___x_2599_ = stack[7].m_obj;
lean_object* v___x_2600_ = stack[8].m_obj;
lean_object* v_a_2601_ = stack[9].m_obj;
lean_object* v_b_2602_ = stack[10].m_obj;
lean_object* v___y_2603_ = stack[11].m_obj;
lean_object* v___y_2604_ = stack[12].m_obj;
lean_object* v___y_2605_ = stack[13].m_obj;
lean_object* v___y_2606_ = stack[14].m_obj;
lean_object* v_res_2842_;
v_res_2842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2592_, v_val_2593_, v_upperBound_2594_, v_args_2595_, v_e_2596_, v_next_2597_, v_params_2598_, v___x_2599_, v___x_2600_, v_a_2601_, v_b_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
stack->m_obj
 = v_res_2842_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2843_, lean_object* v_val_2844_, lean_object* v_upperBound_2845_, lean_object* v_args_2846_, lean_object* v_e_2847_, lean_object* v_next_2848_, lean_object* v_params_2849_, lean_object* v___x_2850_, lean_object* v___x_2851_, lean_object* v_a_2852_, lean_object* v_b_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2843_, v_val_2844_, v_upperBound_2845_, v_args_2846_, v_e_2847_, v_next_2848_, v_params_2849_, v___x_2850_, v___x_2851_, v_a_2852_, v_b_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___x_2851_);
lean_dec(v___x_2850_);
lean_dec_ref(v_params_2849_);
lean_dec(v_next_2848_);
lean_dec_ref(v_args_2846_);
lean_dec(v_upperBound_2845_);
lean_dec(v_val_2843_);
return v_res_2859_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2862_, lean_object* v___x_2863_, lean_object* v_val_2864_, lean_object* v_e_2865_, lean_object* v_next_2866_, lean_object* v_params_2867_, lean_object* v___x_2868_, lean_object* v___x_2869_, lean_object* v_x_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
if (lean_obj_tag(v_x_2870_) == 5)
{
lean_object* v_fn_2878_; lean_object* v_arg_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_fn_2878_ = lean_ctor_get(v_x_2870_, 0);
lean_inc_ref(v_fn_2878_);
v_arg_2879_ = lean_ctor_get(v_x_2870_, 1);
lean_inc_ref(v_arg_2879_);
lean_dec_ref_known(v_x_2870_, 2);
v___x_2880_ = lean_array_set(v_x_2871_, v_x_2872_, v_arg_2879_);
v___x_2881_ = lean_unsigned_to_nat(1u);
v___x_2882_ = lean_nat_sub(v_x_2872_, v___x_2881_);
lean_dec(v_x_2872_);
v_x_2870_ = v_fn_2878_;
v_x_2871_ = v___x_2880_;
v_x_2872_ = v___x_2882_;
goto _start;
}
else
{
uint8_t v___x_2884_; 
lean_dec(v_x_2872_);
v___x_2884_ = l_Lean_Expr_isConst(v_x_2870_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec_ref(v_x_2871_);
lean_dec_ref(v_x_2870_);
lean_dec_ref(v_e_2865_);
v___x_2885_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2887_ = l_Lean_Expr_constName_x21(v_x_2870_);
lean_dec_ref(v_x_2870_);
v___x_2888_ = lean_unsigned_to_nat(0u);
v___x_2889_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2887_, v_preDefs_2862_, v___x_2888_);
lean_dec(v___x_2887_);
if (lean_obj_tag(v___x_2889_) == 1)
{
lean_object* v_val_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_val_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_val_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_array_get_borrowed(v___x_2888_, v___x_2863_, v_val_2890_);
v___x_2893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2864_, v_val_2890_, v___x_2892_, v_x_2871_, v_e_2865_, v_next_2866_, v_params_2867_, v___x_2868_, v___x_2869_, v___x_2888_, v___x_2891_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec_ref(v_x_2871_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2901_; 
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2901_ == 0)
{
lean_object* v_unused_2902_; 
v_unused_2902_ = lean_ctor_get(v___x_2893_, 0);
lean_dec(v_unused_2902_);
v___x_2895_ = v___x_2893_;
v_isShared_2896_ = v_isSharedCheck_2901_;
goto v_resetjp_2894_;
}
else
{
lean_dec(v___x_2893_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2901_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2897_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2897_);
v___x_2899_ = v___x_2895_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
v_a_2903_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2893_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2893_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
lean_dec(v___x_2889_);
lean_dec_ref(v_x_2871_);
lean_dec_ref(v_e_2865_);
v___x_2911_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
return v___x_2912_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_2862_ = stack[0].m_obj;
lean_object* v___x_2863_ = stack[1].m_obj;
lean_object* v_val_2864_ = stack[2].m_obj;
lean_object* v_e_2865_ = stack[3].m_obj;
lean_object* v_next_2866_ = stack[4].m_obj;
lean_object* v_params_2867_ = stack[5].m_obj;
lean_object* v___x_2868_ = stack[6].m_obj;
lean_object* v___x_2869_ = stack[7].m_obj;
lean_object* v_x_2870_ = stack[8].m_obj;
lean_object* v_x_2871_ = stack[9].m_obj;
lean_object* v_x_2872_ = stack[10].m_obj;
lean_object* v___y_2873_ = stack[11].m_obj;
lean_object* v___y_2874_ = stack[12].m_obj;
lean_object* v___y_2875_ = stack[13].m_obj;
lean_object* v___y_2876_ = stack[14].m_obj;
lean_object* v_res_2913_;
v_res_2913_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2862_, v___x_2863_, v_val_2864_, v_e_2865_, v_next_2866_, v_params_2867_, v___x_2868_, v___x_2869_, v_x_2870_, v_x_2871_, v_x_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
stack->m_obj
 = v_res_2913_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2914_, lean_object* v___x_2915_, lean_object* v_val_2916_, lean_object* v_e_2917_, lean_object* v_next_2918_, lean_object* v_params_2919_, lean_object* v___x_2920_, lean_object* v___x_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v_x_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2914_, v___x_2915_, v_val_2916_, v_e_2917_, v_next_2918_, v_params_2919_, v___x_2920_, v___x_2921_, v_x_2922_, v_x_2923_, v_x_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___x_2921_);
lean_dec(v___x_2920_);
lean_dec_ref(v_params_2919_);
lean_dec(v_next_2918_);
lean_dec(v_val_2916_);
lean_dec_ref(v___x_2915_);
lean_dec_ref(v_preDefs_2914_);
return v_res_2930_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2931_, lean_object* v___x_2932_, lean_object* v_val_2933_, lean_object* v_a_2934_, lean_object* v_params_2935_, lean_object* v___x_2936_, lean_object* v___x_2937_, lean_object* v_e_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_dummy_2944_; lean_object* v_nargs_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_dummy_2944_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2945_ = l_Lean_Expr_getAppNumArgs(v_e_2938_);
lean_inc(v_nargs_2945_);
v___x_2946_ = lean_mk_array(v_nargs_2945_, v_dummy_2944_);
v___x_2947_ = lean_unsigned_to_nat(1u);
v___x_2948_ = lean_nat_sub(v_nargs_2945_, v___x_2947_);
lean_dec(v_nargs_2945_);
lean_inc_ref(v_e_2938_);
v___x_2949_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2931_, v___x_2932_, v_val_2933_, v_e_2938_, v_a_2934_, v_params_2935_, v___x_2936_, v___x_2937_, v_e_2938_, v___x_2946_, v___x_2948_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
return v___x_2949_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_2931_ = stack[0].m_obj;
lean_object* v___x_2932_ = stack[1].m_obj;
lean_object* v_val_2933_ = stack[2].m_obj;
lean_object* v_a_2934_ = stack[3].m_obj;
lean_object* v_params_2935_ = stack[4].m_obj;
lean_object* v___x_2936_ = stack[5].m_obj;
lean_object* v___x_2937_ = stack[6].m_obj;
lean_object* v_e_2938_ = stack[7].m_obj;
lean_object* v___y_2939_ = stack[8].m_obj;
lean_object* v___y_2940_ = stack[9].m_obj;
lean_object* v___y_2941_ = stack[10].m_obj;
lean_object* v___y_2942_ = stack[11].m_obj;
lean_object* v_res_2950_;
v_res_2950_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2931_, v___x_2932_, v_val_2933_, v_a_2934_, v_params_2935_, v___x_2936_, v___x_2937_, v_e_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
stack->m_obj
 = v_res_2950_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2951_, lean_object* v___x_2952_, lean_object* v_val_2953_, lean_object* v_a_2954_, lean_object* v_params_2955_, lean_object* v___x_2956_, lean_object* v___x_2957_, lean_object* v_e_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2951_, v___x_2952_, v_val_2953_, v_a_2954_, v_params_2955_, v___x_2956_, v___x_2957_, v_e_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___x_2957_);
lean_dec(v___x_2956_);
lean_dec_ref(v_params_2955_);
lean_dec(v_a_2954_);
lean_dec(v_val_2953_);
lean_dec_ref(v___x_2952_);
lean_dec_ref(v_preDefs_2951_);
return v_res_2964_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2968_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2969_ = lean_unsigned_to_nat(6u);
v___x_2970_ = lean_unsigned_to_nat(201u);
v___x_2971_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2972_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2973_ = l_mkPanicMessageWithDecl(v___x_2972_, v___x_2971_, v___x_2970_, v___x_2969_, v___x_2968_);
return v___x_2973_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2974_, lean_object* v___x_2975_, lean_object* v_a_2976_, lean_object* v_preDefs_2977_, lean_object* v_val_2978_, lean_object* v___f_2979_, lean_object* v___x_2980_, lean_object* v_params_2981_, lean_object* v_body_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_array_get_size(v_params_2981_);
v___x_2989_ = lean_array_get(v___x_2974_, v___x_2975_, v_a_2976_);
v___x_2990_ = lean_nat_dec_eq(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_dec(v___x_2989_);
lean_dec_ref(v_body_2982_);
lean_dec_ref(v_params_2981_);
lean_dec_ref(v___f_2979_);
lean_dec(v_val_2978_);
lean_dec_ref(v_preDefs_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v___x_2975_);
v___x_2991_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2992_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2991_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
return v___x_2992_;
}
else
{
lean_object* v___f_2993_; uint8_t v___x_2994_; lean_object* v___x_2995_; 
v___f_2993_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2993_, 0, v_preDefs_2977_);
lean_closure_set(v___f_2993_, 1, v___x_2975_);
lean_closure_set(v___f_2993_, 2, v_val_2978_);
lean_closure_set(v___f_2993_, 3, v_a_2976_);
lean_closure_set(v___f_2993_, 4, v_params_2981_);
lean_closure_set(v___f_2993_, 5, v___x_2988_);
lean_closure_set(v___f_2993_, 6, v___x_2989_);
v___x_2994_ = 0;
v___x_2995_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2982_, v___f_2993_, v___f_2979_, v___x_2994_, v___x_2990_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; 
v_unused_3003_ = lean_ctor_get(v___x_2995_, 0);
lean_dec(v_unused_3003_);
v___x_2997_ = v___x_2995_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_dec(v___x_2995_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_2980_);
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2980_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
v_a_3004_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2995_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2995_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2974_ = stack[0].m_obj;
lean_object* v___x_2975_ = stack[1].m_obj;
lean_object* v_a_2976_ = stack[2].m_obj;
lean_object* v_preDefs_2977_ = stack[3].m_obj;
lean_object* v_val_2978_ = stack[4].m_obj;
lean_object* v___f_2979_ = stack[5].m_obj;
lean_object* v___x_2980_ = stack[6].m_obj;
lean_object* v_params_2981_ = stack[7].m_obj;
lean_object* v_body_2982_ = stack[8].m_obj;
lean_object* v___y_2983_ = stack[9].m_obj;
lean_object* v___y_2984_ = stack[10].m_obj;
lean_object* v___y_2985_ = stack[11].m_obj;
lean_object* v___y_2986_ = stack[12].m_obj;
lean_object* v_res_3012_;
v_res_3012_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2974_, v___x_2975_, v_a_2976_, v_preDefs_2977_, v_val_2978_, v___f_2979_, v___x_2980_, v_params_2981_, v_body_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
stack->m_obj
 = v_res_3012_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_3013_, lean_object* v___x_3014_, lean_object* v_a_3015_, lean_object* v_preDefs_3016_, lean_object* v_val_3017_, lean_object* v___f_3018_, lean_object* v___x_3019_, lean_object* v_params_3020_, lean_object* v_body_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_3013_, v___x_3014_, v_a_3015_, v_preDefs_3016_, v_val_3017_, v___f_3018_, v___x_3019_, v_params_3020_, v_body_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___x_3013_);
return v_res_3027_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v_e_3028_);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3028_ = stack[0].m_obj;
lean_object* v___y_3029_ = stack[1].m_obj;
lean_object* v___y_3030_ = stack[2].m_obj;
lean_object* v___y_3031_ = stack[3].m_obj;
lean_object* v___y_3032_ = stack[4].m_obj;
lean_object* v_res_3036_;
v_res_3036_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
stack->m_obj
 = v_res_3036_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
return v_res_3043_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v___x_3045_, lean_object* v_preDefs_3046_, lean_object* v_val_3047_, lean_object* v_upperBound_3048_, lean_object* v_a_3049_, lean_object* v_b_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
uint8_t v___x_3056_; 
v___x_3056_ = lean_nat_dec_lt(v_a_3049_, v_upperBound_3048_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
lean_dec(v_a_3049_);
lean_dec(v_val_3047_);
lean_dec_ref(v_preDefs_3046_);
lean_dec_ref(v___x_3045_);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_b_3050_);
return v___x_3057_;
}
else
{
lean_object* v___x_3058_; lean_object* v_value_3059_; lean_object* v___f_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___f_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; 
v___x_3058_ = lean_array_fget_borrowed(v_preDefs_3046_, v_a_3049_);
v_value_3059_ = lean_ctor_get(v___x_3058_, 7);
v___f_3060_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3062_ = lean_box(0);
lean_inc(v_val_3047_);
lean_inc_ref(v_preDefs_3046_);
lean_inc(v_a_3049_);
lean_inc_ref(v___x_3045_);
v___f_3063_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3063_, 0, v___x_3061_);
lean_closure_set(v___f_3063_, 1, v___x_3045_);
lean_closure_set(v___f_3063_, 2, v_a_3049_);
lean_closure_set(v___f_3063_, 3, v_preDefs_3046_);
lean_closure_set(v___f_3063_, 4, v_val_3047_);
lean_closure_set(v___f_3063_, 5, v___f_3060_);
lean_closure_set(v___f_3063_, 6, v___x_3062_);
v___x_3064_ = 0;
lean_inc_ref(v_value_3059_);
v___x_3065_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3059_, v___f_3063_, v___x_3064_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_dec_ref_known(v___x_3065_, 1);
v___x_3066_ = lean_unsigned_to_nat(1u);
v___x_3067_ = lean_nat_add(v_a_3049_, v___x_3066_);
lean_dec(v_a_3049_);
v_a_3049_ = v___x_3067_;
v_b_3050_ = v___x_3062_;
goto _start;
}
else
{
lean_dec(v_a_3049_);
lean_dec(v_val_3047_);
lean_dec_ref(v_preDefs_3046_);
lean_dec_ref(v___x_3045_);
return v___x_3065_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3045_ = stack[0].m_obj;
lean_object* v_preDefs_3046_ = stack[1].m_obj;
lean_object* v_val_3047_ = stack[2].m_obj;
lean_object* v_upperBound_3048_ = stack[3].m_obj;
lean_object* v_a_3049_ = stack[4].m_obj;
lean_object* v_b_3050_ = stack[5].m_obj;
lean_object* v___y_3051_ = stack[6].m_obj;
lean_object* v___y_3052_ = stack[7].m_obj;
lean_object* v___y_3053_ = stack[8].m_obj;
lean_object* v___y_3054_ = stack[9].m_obj;
lean_object* v_res_3069_;
v_res_3069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3045_, v_preDefs_3046_, v_val_3047_, v_upperBound_3048_, v_a_3049_, v_b_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
stack->m_obj
 = v_res_3069_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v___x_3070_, lean_object* v_preDefs_3071_, lean_object* v_val_3072_, lean_object* v_upperBound_3073_, lean_object* v_a_3074_, lean_object* v_b_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3070_, v_preDefs_3071_, v_val_3072_, v_upperBound_3073_, v_a_3074_, v_b_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v_upperBound_3073_);
return v_res_3081_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3084_ = l_Lean_stringToMessageData(v___x_3083_);
return v___x_3084_;
}
}
lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
size_t v_sz_3091_; size_t v___x_3092_; lean_object* v___x_3093_; 
v_sz_3091_ = lean_array_size(v_preDefs_3085_);
v___x_3092_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3085_);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3091_, v___x_3092_, v_preDefs_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; size_t v_sz_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc_n(v_a_3094_, 2);
lean_dec_ref_known(v___x_3093_, 1);
v_sz_3095_ = lean_array_size(v_a_3094_);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3095_, v___x_3092_, v_a_3094_);
v___x_3097_ = l_Lean_Elab_FixedParams_Info_init(v_a_3094_);
v___x_3098_ = lean_st_mk_ref(v___x_3097_);
v___x_3099_ = lean_st_ref_take(v___x_3098_);
v___x_3100_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3099_);
v___x_3101_ = lean_st_ref_put(v___x_3098_, v___x_3100_);
v___x_3102_ = lean_array_get_size(v_preDefs_3085_);
v___x_3103_ = lean_unsigned_to_nat(0u);
v___x_3104_ = lean_box(0);
lean_inc(v___x_3098_);
v___x_3105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3096_, v_preDefs_3085_, v___x_3098_, v___x_3102_, v___x_3103_, v___x_3104_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3145_; 
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; 
v_unused_3146_ = lean_ctor_get(v___x_3105_, 0);
lean_dec(v_unused_3146_);
v___x_3107_ = v___x_3105_;
v_isShared_3108_ = v_isSharedCheck_3145_;
goto v_resetjp_3106_;
}
else
{
lean_dec(v___x_3105_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3145_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v_toCold_3110_; lean_object* v_options_3111_; uint8_t v_hasTrace_3112_; 
v___x_3109_ = lean_st_ref_get(v___x_3098_);
lean_dec(v___x_3098_);
v_toCold_3110_ = lean_ctor_get(v_a_3088_, 0);
v_options_3111_ = lean_ctor_get(v_toCold_3110_, 2);
v_hasTrace_3112_ = lean_ctor_get_uint8(v_options_3111_, sizeof(void*)*1);
if (v_hasTrace_3112_ == 0)
{
lean_object* v___x_3114_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3109_);
v___x_3114_ = v___x_3107_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v_inheritedTraceOptions_3116_ = lean_ctor_get(v_toCold_3110_, 11);
v___x_3117_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3118_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3119_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3116_, v_options_3111_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3121_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3109_);
v___x_3121_ = v___x_3107_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3109_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_del_object(v___x_3107_);
v___x_3123_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3109_);
v___x_3124_ = l_Lean_Elab_FixedParams_Info_format(v___x_3109_);
v___x_3125_ = l_Std_Format_indentD(v___x_3124_);
v___x_3126_ = l_Lean_MessageData_ofFormat(v___x_3125_);
v___x_3127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3123_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3117_, v___x_3127_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v___x_3128_, 0);
lean_dec(v_unused_3136_);
v___x_3130_ = v___x_3128_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_dec(v___x_3128_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3109_);
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3109_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v___x_3109_);
v_a_3137_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3128_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3128_);
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
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v___x_3098_);
v_a_3147_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3105_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3105_);
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
lean_dec_ref(v_preDefs_3085_);
v_a_3155_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3093_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3093_);
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
LEAN_EXPORT void l_Lean_Elab_getFixedParamsInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_3085_ = stack[0].m_obj;
lean_object* v_a_3086_ = stack[1].m_obj;
lean_object* v_a_3087_ = stack[2].m_obj;
lean_object* v_a_3088_ = stack[3].m_obj;
lean_object* v_a_3089_ = stack[4].m_obj;
lean_object* v_res_3163_;
v_res_3163_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
stack->m_obj
 = v_res_3163_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
lean_dec_ref(v_a_3165_);
return v_res_3170_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3171_, lean_object* v_val_3172_, lean_object* v_next_3173_, lean_object* v_next_3174_, lean_object* v___x_3175_, lean_object* v___x_3176_, lean_object* v_upperBound_3177_, lean_object* v_params_3178_, lean_object* v___x_3179_, lean_object* v_inst_3180_, lean_object* v_R_3181_, lean_object* v_a_3182_, uint8_t v_b_3183_, lean_object* v_c_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3171_, v_val_3172_, v_next_3173_, v_next_3174_, v___x_3175_, v___x_3176_, v_upperBound_3177_, v_params_3178_, v___x_3179_, v_a_3182_, v_b_3183_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3171_ = stack[0].m_obj;
lean_object* v_val_3172_ = stack[1].m_obj;
lean_object* v_next_3173_ = stack[2].m_obj;
lean_object* v_next_3174_ = stack[3].m_obj;
lean_object* v___x_3175_ = stack[4].m_obj;
lean_object* v___x_3176_ = stack[5].m_obj;
lean_object* v_upperBound_3177_ = stack[6].m_obj;
lean_object* v_params_3178_ = stack[7].m_obj;
lean_object* v___x_3179_ = stack[8].m_obj;
lean_object* v_a_3182_ = stack[11].m_obj;
uint8_t v_b_3183_ = stack[12].m_num;
lean_object* v___y_3185_ = stack[14].m_obj;
lean_object* v___y_3186_ = stack[15].m_obj;
lean_object* v___y_3187_ = stack[16].m_obj;
lean_object* v___y_3188_ = stack[17].m_obj;
lean_object* v_res_3191_;
v_res_3191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3171_, v_val_3172_, v_next_3173_, v_next_3174_, v___x_3175_, v___x_3176_, v_upperBound_3177_, v_params_3178_, v___x_3179_, lean_box(0), lean_box(0), v_a_3182_, v_b_3183_, lean_box(0), v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
stack->m_obj
 = v_res_3191_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3192_ = _args[0];
lean_object* v_val_3193_ = _args[1];
lean_object* v_next_3194_ = _args[2];
lean_object* v_next_3195_ = _args[3];
lean_object* v___x_3196_ = _args[4];
lean_object* v___x_3197_ = _args[5];
lean_object* v_upperBound_3198_ = _args[6];
lean_object* v_params_3199_ = _args[7];
lean_object* v___x_3200_ = _args[8];
lean_object* v_inst_3201_ = _args[9];
lean_object* v_R_3202_ = _args[10];
lean_object* v_a_3203_ = _args[11];
lean_object* v_b_3204_ = _args[12];
lean_object* v_c_3205_ = _args[13];
lean_object* v___y_3206_ = _args[14];
lean_object* v___y_3207_ = _args[15];
lean_object* v___y_3208_ = _args[16];
lean_object* v___y_3209_ = _args[17];
lean_object* v___y_3210_ = _args[18];
_start:
{
uint8_t v_b_boxed_3211_; lean_object* v_res_3212_; 
v_b_boxed_3211_ = lean_unbox(v_b_3204_);
v_res_3212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3192_, v_val_3193_, v_next_3194_, v_next_3195_, v___x_3196_, v___x_3197_, v_upperBound_3198_, v_params_3199_, v___x_3200_, v_inst_3201_, v_R_3202_, v_a_3203_, v_b_boxed_3211_, v_c_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v_params_3199_);
lean_dec(v_upperBound_3198_);
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
lean_dec(v_next_3195_);
lean_dec(v_val_3193_);
lean_dec(v_val_3192_);
return v_res_3212_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3213_, lean_object* v_val_3214_, lean_object* v_upperBound_3215_, lean_object* v_args_3216_, lean_object* v_e_3217_, lean_object* v_next_3218_, lean_object* v_params_3219_, lean_object* v___x_3220_, lean_object* v___x_3221_, lean_object* v_inst_3222_, lean_object* v_R_3223_, lean_object* v_a_3224_, lean_object* v_b_3225_, lean_object* v_c_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3213_, v_val_3214_, v_upperBound_3215_, v_args_3216_, v_e_3217_, v_next_3218_, v_params_3219_, v___x_3220_, v___x_3221_, v_a_3224_, v_b_3225_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3213_ = stack[0].m_obj;
lean_object* v_val_3214_ = stack[1].m_obj;
lean_object* v_upperBound_3215_ = stack[2].m_obj;
lean_object* v_args_3216_ = stack[3].m_obj;
lean_object* v_e_3217_ = stack[4].m_obj;
lean_object* v_next_3218_ = stack[5].m_obj;
lean_object* v_params_3219_ = stack[6].m_obj;
lean_object* v___x_3220_ = stack[7].m_obj;
lean_object* v___x_3221_ = stack[8].m_obj;
lean_object* v_a_3224_ = stack[11].m_obj;
lean_object* v_b_3225_ = stack[12].m_obj;
lean_object* v___y_3227_ = stack[14].m_obj;
lean_object* v___y_3228_ = stack[15].m_obj;
lean_object* v___y_3229_ = stack[16].m_obj;
lean_object* v___y_3230_ = stack[17].m_obj;
lean_object* v_res_3233_;
v_res_3233_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3213_, v_val_3214_, v_upperBound_3215_, v_args_3216_, v_e_3217_, v_next_3218_, v_params_3219_, v___x_3220_, v___x_3221_, lean_box(0), lean_box(0), v_a_3224_, v_b_3225_, lean_box(0), v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
stack->m_obj
 = v_res_3233_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3234_ = _args[0];
lean_object* v_val_3235_ = _args[1];
lean_object* v_upperBound_3236_ = _args[2];
lean_object* v_args_3237_ = _args[3];
lean_object* v_e_3238_ = _args[4];
lean_object* v_next_3239_ = _args[5];
lean_object* v_params_3240_ = _args[6];
lean_object* v___x_3241_ = _args[7];
lean_object* v___x_3242_ = _args[8];
lean_object* v_inst_3243_ = _args[9];
lean_object* v_R_3244_ = _args[10];
lean_object* v_a_3245_ = _args[11];
lean_object* v_b_3246_ = _args[12];
lean_object* v_c_3247_ = _args[13];
lean_object* v___y_3248_ = _args[14];
lean_object* v___y_3249_ = _args[15];
lean_object* v___y_3250_ = _args[16];
lean_object* v___y_3251_ = _args[17];
lean_object* v___y_3252_ = _args[18];
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3234_, v_val_3235_, v_upperBound_3236_, v_args_3237_, v_e_3238_, v_next_3239_, v_params_3240_, v___x_3241_, v___x_3242_, v_inst_3243_, v_R_3244_, v_a_3245_, v_b_3246_, v_c_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___x_3242_);
lean_dec(v___x_3241_);
lean_dec_ref(v_params_3240_);
lean_dec(v_next_3239_);
lean_dec_ref(v_args_3237_);
lean_dec(v_upperBound_3236_);
lean_dec(v_val_3234_);
return v_res_3253_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v___x_3254_, lean_object* v_preDefs_3255_, lean_object* v_val_3256_, lean_object* v_upperBound_3257_, lean_object* v_inst_3258_, lean_object* v_R_3259_, lean_object* v_a_3260_, lean_object* v_b_3261_, lean_object* v_c_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3254_, v_preDefs_3255_, v_val_3256_, v_upperBound_3257_, v_a_3260_, v_b_3261_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
return v___x_3268_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3254_ = stack[0].m_obj;
lean_object* v_preDefs_3255_ = stack[1].m_obj;
lean_object* v_val_3256_ = stack[2].m_obj;
lean_object* v_upperBound_3257_ = stack[3].m_obj;
lean_object* v_a_3260_ = stack[6].m_obj;
lean_object* v_b_3261_ = stack[7].m_obj;
lean_object* v___y_3263_ = stack[9].m_obj;
lean_object* v___y_3264_ = stack[10].m_obj;
lean_object* v___y_3265_ = stack[11].m_obj;
lean_object* v___y_3266_ = stack[12].m_obj;
lean_object* v_res_3269_;
v_res_3269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3254_, v_preDefs_3255_, v_val_3256_, v_upperBound_3257_, lean_box(0), lean_box(0), v_a_3260_, v_b_3261_, lean_box(0), v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
stack->m_obj
 = v_res_3269_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v___x_3270_, lean_object* v_preDefs_3271_, lean_object* v_val_3272_, lean_object* v_upperBound_3273_, lean_object* v_inst_3274_, lean_object* v_R_3275_, lean_object* v_a_3276_, lean_object* v_b_3277_, lean_object* v_c_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3270_, v_preDefs_3271_, v_val_3272_, v_upperBound_3273_, v_inst_3274_, v_R_3275_, v_a_3276_, v_b_3277_, v_c_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v_upperBound_3273_);
return v_res_3284_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3285_, lean_object* v___x_3286_, lean_object* v_pre_3287_, lean_object* v_post_3288_, uint8_t v_usedLetOnly_3289_, uint8_t v_skipConstInApp_3290_, uint8_t v_skipInstances_3291_, lean_object* v___x_3292_, lean_object* v_inst_3293_, lean_object* v_R_3294_, lean_object* v_a_3295_, lean_object* v_b_3296_, lean_object* v_c_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___x_3304_; 
v___x_3304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3285_, v___x_3286_, v_pre_3287_, v_post_3288_, v_usedLetOnly_3289_, v_skipConstInApp_3290_, v_skipInstances_3291_, v_a_3295_, v_b_3296_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3285_ = stack[0].m_obj;
lean_object* v___x_3286_ = stack[1].m_obj;
lean_object* v_pre_3287_ = stack[2].m_obj;
lean_object* v_post_3288_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3289_ = stack[4].m_num;
uint8_t v_skipConstInApp_3290_ = stack[5].m_num;
uint8_t v_skipInstances_3291_ = stack[6].m_num;
lean_object* v___x_3292_ = stack[7].m_obj;
lean_object* v_a_3295_ = stack[10].m_obj;
lean_object* v_b_3296_ = stack[11].m_obj;
lean_object* v___y_3298_ = stack[13].m_obj;
lean_object* v___y_3299_ = stack[14].m_obj;
lean_object* v___y_3300_ = stack[15].m_obj;
lean_object* v___y_3301_ = stack[16].m_obj;
lean_object* v___y_3302_ = stack[17].m_obj;
lean_object* v_res_3305_;
v_res_3305_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3285_, v___x_3286_, v_pre_3287_, v_post_3288_, v_usedLetOnly_3289_, v_skipConstInApp_3290_, v_skipInstances_3291_, v___x_3292_, lean_box(0), lean_box(0), v_a_3295_, v_b_3296_, lean_box(0), v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
stack->m_obj
 = v_res_3305_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3306_ = _args[0];
lean_object* v___x_3307_ = _args[1];
lean_object* v_pre_3308_ = _args[2];
lean_object* v_post_3309_ = _args[3];
lean_object* v_usedLetOnly_3310_ = _args[4];
lean_object* v_skipConstInApp_3311_ = _args[5];
lean_object* v_skipInstances_3312_ = _args[6];
lean_object* v___x_3313_ = _args[7];
lean_object* v_inst_3314_ = _args[8];
lean_object* v_R_3315_ = _args[9];
lean_object* v_a_3316_ = _args[10];
lean_object* v_b_3317_ = _args[11];
lean_object* v_c_3318_ = _args[12];
lean_object* v___y_3319_ = _args[13];
lean_object* v___y_3320_ = _args[14];
lean_object* v___y_3321_ = _args[15];
lean_object* v___y_3322_ = _args[16];
lean_object* v___y_3323_ = _args[17];
lean_object* v___y_3324_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3325_; uint8_t v_skipConstInApp_boxed_3326_; uint8_t v_skipInstances_boxed_3327_; lean_object* v_res_3328_; 
v_usedLetOnly_boxed_3325_ = lean_unbox(v_usedLetOnly_3310_);
v_skipConstInApp_boxed_3326_ = lean_unbox(v_skipConstInApp_3311_);
v_skipInstances_boxed_3327_ = lean_unbox(v_skipInstances_3312_);
v_res_3328_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3306_, v___x_3307_, v_pre_3308_, v_post_3309_, v_usedLetOnly_boxed_3325_, v_skipConstInApp_boxed_3326_, v_skipInstances_boxed_3327_, v___x_3313_, v_inst_3314_, v_R_3315_, v_a_3316_, v_b_3317_, v_c_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___x_3313_);
lean_dec_ref(v___x_3307_);
lean_dec(v_upperBound_3306_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3329_, lean_object* v_m_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3330_, v_a_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3333_, lean_object* v_m_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3333_, v_m_3334_, v_a_3335_);
lean_dec_ref(v_a_3335_);
lean_dec_ref(v_m_3334_);
return v_res_3336_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3337_, lean_object* v_name_3338_, uint8_t v_bi_3339_, lean_object* v_type_3340_, lean_object* v_k_3341_, uint8_t v_kind_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3338_, v_bi_3339_, v_type_3340_, v_k_3341_, v_kind_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
return v___x_3349_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3338_ = stack[1].m_obj;
uint8_t v_bi_3339_ = stack[2].m_num;
lean_object* v_type_3340_ = stack[3].m_obj;
lean_object* v_k_3341_ = stack[4].m_obj;
uint8_t v_kind_3342_ = stack[5].m_num;
lean_object* v___y_3343_ = stack[6].m_obj;
lean_object* v___y_3344_ = stack[7].m_obj;
lean_object* v___y_3345_ = stack[8].m_obj;
lean_object* v___y_3346_ = stack[9].m_obj;
lean_object* v___y_3347_ = stack[10].m_obj;
lean_object* v_res_3350_;
v_res_3350_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_box(0), v_name_3338_, v_bi_3339_, v_type_3340_, v_k_3341_, v_kind_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
stack->m_obj
 = v_res_3350_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3351_, lean_object* v_name_3352_, lean_object* v_bi_3353_, lean_object* v_type_3354_, lean_object* v_k_3355_, lean_object* v_kind_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
uint8_t v_bi_boxed_3363_; uint8_t v_kind_boxed_3364_; lean_object* v_res_3365_; 
v_bi_boxed_3363_ = lean_unbox(v_bi_3353_);
v_kind_boxed_3364_ = lean_unbox(v_kind_3356_);
v_res_3365_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3351_, v_name_3352_, v_bi_boxed_3363_, v_type_3354_, v_k_3355_, v_kind_boxed_3364_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
return v_res_3365_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3366_, lean_object* v_name_3367_, lean_object* v_type_3368_, lean_object* v_val_3369_, lean_object* v_k_3370_, uint8_t v_nondep_3371_, uint8_t v_kind_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3367_, v_type_3368_, v_val_3369_, v_k_3370_, v_nondep_3371_, v_kind_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3367_ = stack[1].m_obj;
lean_object* v_type_3368_ = stack[2].m_obj;
lean_object* v_val_3369_ = stack[3].m_obj;
lean_object* v_k_3370_ = stack[4].m_obj;
uint8_t v_nondep_3371_ = stack[5].m_num;
uint8_t v_kind_3372_ = stack[6].m_num;
lean_object* v___y_3373_ = stack[7].m_obj;
lean_object* v___y_3374_ = stack[8].m_obj;
lean_object* v___y_3375_ = stack[9].m_obj;
lean_object* v___y_3376_ = stack[10].m_obj;
lean_object* v___y_3377_ = stack[11].m_obj;
lean_object* v_res_3380_;
v_res_3380_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_box(0), v_name_3367_, v_type_3368_, v_val_3369_, v_k_3370_, v_nondep_3371_, v_kind_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
stack->m_obj
 = v_res_3380_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3381_, lean_object* v_name_3382_, lean_object* v_type_3383_, lean_object* v_val_3384_, lean_object* v_k_3385_, lean_object* v_nondep_3386_, lean_object* v_kind_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
uint8_t v_nondep_boxed_3394_; uint8_t v_kind_boxed_3395_; lean_object* v_res_3396_; 
v_nondep_boxed_3394_ = lean_unbox(v_nondep_3386_);
v_kind_boxed_3395_ = lean_unbox(v_kind_3387_);
v_res_3396_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3381_, v_name_3382_, v_type_3383_, v_val_3384_, v_k_3385_, v_nondep_boxed_3394_, v_kind_boxed_3395_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
return v_res_3396_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3397_, lean_object* v_ref_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3398_);
return v___x_3404_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3398_ = stack[1].m_obj;
lean_object* v___y_3399_ = stack[2].m_obj;
lean_object* v___y_3400_ = stack[3].m_obj;
lean_object* v___y_3401_ = stack[4].m_obj;
lean_object* v___y_3402_ = stack[5].m_obj;
lean_object* v_res_3405_;
v_res_3405_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_box(0), v_ref_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
stack->m_obj
 = v_res_3405_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3406_, lean_object* v_ref_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3406_, v_ref_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
return v_res_3413_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3414_, lean_object* v_x_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
return v___x_3422_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3415_ = stack[1].m_obj;
lean_object* v___y_3416_ = stack[2].m_obj;
lean_object* v___y_3417_ = stack[3].m_obj;
lean_object* v___y_3418_ = stack[4].m_obj;
lean_object* v___y_3419_ = stack[5].m_obj;
lean_object* v___y_3420_ = stack[6].m_obj;
lean_object* v_res_3423_;
v_res_3423_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_box(0), v_x_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
stack->m_obj
 = v_res_3423_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3424_, lean_object* v_x_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3424_, v_x_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3433_, lean_object* v_m_3434_, lean_object* v_a_3435_, lean_object* v_b_3436_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3434_, v_a_3435_, v_b_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3438_, lean_object* v_a_3439_, lean_object* v_x_3440_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3439_, v_x_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3442_, lean_object* v_a_3443_, lean_object* v_x_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3442_, v_a_3443_, v_x_3444_);
lean_dec(v_x_3444_);
lean_dec_ref(v_a_3443_);
return v_res_3445_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3446_, lean_object* v_a_3447_, lean_object* v_x_3448_){
_start:
{
uint8_t v___x_3449_; 
v___x_3449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3447_, v_x_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3447_ = stack[1].m_obj;
lean_object* v_x_3448_ = stack[2].m_obj;
uint8_t v_res_3450_;
v_res_3450_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_box(0), v_a_3447_, v_x_3448_);
stack->m_num = v_res_3450_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3451_, lean_object* v_a_3452_, lean_object* v_x_3453_){
_start:
{
uint8_t v_res_3454_; lean_object* v_r_3455_; 
v_res_3454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3451_, v_a_3452_, v_x_3453_);
lean_dec(v_x_3453_);
lean_dec_ref(v_a_3452_);
v_r_3455_ = lean_box(v_res_3454_);
return v_r_3455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3456_, lean_object* v_data_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3459_, lean_object* v_a_3460_, lean_object* v_b_3461_, lean_object* v_x_3462_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3460_, v_b_3461_, v_x_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3464_, lean_object* v_i_3465_, lean_object* v_source_3466_, lean_object* v_target_3467_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3465_, v_source_3466_, v_target_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3469_, lean_object* v_x_3470_, lean_object* v_x_3471_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3470_, v_x_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3486_, lean_object* v_x_3487_){
_start:
{
if (lean_obj_tag(v_x_3486_) == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3488_;
}
else
{
lean_object* v_val_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3500_; 
v_val_3489_ = lean_ctor_get(v_x_3486_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_x_3486_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3491_ = v_x_3486_;
v_isShared_3492_ = v_isSharedCheck_3500_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_val_3489_);
lean_dec(v_x_3486_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3500_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3496_; 
v___x_3493_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3494_ = l_Nat_reprFast(v_val_3489_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set_tag(v___x_3491_, 3);
lean_ctor_set(v___x_3491_, 0, v___x_3494_);
v___x_3496_ = v___x_3491_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3494_);
v___x_3496_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3493_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = l_Repr_addAppParen(v___x_3497_, v_x_3487_);
return v___x_3498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3501_, lean_object* v_x_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3501_, v_x_3502_);
lean_dec(v_x_3502_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3504_, lean_object* v_x_3505_, lean_object* v_x_3506_){
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
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = lean_unsigned_to_nat(0u);
v___x_3515_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3507_, v___x_3514_);
v___x_3516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3513_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v_x_3505_ = v___x_3516_;
v_x_3506_ = v_tail_3508_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3520_, lean_object* v_x_3521_, lean_object* v_x_3522_){
_start:
{
if (lean_obj_tag(v_x_3522_) == 0)
{
lean_dec(v_x_3520_);
return v_x_3521_;
}
else
{
lean_object* v_head_3523_; lean_object* v_tail_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3535_; 
v_head_3523_ = lean_ctor_get(v_x_3522_, 0);
v_tail_3524_ = lean_ctor_get(v_x_3522_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_x_3522_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3526_ = v_x_3522_;
v_isShared_3527_ = v_isSharedCheck_3535_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_tail_3524_);
lean_inc(v_head_3523_);
lean_dec(v_x_3522_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3535_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
lean_inc(v_x_3520_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 5);
lean_ctor_set(v___x_3526_, 1, v_x_3520_);
lean_ctor_set(v___x_3526_, 0, v_x_3521_);
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_x_3521_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_x_3520_);
v___x_3529_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3530_ = lean_unsigned_to_nat(0u);
v___x_3531_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3523_, v___x_3530_);
v___x_3532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3529_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3520_, v___x_3532_, v_tail_3524_);
return v___x_3533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = lean_unsigned_to_nat(0u);
v___x_3538_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3536_, v___x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3539_, lean_object* v_x_3540_){
_start:
{
if (lean_obj_tag(v_x_3539_) == 0)
{
lean_object* v___x_3541_; 
lean_dec(v_x_3540_);
v___x_3541_ = lean_box(0);
return v___x_3541_;
}
else
{
lean_object* v_tail_3542_; 
v_tail_3542_ = lean_ctor_get(v_x_3539_, 1);
if (lean_obj_tag(v_tail_3542_) == 0)
{
lean_object* v_head_3543_; lean_object* v___x_3544_; 
lean_dec(v_x_3540_);
v_head_3543_ = lean_ctor_get(v_x_3539_, 0);
lean_inc(v_head_3543_);
lean_dec_ref_known(v_x_3539_, 2);
v___x_3544_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3543_);
return v___x_3544_;
}
else
{
lean_object* v_head_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_inc(v_tail_3542_);
v_head_3545_ = lean_ctor_get(v_x_3539_, 0);
lean_inc(v_head_3545_);
lean_dec_ref_known(v_x_3539_, 2);
v___x_3546_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3545_);
v___x_3547_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3540_, v___x_3546_, v_tail_3542_);
return v___x_3547_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3556_ = lean_string_length(v___x_3555_);
return v___x_3556_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3558_ = lean_nat_to_int(v___x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3564_){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3565_ = lean_array_get_size(v_xs_3564_);
v___x_3566_ = lean_unsigned_to_nat(0u);
v___x_3567_ = lean_nat_dec_eq(v___x_3565_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3568_ = lean_array_to_list(v_xs_3564_);
v___x_3569_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3570_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3568_, v___x_3569_);
v___x_3571_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3572_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
lean_ctor_set(v___x_3573_, 1, v___x_3570_);
v___x_3574_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3573_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3571_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = l_Std_Format_fill(v___x_3576_);
return v___x_3577_;
}
else
{
lean_object* v___x_3578_; 
lean_dec_ref(v_xs_3564_);
v___x_3578_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3578_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3579_, lean_object* v_x_3580_, lean_object* v_x_3581_){
_start:
{
if (lean_obj_tag(v_x_3581_) == 0)
{
lean_dec(v_x_3579_);
return v_x_3580_;
}
else
{
lean_object* v_head_3582_; lean_object* v_tail_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3593_; 
v_head_3582_ = lean_ctor_get(v_x_3581_, 0);
v_tail_3583_ = lean_ctor_get(v_x_3581_, 1);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_x_3581_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3585_ = v_x_3581_;
v_isShared_3586_ = v_isSharedCheck_3593_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_tail_3583_);
lean_inc(v_head_3582_);
lean_dec(v_x_3581_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3593_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
lean_inc(v_x_3579_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 5);
lean_ctor_set(v___x_3585_, 1, v_x_3579_);
lean_ctor_set(v___x_3585_, 0, v_x_3580_);
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_x_3580_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_x_3579_);
v___x_3588_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3582_);
v___x_3590_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3588_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
v_x_3580_ = v___x_3590_;
v_x_3581_ = v_tail_3583_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3594_, lean_object* v_x_3595_){
_start:
{
if (lean_obj_tag(v_x_3594_) == 0)
{
lean_object* v___x_3596_; 
lean_dec(v_x_3595_);
v___x_3596_ = lean_box(0);
return v___x_3596_;
}
else
{
lean_object* v_tail_3597_; 
v_tail_3597_ = lean_ctor_get(v_x_3594_, 1);
if (lean_obj_tag(v_tail_3597_) == 0)
{
lean_object* v_head_3598_; lean_object* v___x_3599_; 
lean_dec(v_x_3595_);
v_head_3598_ = lean_ctor_get(v_x_3594_, 0);
lean_inc(v_head_3598_);
lean_dec_ref_known(v_x_3594_, 2);
v___x_3599_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3598_);
return v___x_3599_;
}
else
{
lean_object* v_head_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
lean_inc(v_tail_3597_);
v_head_3600_ = lean_ctor_get(v_x_3594_, 0);
lean_inc(v_head_3600_);
lean_dec_ref_known(v_x_3594_, 2);
v___x_3601_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3600_);
v___x_3602_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3595_, v___x_3601_, v_tail_3597_);
return v___x_3602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3603_){
_start:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3604_ = lean_array_get_size(v_xs_3603_);
v___x_3605_ = lean_unsigned_to_nat(0u);
v___x_3606_ = lean_nat_dec_eq(v___x_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3607_ = lean_array_to_list(v_xs_3603_);
v___x_3608_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3609_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3607_, v___x_3608_);
v___x_3610_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3611_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v___x_3609_);
v___x_3613_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3610_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Std_Format_fill(v___x_3615_);
return v___x_3616_;
}
else
{
lean_object* v___x_3617_; 
lean_dec_ref(v_xs_3603_);
v___x_3617_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3617_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_){
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
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3628_ = l_Nat_reprFast(v_head_3621_);
v___x_3629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
v___x_3630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3627_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v_x_3619_ = v___x_3630_;
v_x_3620_ = v_tail_3622_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3634_, lean_object* v_x_3635_, lean_object* v_x_3636_){
_start:
{
if (lean_obj_tag(v_x_3636_) == 0)
{
lean_dec(v_x_3634_);
return v_x_3635_;
}
else
{
lean_object* v_head_3637_; lean_object* v_tail_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3649_; 
v_head_3637_ = lean_ctor_get(v_x_3636_, 0);
v_tail_3638_ = lean_ctor_get(v_x_3636_, 1);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_x_3636_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3640_ = v_x_3636_;
v_isShared_3641_ = v_isSharedCheck_3649_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_tail_3638_);
lean_inc(v_head_3637_);
lean_dec(v_x_3636_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3649_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
lean_inc(v_x_3634_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set_tag(v___x_3640_, 5);
lean_ctor_set(v___x_3640_, 1, v_x_3634_);
lean_ctor_set(v___x_3640_, 0, v_x_3635_);
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_x_3635_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_x_3634_);
v___x_3643_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3644_ = l_Nat_reprFast(v_head_3637_);
v___x_3645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
v___x_3646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3643_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3634_, v___x_3646_, v_tail_3638_);
return v___x_3647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = l_Nat_reprFast(v___y_3650_);
v___x_3652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3653_, lean_object* v_x_3654_){
_start:
{
if (lean_obj_tag(v_x_3653_) == 0)
{
lean_object* v___x_3655_; 
lean_dec(v_x_3654_);
v___x_3655_ = lean_box(0);
return v___x_3655_;
}
else
{
lean_object* v_tail_3656_; 
v_tail_3656_ = lean_ctor_get(v_x_3653_, 1);
if (lean_obj_tag(v_tail_3656_) == 0)
{
lean_object* v_head_3657_; lean_object* v___x_3658_; 
lean_dec(v_x_3654_);
v_head_3657_ = lean_ctor_get(v_x_3653_, 0);
lean_inc(v_head_3657_);
lean_dec_ref_known(v_x_3653_, 2);
v___x_3658_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3657_);
return v___x_3658_;
}
else
{
lean_object* v_head_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_inc(v_tail_3656_);
v_head_3659_ = lean_ctor_get(v_x_3653_, 0);
lean_inc(v_head_3659_);
lean_dec_ref_known(v_x_3653_, 2);
v___x_3660_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3659_);
v___x_3661_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3654_, v___x_3660_, v_tail_3656_);
return v___x_3661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3662_){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3663_ = lean_array_get_size(v_xs_3662_);
v___x_3664_ = lean_unsigned_to_nat(0u);
v___x_3665_ = lean_nat_dec_eq(v___x_3663_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3666_ = lean_array_to_list(v_xs_3662_);
v___x_3667_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3668_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3666_, v___x_3667_);
v___x_3669_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3670_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
lean_ctor_set(v___x_3671_, 1, v___x_3668_);
v___x_3672_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3669_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
v___x_3675_ = l_Std_Format_fill(v___x_3674_);
return v___x_3675_;
}
else
{
lean_object* v___x_3676_; 
lean_dec_ref(v_xs_3662_);
v___x_3676_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3676_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3677_, lean_object* v_x_3678_, lean_object* v_x_3679_){
_start:
{
if (lean_obj_tag(v_x_3679_) == 0)
{
lean_dec(v_x_3677_);
return v_x_3678_;
}
else
{
lean_object* v_head_3680_; lean_object* v_tail_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3691_; 
v_head_3680_ = lean_ctor_get(v_x_3679_, 0);
v_tail_3681_ = lean_ctor_get(v_x_3679_, 1);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_x_3679_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3683_ = v_x_3679_;
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_tail_3681_);
lean_inc(v_head_3680_);
lean_dec(v_x_3679_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3691_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
lean_inc(v_x_3677_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set_tag(v___x_3683_, 5);
lean_ctor_set(v___x_3683_, 1, v_x_3677_);
lean_ctor_set(v___x_3683_, 0, v_x_3678_);
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_x_3678_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_x_3677_);
v___x_3686_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3680_);
v___x_3688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v_x_3678_ = v___x_3688_;
v_x_3679_ = v_tail_3681_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3692_, lean_object* v_x_3693_){
_start:
{
if (lean_obj_tag(v_x_3692_) == 0)
{
lean_object* v___x_3694_; 
lean_dec(v_x_3693_);
v___x_3694_ = lean_box(0);
return v___x_3694_;
}
else
{
lean_object* v_tail_3695_; 
v_tail_3695_ = lean_ctor_get(v_x_3692_, 1);
if (lean_obj_tag(v_tail_3695_) == 0)
{
lean_object* v_head_3696_; lean_object* v___x_3697_; 
lean_dec(v_x_3693_);
v_head_3696_ = lean_ctor_get(v_x_3692_, 0);
lean_inc(v_head_3696_);
lean_dec_ref_known(v_x_3692_, 2);
v___x_3697_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3696_);
return v___x_3697_;
}
else
{
lean_object* v_head_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
lean_inc(v_tail_3695_);
v_head_3698_ = lean_ctor_get(v_x_3692_, 0);
lean_inc(v_head_3698_);
lean_dec_ref_known(v_x_3692_, 2);
v___x_3699_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3698_);
v___x_3700_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3693_, v___x_3699_, v_tail_3695_);
return v___x_3700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3701_){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v___x_3702_ = lean_array_get_size(v_xs_3701_);
v___x_3703_ = lean_unsigned_to_nat(0u);
v___x_3704_ = lean_nat_dec_eq(v___x_3702_, v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3705_ = lean_array_to_list(v_xs_3701_);
v___x_3706_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3707_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3705_, v___x_3706_);
v___x_3708_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3709_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v___x_3707_);
v___x_3711_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3708_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = l_Std_Format_fill(v___x_3713_);
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; 
lean_dec_ref(v_xs_3701_);
v___x_3715_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3715_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3716_, lean_object* v_x_3717_, lean_object* v_x_3718_){
_start:
{
if (lean_obj_tag(v_x_3718_) == 0)
{
lean_dec(v_x_3716_);
return v_x_3717_;
}
else
{
lean_object* v_head_3719_; lean_object* v_tail_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3730_; 
v_head_3719_ = lean_ctor_get(v_x_3718_, 0);
v_tail_3720_ = lean_ctor_get(v_x_3718_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_x_3718_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3722_ = v_x_3718_;
v_isShared_3723_ = v_isSharedCheck_3730_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_tail_3720_);
lean_inc(v_head_3719_);
lean_dec(v_x_3718_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3730_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
lean_inc(v_x_3716_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set_tag(v___x_3722_, 5);
lean_ctor_set(v___x_3722_, 1, v_x_3716_);
lean_ctor_set(v___x_3722_, 0, v_x_3717_);
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_x_3717_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_x_3716_);
v___x_3725_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3719_);
v___x_3727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v_x_3717_ = v___x_3727_;
v_x_3718_ = v_tail_3720_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3731_, lean_object* v_x_3732_){
_start:
{
if (lean_obj_tag(v_x_3731_) == 0)
{
lean_object* v___x_3733_; 
lean_dec(v_x_3732_);
v___x_3733_ = lean_box(0);
return v___x_3733_;
}
else
{
lean_object* v_tail_3734_; 
v_tail_3734_ = lean_ctor_get(v_x_3731_, 1);
if (lean_obj_tag(v_tail_3734_) == 0)
{
lean_object* v_head_3735_; lean_object* v___x_3736_; 
lean_dec(v_x_3732_);
v_head_3735_ = lean_ctor_get(v_x_3731_, 0);
lean_inc(v_head_3735_);
lean_dec_ref_known(v_x_3731_, 2);
v___x_3736_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3735_);
return v___x_3736_;
}
else
{
lean_object* v_head_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_inc(v_tail_3734_);
v_head_3737_ = lean_ctor_get(v_x_3731_, 0);
lean_inc(v_head_3737_);
lean_dec_ref_known(v_x_3731_, 2);
v___x_3738_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3737_);
v___x_3739_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3732_, v___x_3738_, v_tail_3734_);
return v___x_3739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3740_){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v___x_3741_ = lean_array_get_size(v_xs_3740_);
v___x_3742_ = lean_unsigned_to_nat(0u);
v___x_3743_ = lean_nat_dec_eq(v___x_3741_, v___x_3742_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3744_ = lean_array_to_list(v_xs_3740_);
v___x_3745_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3746_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3744_, v___x_3745_);
v___x_3747_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3748_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v___x_3746_);
v___x_3750_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3747_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = l_Std_Format_fill(v___x_3752_);
return v___x_3753_;
}
else
{
lean_object* v___x_3754_; 
lean_dec_ref(v_xs_3740_);
v___x_3754_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3754_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3768_ = lean_unsigned_to_nat(12u);
v___x_3769_ = lean_nat_to_int(v___x_3768_);
return v___x_3769_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3773_ = lean_unsigned_to_nat(9u);
v___x_3774_ = lean_nat_to_int(v___x_3773_);
return v___x_3774_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_unsigned_to_nat(11u);
v___x_3779_ = lean_nat_to_int(v___x_3778_);
return v___x_3779_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3782_ = lean_string_length(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3784_ = lean_nat_to_int(v___x_3783_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3789_){
_start:
{
lean_object* v_numFixed_3790_; lean_object* v_perms_3791_; lean_object* v_revDeps_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_numFixed_3790_ = lean_ctor_get(v_x_3789_, 0);
lean_inc(v_numFixed_3790_);
v_perms_3791_ = lean_ctor_get(v_x_3789_, 1);
lean_inc_ref(v_perms_3791_);
v_revDeps_3792_ = lean_ctor_get(v_x_3789_, 2);
lean_inc_ref(v_revDeps_3792_);
lean_dec_ref(v_x_3789_);
v___x_3793_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3794_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3795_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3796_ = l_Nat_reprFast(v_numFixed_3790_);
v___x_3797_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3795_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = 0;
v___x_3800_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set_uint8(v___x_3800_, sizeof(void*)*1, v___x_3799_);
v___x_3801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3794_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3803_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3801_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = lean_box(1);
v___x_3805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
lean_ctor_set(v___x_3808_, 1, v___x_3793_);
v___x_3809_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3810_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3791_);
v___x_3811_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
lean_ctor_set_uint8(v___x_3812_, sizeof(void*)*1, v___x_3799_);
v___x_3813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3808_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v___x_3802_);
v___x_3815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
lean_ctor_set(v___x_3815_, 1, v___x_3804_);
v___x_3816_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
lean_ctor_set(v___x_3818_, 1, v___x_3793_);
v___x_3819_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3820_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3792_);
v___x_3821_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3819_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
lean_ctor_set_uint8(v___x_3822_, sizeof(void*)*1, v___x_3799_);
v___x_3823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3818_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3825_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
lean_ctor_set(v___x_3826_, 1, v___x_3823_);
v___x_3827_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3824_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*1, v___x_3799_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3831_, lean_object* v_prec_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3831_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3834_, lean_object* v_prec_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3834_, v_prec_3835_);
lean_dec(v_prec_3835_);
return v_res_3836_;
}
}
lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___f_3845_; lean_object* v___x_5728__overap_3846_; lean_object* v___x_3847_; 
v___f_3845_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5728__overap_3846_ = lean_panic_fn_borrowed(v___f_3845_, v_msg_3839_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
v___x_3847_ = lean_apply_5(v___x_5728__overap_3846_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, lean_box(0));
return v___x_3847_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3839_ = stack[0].m_obj;
lean_object* v___y_3840_ = stack[1].m_obj;
lean_object* v___y_3841_ = stack[2].m_obj;
lean_object* v___y_3842_ = stack[3].m_obj;
lean_object* v___y_3843_ = stack[4].m_obj;
lean_object* v_res_3848_;
v_res_3848_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
stack->m_obj
 = v_res_3848_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
return v_res_3855_;
}
}
lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___f_3862_; lean_object* v___x_5738__overap_3863_; lean_object* v___x_3864_; 
v___f_3862_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5738__overap_3863_ = lean_panic_fn_borrowed(v___f_3862_, v_msg_3856_);
lean_inc(v___y_3860_);
lean_inc_ref(v___y_3859_);
lean_inc(v___y_3858_);
lean_inc_ref(v___y_3857_);
v___x_3864_ = lean_apply_5(v___x_5738__overap_3863_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, lean_box(0));
return v___x_3864_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3856_ = stack[0].m_obj;
lean_object* v___y_3857_ = stack[1].m_obj;
lean_object* v___y_3858_ = stack[2].m_obj;
lean_object* v___y_3859_ = stack[3].m_obj;
lean_object* v___y_3860_ = stack[4].m_obj;
lean_object* v_res_3865_;
v_res_3865_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
stack->m_obj
 = v_res_3865_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
return v_res_3872_;
}
}
lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___f_3879_; lean_object* v___x_5748__overap_3880_; lean_object* v___x_3881_; 
v___f_3879_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5748__overap_3880_ = lean_panic_fn_borrowed(v___f_3879_, v_msg_3873_);
lean_inc(v___y_3877_);
lean_inc_ref(v___y_3876_);
lean_inc(v___y_3875_);
lean_inc_ref(v___y_3874_);
v___x_3881_ = lean_apply_5(v___x_5748__overap_3880_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, lean_box(0));
return v___x_3881_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3873_ = stack[0].m_obj;
lean_object* v___y_3874_ = stack[1].m_obj;
lean_object* v___y_3875_ = stack[2].m_obj;
lean_object* v___y_3876_ = stack[3].m_obj;
lean_object* v___y_3877_ = stack[4].m_obj;
lean_object* v_res_3882_;
v_res_3882_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
stack->m_obj
 = v_res_3882_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
return v_res_3889_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3893_ = lean_unsigned_to_nat(12u);
v___x_3894_ = lean_unsigned_to_nat(294u);
v___x_3895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3896_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3897_ = l_mkPanicMessageWithDecl(v___x_3896_, v___x_3895_, v___x_3894_, v___x_3893_, v___x_3892_);
return v___x_3897_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3900_ = lean_unsigned_to_nat(12u);
v___x_3901_ = lean_unsigned_to_nat(297u);
v___x_3902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3904_ = l_mkPanicMessageWithDecl(v___x_3903_, v___x_3902_, v___x_3901_, v___x_3900_, v___x_3899_);
return v___x_3904_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3905_, lean_object* v_as_3906_, size_t v_sz_3907_, size_t v_i_3908_, lean_object* v_b_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_a_3916_; uint8_t v___x_3920_; 
v___x_3920_ = lean_usize_dec_lt(v_i_3908_, v_sz_3907_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; 
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v_b_3909_);
return v___x_3921_;
}
else
{
lean_object* v_a_3922_; 
v_a_3922_ = lean_array_uget_borrowed(v_as_3906_, v_i_3908_);
if (lean_obj_tag(v_a_3922_) == 1)
{
lean_object* v_val_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_val_3923_ = lean_ctor_get(v_a_3922_, 0);
v___x_3924_ = lean_box(0);
v___x_3925_ = lean_unsigned_to_nat(0u);
v___x_3926_ = lean_array_get_borrowed(v___x_3924_, v_val_3923_, v___x_3925_);
if (lean_obj_tag(v___x_3926_) == 1)
{
lean_object* v_val_3927_; lean_object* v___x_3928_; 
v_val_3927_ = lean_ctor_get(v___x_3926_, 0);
v___x_3928_ = lean_array_get_borrowed(v___x_3924_, v___x_3905_, v_val_3927_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_dec_ref(v_b_3909_);
v___x_3929_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3930_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3929_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3940_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3933_ = v___x_3930_;
v_isShared_3934_ = v_isSharedCheck_3940_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3940_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
if (lean_obj_tag(v_a_3931_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; 
v_a_3935_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v_a_3931_, 1);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v_a_3935_);
v___x_3937_ = v___x_3933_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
else
{
lean_object* v_a_3939_; 
lean_del_object(v___x_3933_);
v_a_3939_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_a_3939_);
lean_dec_ref_known(v_a_3931_, 1);
v_a_3916_ = v_a_3939_;
goto v___jp_3915_;
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
v_a_3941_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3930_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3930_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
lean_object* v___x_3949_; 
lean_inc_ref(v___x_3928_);
v___x_3949_ = lean_array_push(v_b_3909_, v___x_3928_);
v_a_3916_ = v___x_3949_;
goto v___jp_3915_;
}
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3950_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3951_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3950_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_dec_ref_known(v___x_3951_, 1);
v_a_3916_ = v_b_3909_;
goto v___jp_3915_;
}
else
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
lean_dec_ref(v_b_3909_);
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_box(0);
v___x_3961_ = lean_array_push(v_b_3909_, v___x_3960_);
v_a_3916_ = v___x_3961_;
goto v___jp_3915_;
}
}
v___jp_3915_:
{
size_t v___x_3917_; size_t v___x_3918_; 
v___x_3917_ = ((size_t)1ULL);
v___x_3918_ = lean_usize_add(v_i_3908_, v___x_3917_);
v_i_3908_ = v___x_3918_;
v_b_3909_ = v_a_3916_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3905_ = stack[0].m_obj;
lean_object* v_as_3906_ = stack[1].m_obj;
size_t v_sz_3907_ = stack[2].m_num;
size_t v_i_3908_ = stack[3].m_num;
lean_object* v_b_3909_ = stack[4].m_obj;
lean_object* v___y_3910_ = stack[5].m_obj;
lean_object* v___y_3911_ = stack[6].m_obj;
lean_object* v___y_3912_ = stack[7].m_obj;
lean_object* v___y_3913_ = stack[8].m_obj;
lean_object* v_res_3962_;
v_res_3962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3905_, v_as_3906_, v_sz_3907_, v_i_3908_, v_b_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
stack->m_obj
 = v_res_3962_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3963_, lean_object* v_as_3964_, lean_object* v_sz_3965_, lean_object* v_i_3966_, lean_object* v_b_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
size_t v_sz_boxed_3973_; size_t v_i_boxed_3974_; lean_object* v_res_3975_; 
v_sz_boxed_3973_ = lean_unbox_usize(v_sz_3965_);
lean_dec(v_sz_3965_);
v_i_boxed_3974_ = lean_unbox_usize(v_i_3966_);
lean_dec(v_i_3966_);
v_res_3975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3963_, v_as_3964_, v_sz_boxed_3973_, v_i_boxed_3974_, v_b_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec_ref(v_as_3964_);
lean_dec_ref(v___x_3963_);
return v_res_3975_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3978_, lean_object* v___x_3979_, lean_object* v___x_3980_, lean_object* v_a_3981_, lean_object* v_b_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_nat_dec_lt(v_a_3981_, v_upperBound_3978_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
lean_dec(v_a_3981_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v_b_3982_);
return v___x_3989_;
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; size_t v_sz_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v___x_3990_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3991_ = lean_array_fget_borrowed(v___x_3979_, v_a_3981_);
v_sz_3992_ = lean_array_size(v___x_3991_);
v___x_3993_ = ((size_t)0ULL);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3980_, v___x_3991_, v_sz_3992_, v___x_3993_, v___x_3990_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref_known(v___x_3994_, 1);
v___x_3996_ = lean_array_push(v_b_3982_, v_a_3995_);
v___x_3997_ = lean_unsigned_to_nat(1u);
v___x_3998_ = lean_nat_add(v_a_3981_, v___x_3997_);
lean_dec(v_a_3981_);
v_a_3981_ = v___x_3998_;
v_b_3982_ = v___x_3996_;
goto _start;
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec_ref(v_b_3982_);
lean_dec(v_a_3981_);
v_a_4000_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3994_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3994_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3978_ = stack[0].m_obj;
lean_object* v___x_3979_ = stack[1].m_obj;
lean_object* v___x_3980_ = stack[2].m_obj;
lean_object* v_a_3981_ = stack[3].m_obj;
lean_object* v_b_3982_ = stack[4].m_obj;
lean_object* v___y_3983_ = stack[5].m_obj;
lean_object* v___y_3984_ = stack[6].m_obj;
lean_object* v___y_3985_ = stack[7].m_obj;
lean_object* v___y_3986_ = stack[8].m_obj;
lean_object* v_res_4008_;
v_res_4008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3978_, v___x_3979_, v___x_3980_, v_a_3981_, v_b_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
stack->m_obj
 = v_res_4008_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_4009_, lean_object* v___x_4010_, lean_object* v___x_4011_, lean_object* v_a_4012_, lean_object* v_b_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4009_, v___x_4010_, v___x_4011_, v_a_4012_, v_b_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec_ref(v___x_4011_);
lean_dec_ref(v___x_4010_);
lean_dec(v_upperBound_4009_);
return v_res_4019_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4021_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_4022_ = lean_unsigned_to_nat(8u);
v___x_4023_ = lean_unsigned_to_nat(281u);
v___x_4024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4025_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4026_ = l_mkPanicMessageWithDecl(v___x_4025_, v___x_4024_, v___x_4023_, v___x_4022_, v___x_4021_);
return v___x_4026_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_4027_, lean_object* v_a_4028_, lean_object* v_b_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v_a_4036_; uint8_t v___x_4040_; 
v___x_4040_ = lean_nat_dec_lt(v_a_4028_, v_upperBound_4027_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; 
lean_dec(v_a_4028_);
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v_b_4029_);
return v___x_4041_;
}
else
{
lean_object* v_snd_4042_; lean_object* v_snd_4043_; lean_object* v_snd_4044_; lean_object* v_fst_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4169_; 
v_snd_4042_ = lean_ctor_get(v_b_4029_, 1);
lean_inc(v_snd_4042_);
v_snd_4043_ = lean_ctor_get(v_snd_4042_, 1);
lean_inc(v_snd_4043_);
v_snd_4044_ = lean_ctor_get(v_snd_4043_, 1);
lean_inc(v_snd_4044_);
v_fst_4045_ = lean_ctor_get(v_b_4029_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v_b_4029_);
if (v_isSharedCheck_4169_ == 0)
{
lean_object* v_unused_4170_; 
v_unused_4170_ = lean_ctor_get(v_b_4029_, 1);
lean_dec(v_unused_4170_);
v___x_4047_ = v_b_4029_;
v_isShared_4048_ = v_isSharedCheck_4169_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_fst_4045_);
lean_dec(v_b_4029_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4169_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v_fst_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4167_; 
v_fst_4049_ = lean_ctor_get(v_snd_4042_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v_snd_4042_);
if (v_isSharedCheck_4167_ == 0)
{
lean_object* v_unused_4168_; 
v_unused_4168_ = lean_ctor_get(v_snd_4042_, 1);
lean_dec(v_unused_4168_);
v___x_4051_ = v_snd_4042_;
v_isShared_4052_ = v_isSharedCheck_4167_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_fst_4049_);
lean_dec(v_snd_4042_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4167_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v_fst_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4165_; 
v_fst_4053_ = lean_ctor_get(v_snd_4043_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v_snd_4043_);
if (v_isSharedCheck_4165_ == 0)
{
lean_object* v_unused_4166_; 
v_unused_4166_ = lean_ctor_get(v_snd_4043_, 1);
lean_dec(v_unused_4166_);
v___x_4055_ = v_snd_4043_;
v_isShared_4056_ = v_isSharedCheck_4165_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_fst_4053_);
lean_dec(v_snd_4043_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4165_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v_array_4057_; lean_object* v_start_4058_; lean_object* v_stop_4059_; uint8_t v___x_4060_; 
v_array_4057_ = lean_ctor_get(v_snd_4044_, 0);
v_start_4058_ = lean_ctor_get(v_snd_4044_, 1);
v_stop_4059_ = lean_ctor_get(v_snd_4044_, 2);
v___x_4060_ = lean_nat_dec_lt(v_start_4058_, v_stop_4059_);
if (v___x_4060_ == 0)
{
lean_object* v___x_4062_; 
lean_dec(v_a_4028_);
if (v_isShared_4056_ == 0)
{
v___x_4062_ = v___x_4055_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_fst_4053_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_snd_4044_);
v___x_4062_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4064_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 1, v___x_4062_);
v___x_4064_ = v___x_4051_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_fst_4049_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4066_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 1, v___x_4064_);
v___x_4066_ = v___x_4047_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_fst_4045_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4067_; 
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
return v___x_4067_;
}
}
}
}
else
{
lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4161_; 
lean_inc(v_stop_4059_);
lean_inc(v_start_4058_);
lean_inc_ref(v_array_4057_);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_snd_4044_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; lean_object* v_unused_4163_; lean_object* v_unused_4164_; 
v_unused_4162_ = lean_ctor_get(v_snd_4044_, 2);
lean_dec(v_unused_4162_);
v_unused_4163_ = lean_ctor_get(v_snd_4044_, 1);
lean_dec(v_unused_4163_);
v_unused_4164_ = lean_ctor_get(v_snd_4044_, 0);
lean_dec(v_unused_4164_);
v___x_4072_ = v_snd_4044_;
v_isShared_4073_ = v_isSharedCheck_4161_;
goto v_resetjp_4071_;
}
else
{
lean_dec(v_snd_4044_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4161_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v_array_4074_; lean_object* v_start_4075_; lean_object* v_stop_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4081_; 
v_array_4074_ = lean_ctor_get(v_fst_4053_, 0);
v_start_4075_ = lean_ctor_get(v_fst_4053_, 1);
v_stop_4076_ = lean_ctor_get(v_fst_4053_, 2);
v___x_4077_ = lean_array_fget(v_array_4057_, v_start_4058_);
v___x_4078_ = lean_unsigned_to_nat(1u);
v___x_4079_ = lean_nat_add(v_start_4058_, v___x_4078_);
lean_dec(v_start_4058_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 1, v___x_4079_);
v___x_4081_ = v___x_4072_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_array_4057_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___x_4079_);
lean_ctor_set(v_reuseFailAlloc_4160_, 2, v_stop_4059_);
v___x_4081_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
uint8_t v___x_4082_; 
v___x_4082_ = lean_nat_dec_lt(v_start_4075_, v_stop_4076_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4084_; 
lean_dec(v___x_4077_);
lean_dec(v_a_4028_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 1, v___x_4081_);
v___x_4084_ = v___x_4055_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_fst_4053_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v___x_4081_);
v___x_4084_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4086_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 1, v___x_4084_);
v___x_4086_ = v___x_4051_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_fst_4049_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4084_);
v___x_4086_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
lean_object* v___x_4088_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 1, v___x_4086_);
v___x_4088_ = v___x_4047_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_fst_4045_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4089_; 
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
return v___x_4089_;
}
}
}
}
else
{
lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4156_; 
lean_inc(v_stop_4076_);
lean_inc(v_start_4075_);
lean_inc_ref(v_array_4074_);
v_isSharedCheck_4156_ = !lean_is_exclusive(v_fst_4053_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; lean_object* v_unused_4158_; lean_object* v_unused_4159_; 
v_unused_4157_ = lean_ctor_get(v_fst_4053_, 2);
lean_dec(v_unused_4157_);
v_unused_4158_ = lean_ctor_get(v_fst_4053_, 1);
lean_dec(v_unused_4158_);
v_unused_4159_ = lean_ctor_get(v_fst_4053_, 0);
lean_dec(v_unused_4159_);
v___x_4094_ = v_fst_4053_;
v_isShared_4095_ = v_isSharedCheck_4156_;
goto v_resetjp_4093_;
}
else
{
lean_dec(v_fst_4053_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4156_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4096_ = lean_nat_add(v_start_4075_, v___x_4078_);
lean_dec(v_start_4075_);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v___x_4096_);
v___x_4098_ = v___x_4094_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_array_4074_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v___x_4096_);
lean_ctor_set(v_reuseFailAlloc_4155_, 2, v_stop_4076_);
v___x_4098_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
if (lean_obj_tag(v___x_4077_) == 1)
{
lean_object* v_val_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4143_; 
v_val_4099_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4101_ = v___x_4077_;
v_isShared_4102_ = v_isSharedCheck_4143_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_val_4099_);
lean_dec(v___x_4077_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4143_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
v___x_4103_ = lean_box(0);
v___x_4104_ = lean_unsigned_to_nat(0u);
v___x_4105_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4106_ = lean_array_get(v___x_4103_, v_val_4099_, v___x_4104_);
lean_dec(v_val_4099_);
lean_inc(v_a_4028_);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v_a_4028_);
v___x_4108_ = v___x_4101_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4028_);
v___x_4108_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
uint8_t v___x_4109_; 
v___x_4109_ = l_Option_instDecidableEq___redArg(v___x_4105_, v___x_4106_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_dec_ref(v___x_4098_);
lean_dec_ref(v___x_4081_);
lean_del_object(v___x_4055_);
lean_del_object(v___x_4051_);
lean_dec(v_fst_4049_);
lean_del_object(v___x_4047_);
lean_dec(v_fst_4045_);
v___x_4110_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4111_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4110_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4121_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4114_ = v___x_4111_;
v_isShared_4115_ = v_isSharedCheck_4121_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4111_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4121_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
if (lean_obj_tag(v_a_4112_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4118_; 
lean_dec(v_a_4028_);
v_a_4116_ = lean_ctor_get(v_a_4112_, 0);
lean_inc(v_a_4116_);
lean_dec_ref_known(v_a_4112_, 1);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 0, v_a_4116_);
v___x_4118_ = v___x_4114_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4116_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
else
{
lean_object* v_a_4120_; 
lean_del_object(v___x_4114_);
v_a_4120_ = lean_ctor_get(v_a_4112_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v_a_4112_, 1);
v_a_4036_ = v_a_4120_;
goto v___jp_4035_;
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec(v_a_4028_);
v_a_4122_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4111_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4111_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
else
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4134_; 
lean_inc(v_fst_4049_);
v___x_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4130_, 0, v_fst_4049_);
v___x_4131_ = lean_array_push(v_fst_4045_, v___x_4130_);
v___x_4132_ = lean_nat_add(v_fst_4049_, v___x_4078_);
lean_dec(v_fst_4049_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 1, v___x_4081_);
lean_ctor_set(v___x_4055_, 0, v___x_4098_);
v___x_4134_ = v___x_4055_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4098_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4081_);
v___x_4134_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
lean_object* v___x_4136_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 1, v___x_4134_);
lean_ctor_set(v___x_4051_, 0, v___x_4132_);
v___x_4136_ = v___x_4051_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4132_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4138_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 1, v___x_4136_);
lean_ctor_set(v___x_4047_, 0, v___x_4131_);
v___x_4138_ = v___x_4047_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4131_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v___x_4136_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
v_a_4036_ = v___x_4138_;
goto v___jp_4035_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
lean_dec(v___x_4077_);
v___x_4144_ = lean_box(0);
v___x_4145_ = lean_array_push(v_fst_4045_, v___x_4144_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 1, v___x_4081_);
lean_ctor_set(v___x_4055_, 0, v___x_4098_);
v___x_4147_ = v___x_4055_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4098_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v___x_4081_);
v___x_4147_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
lean_object* v___x_4149_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 1, v___x_4147_);
v___x_4149_ = v___x_4051_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_fst_4049_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v___x_4147_);
v___x_4149_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4151_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 1, v___x_4149_);
lean_ctor_set(v___x_4047_, 0, v___x_4145_);
v___x_4151_ = v___x_4047_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4145_);
lean_ctor_set(v_reuseFailAlloc_4152_, 1, v___x_4149_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
v_a_4036_ = v___x_4151_;
goto v___jp_4035_;
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
v___jp_4035_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = lean_unsigned_to_nat(1u);
v___x_4038_ = lean_nat_add(v_a_4028_, v___x_4037_);
lean_dec(v_a_4028_);
v_a_4028_ = v___x_4038_;
v_b_4029_ = v_a_4036_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4027_ = stack[0].m_obj;
lean_object* v_a_4028_ = stack[1].m_obj;
lean_object* v_b_4029_ = stack[2].m_obj;
lean_object* v___y_4030_ = stack[3].m_obj;
lean_object* v___y_4031_ = stack[4].m_obj;
lean_object* v___y_4032_ = stack[5].m_obj;
lean_object* v___y_4033_ = stack[6].m_obj;
lean_object* v_res_4171_;
v_res_4171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4027_, v_a_4028_, v_b_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
stack->m_obj
 = v_res_4171_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4172_, lean_object* v_a_4173_, lean_object* v_b_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4172_, v_a_4173_, v_b_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v_upperBound_4172_);
return v_res_4180_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4182_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4183_ = lean_unsigned_to_nat(4u);
v___x_4184_ = lean_unsigned_to_nat(275u);
v___x_4185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4186_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4187_ = l_mkPanicMessageWithDecl(v___x_4186_, v___x_4185_, v___x_4184_, v___x_4183_, v___x_4182_);
return v___x_4187_;
}
}
lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4188_, lean_object* v___x_4189_, lean_object* v___x_4190_, lean_object* v_xs_4191_, lean_object* v_x_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_graph_4198_; lean_object* v_revDeps_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4252_; 
v_graph_4198_ = lean_ctor_get(v_a_4188_, 0);
v_revDeps_4199_ = lean_ctor_get(v_a_4188_, 1);
v_isSharedCheck_4252_ = !lean_is_exclusive(v_a_4188_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4201_ = v_a_4188_;
v_isShared_4202_ = v_isSharedCheck_4252_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_revDeps_4199_);
lean_inc(v_graph_4198_);
lean_dec(v_a_4188_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4252_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v___x_4203_ = lean_array_get_borrowed(v___x_4189_, v_graph_4198_, v___x_4190_);
v___x_4204_ = lean_array_get_size(v_xs_4191_);
v___x_4205_ = lean_array_get_size(v___x_4203_);
v___x_4206_ = lean_nat_dec_eq(v___x_4204_, v___x_4205_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_del_object(v___x_4201_);
lean_dec_ref(v_revDeps_4199_);
lean_dec_ref(v_graph_4198_);
lean_dec_ref(v_xs_4191_);
lean_dec(v___x_4190_);
v___x_4207_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4208_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4207_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
return v___x_4208_;
}
else
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4213_; 
v___x_4209_ = lean_mk_empty_array_with_capacity(v___x_4190_);
lean_inc_n(v___x_4190_, 2);
v___x_4210_ = l_Array_toSubarray___redArg(v_xs_4191_, v___x_4190_, v___x_4204_);
lean_inc(v___x_4203_);
v___x_4211_ = l_Array_toSubarray___redArg(v___x_4203_, v___x_4190_, v___x_4205_);
if (v_isShared_4202_ == 0)
{
lean_ctor_set(v___x_4201_, 1, v___x_4211_);
lean_ctor_set(v___x_4201_, 0, v___x_4210_);
v___x_4213_ = v___x_4201_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4210_);
lean_ctor_set(v_reuseFailAlloc_4251_, 1, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
lean_inc(v___x_4190_);
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4190_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4209_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4204_, v___x_4190_, v___x_4215_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v_snd_4218_; lean_object* v_fst_4219_; lean_object* v_fst_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref_known(v___x_4216_, 1);
v_snd_4218_ = lean_ctor_get(v_a_4217_, 1);
lean_inc(v_snd_4218_);
v_fst_4219_ = lean_ctor_get(v_a_4217_, 0);
lean_inc_n(v_fst_4219_, 2);
lean_dec(v_a_4217_);
v_fst_4220_ = lean_ctor_get(v_snd_4218_, 0);
lean_inc(v_fst_4220_);
lean_dec(v_snd_4218_);
v___x_4221_ = lean_unsigned_to_nat(1u);
v___x_4222_ = lean_array_get_size(v_graph_4198_);
v___x_4223_ = lean_mk_empty_array_with_capacity(v___x_4221_);
v___x_4224_ = lean_array_push(v___x_4223_, v_fst_4219_);
v___x_4225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4222_, v_graph_4198_, v_fst_4219_, v___x_4221_, v___x_4224_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v_fst_4219_);
lean_dec_ref(v_graph_4198_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4234_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4228_ = v___x_4225_;
v_isShared_4229_ = v_isSharedCheck_4234_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4225_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4234_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4230_; lean_object* v___x_4232_; 
v___x_4230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4230_, 0, v_fst_4220_);
lean_ctor_set(v___x_4230_, 1, v_a_4226_);
lean_ctor_set(v___x_4230_, 2, v_revDeps_4199_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4230_);
v___x_4232_ = v___x_4228_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4230_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v_fst_4220_);
lean_dec_ref(v_revDeps_4199_);
v_a_4235_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4225_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4225_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v_revDeps_4199_);
lean_dec_ref(v_graph_4198_);
v_a_4243_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4216_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4216_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getFixedParamPerms___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4188_ = stack[0].m_obj;
lean_object* v___x_4189_ = stack[1].m_obj;
lean_object* v___x_4190_ = stack[2].m_obj;
lean_object* v_xs_4191_ = stack[3].m_obj;
lean_object* v_x_4192_ = stack[4].m_obj;
lean_object* v___y_4193_ = stack[5].m_obj;
lean_object* v___y_4194_ = stack[6].m_obj;
lean_object* v___y_4195_ = stack[7].m_obj;
lean_object* v___y_4196_ = stack[8].m_obj;
lean_object* v_res_4253_;
v_res_4253_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4188_, v___x_4189_, v___x_4190_, v_xs_4191_, v_x_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
stack->m_obj
 = v_res_4253_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4254_, lean_object* v___x_4255_, lean_object* v___x_4256_, lean_object* v_xs_4257_, lean_object* v_x_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4254_, v___x_4255_, v___x_4256_, v_xs_4257_, v_x_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec_ref(v_x_4258_);
lean_dec_ref(v___x_4255_);
return v_res_4264_;
}
}
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4271_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4272_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
lean_inc_ref(v_preDefs_4265_);
v___x_4273_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v_value_4277_; lean_object* v___f_4278_; uint8_t v___x_4279_; lean_object* v___x_4280_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4273_, 1);
v___x_4275_ = lean_unsigned_to_nat(0u);
v___x_4276_ = lean_array_get(v___x_4271_, v_preDefs_4265_, v___x_4275_);
lean_dec_ref(v_preDefs_4265_);
v_value_4277_ = lean_ctor_get(v___x_4276_, 7);
lean_inc_ref(v_value_4277_);
lean_dec(v___x_4276_);
v___f_4278_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4278_, 0, v_a_4274_);
lean_closure_set(v___f_4278_, 1, v___x_4272_);
lean_closure_set(v___f_4278_, 2, v___x_4275_);
v___x_4279_ = 0;
v___x_4280_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4277_, v___f_4278_, v___x_4279_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
return v___x_4280_;
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref(v_preDefs_4265_);
v_a_4281_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4273_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4273_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getFixedParamPerms_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDefs_4265_ = stack[0].m_obj;
lean_object* v_a_4266_ = stack[1].m_obj;
lean_object* v_a_4267_ = stack[2].m_obj;
lean_object* v_a_4268_ = stack[3].m_obj;
lean_object* v_a_4269_ = stack[4].m_obj;
lean_object* v_res_4289_;
v_res_4289_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
stack->m_obj
 = v_res_4289_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
return v_res_4296_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4297_, lean_object* v___x_4298_, lean_object* v___x_4299_, lean_object* v_inst_4300_, lean_object* v_R_4301_, lean_object* v_a_4302_, lean_object* v_b_4303_, lean_object* v_c_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4297_, v___x_4298_, v___x_4299_, v_a_4302_, v_b_4303_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
return v___x_4310_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4297_ = stack[0].m_obj;
lean_object* v___x_4298_ = stack[1].m_obj;
lean_object* v___x_4299_ = stack[2].m_obj;
lean_object* v_a_4302_ = stack[5].m_obj;
lean_object* v_b_4303_ = stack[6].m_obj;
lean_object* v___y_4305_ = stack[8].m_obj;
lean_object* v___y_4306_ = stack[9].m_obj;
lean_object* v___y_4307_ = stack[10].m_obj;
lean_object* v___y_4308_ = stack[11].m_obj;
lean_object* v_res_4311_;
v_res_4311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4297_, v___x_4298_, v___x_4299_, lean_box(0), lean_box(0), v_a_4302_, v_b_4303_, lean_box(0), v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
stack->m_obj
 = v_res_4311_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4312_, lean_object* v___x_4313_, lean_object* v___x_4314_, lean_object* v_inst_4315_, lean_object* v_R_4316_, lean_object* v_a_4317_, lean_object* v_b_4318_, lean_object* v_c_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4312_, v___x_4313_, v___x_4314_, v_inst_4315_, v_R_4316_, v_a_4317_, v_b_4318_, v_c_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec_ref(v___x_4314_);
lean_dec_ref(v___x_4313_);
lean_dec(v_upperBound_4312_);
return v_res_4325_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4326_, lean_object* v_inst_4327_, lean_object* v_R_4328_, lean_object* v_a_4329_, lean_object* v_b_4330_, lean_object* v_c_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; 
v___x_4337_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4326_, v_a_4329_, v_b_4330_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
return v___x_4337_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4326_ = stack[0].m_obj;
lean_object* v_a_4329_ = stack[3].m_obj;
lean_object* v_b_4330_ = stack[4].m_obj;
lean_object* v___y_4332_ = stack[6].m_obj;
lean_object* v___y_4333_ = stack[7].m_obj;
lean_object* v___y_4334_ = stack[8].m_obj;
lean_object* v___y_4335_ = stack[9].m_obj;
lean_object* v_res_4338_;
v_res_4338_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4326_, lean_box(0), lean_box(0), v_a_4329_, v_b_4330_, lean_box(0), v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
stack->m_obj
 = v_res_4338_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4339_, lean_object* v_inst_4340_, lean_object* v_R_4341_, lean_object* v_a_4342_, lean_object* v_b_4343_, lean_object* v_c_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4339_, v_inst_4340_, v_R_4341_, v_a_4342_, v_b_4343_, v_c_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v_upperBound_4339_);
return v_res_4350_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4351_, size_t v_i_4352_, size_t v_stop_4353_, lean_object* v_b_4354_){
_start:
{
uint8_t v___x_4355_; 
v___x_4355_ = lean_usize_dec_eq(v_i_4352_, v_stop_4353_);
if (v___x_4355_ == 0)
{
size_t v___x_4356_; size_t v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = ((size_t)1ULL);
v___x_4357_ = lean_usize_sub(v_i_4352_, v___x_4356_);
v___x_4358_ = lean_array_uget_borrowed(v_as_4351_, v___x_4357_);
if (lean_obj_tag(v___x_4358_) == 0)
{
v_i_4352_ = v___x_4357_;
goto _start;
}
else
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = lean_unsigned_to_nat(1u);
v___x_4361_ = lean_nat_add(v_b_4354_, v___x_4360_);
lean_dec(v_b_4354_);
v_i_4352_ = v___x_4357_;
v_b_4354_ = v___x_4361_;
goto _start;
}
}
else
{
return v_b_4354_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4351_ = stack[0].m_obj;
size_t v_i_4352_ = stack[1].m_num;
size_t v_stop_4353_ = stack[2].m_num;
lean_object* v_b_4354_ = stack[3].m_obj;
lean_object* v_res_4363_;
v_res_4363_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4351_, v_i_4352_, v_stop_4353_, v_b_4354_);
stack->m_obj
 = v_res_4363_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4364_, lean_object* v_i_4365_, lean_object* v_stop_4366_, lean_object* v_b_4367_){
_start:
{
size_t v_i_boxed_4368_; size_t v_stop_boxed_4369_; lean_object* v_res_4370_; 
v_i_boxed_4368_ = lean_unbox_usize(v_i_4365_);
lean_dec(v_i_4365_);
v_stop_boxed_4369_ = lean_unbox_usize(v_stop_4366_);
lean_dec(v_stop_4366_);
v_res_4370_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4364_, v_i_boxed_4368_, v_stop_boxed_4369_, v_b_4367_);
lean_dec_ref(v_as_4364_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4371_){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; 
v___x_4372_ = lean_unsigned_to_nat(0u);
v___x_4373_ = lean_array_get_size(v_perm_4371_);
v___x_4374_ = lean_nat_dec_lt(v___x_4372_, v___x_4373_);
if (v___x_4374_ == 0)
{
return v___x_4372_;
}
else
{
size_t v___x_4375_; size_t v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = lean_usize_of_nat(v___x_4373_);
v___x_4376_ = ((size_t)0ULL);
v___x_4377_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4371_, v___x_4375_, v___x_4376_, v___x_4372_);
return v___x_4377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4378_);
lean_dec_ref(v_perm_4378_);
return v_res_4379_;
}
}
uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4380_, lean_object* v_i_4381_){
_start:
{
lean_object* v___x_4382_; uint8_t v___x_4383_; 
v___x_4382_ = lean_array_get_size(v_perm_4380_);
v___x_4383_ = lean_nat_dec_lt(v_i_4381_, v___x_4382_);
if (v___x_4383_ == 0)
{
return v___x_4383_;
}
else
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_array_fget_borrowed(v_perm_4380_, v_i_4381_);
if (lean_obj_tag(v___x_4384_) == 0)
{
uint8_t v___x_4385_; 
v___x_4385_ = 0;
return v___x_4385_;
}
else
{
return v___x_4383_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_isFixed_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_4380_ = stack[0].m_obj;
lean_object* v_i_4381_ = stack[1].m_obj;
uint8_t v_res_4386_;
v_res_4386_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4380_, v_i_4381_);
stack->m_num = v_res_4386_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4387_, lean_object* v_i_4388_){
_start:
{
uint8_t v_res_4389_; lean_object* v_r_4390_; 
v_res_4389_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4387_, v_i_4388_);
lean_dec(v_i_4388_);
lean_dec_ref(v_perm_4387_);
v_r_4390_ = lean_box(v_res_4389_);
return v_r_4390_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v___f_4397_; lean_object* v___x_757__overap_4398_; lean_object* v___x_4399_; 
v___f_4397_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_757__overap_4398_ = lean_panic_fn_borrowed(v___f_4397_, v_msg_4391_);
lean_inc(v___y_4395_);
lean_inc_ref(v___y_4394_);
lean_inc(v___y_4393_);
lean_inc_ref(v___y_4392_);
v___x_4399_ = lean_apply_5(v___x_757__overap_4398_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, lean_box(0));
return v___x_4399_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4391_ = stack[0].m_obj;
lean_object* v___y_4392_ = stack[1].m_obj;
lean_object* v___y_4393_ = stack[2].m_obj;
lean_object* v___y_4394_ = stack[3].m_obj;
lean_object* v___y_4395_ = stack[4].m_obj;
lean_object* v_res_4400_;
v_res_4400_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
stack->m_obj
 = v_res_4400_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
return v_res_4407_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4408_, lean_object* v_msg_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
return v___x_4415_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4409_ = stack[1].m_obj;
lean_object* v___y_4410_ = stack[2].m_obj;
lean_object* v___y_4411_ = stack[3].m_obj;
lean_object* v___y_4412_ = stack[4].m_obj;
lean_object* v___y_4413_ = stack[5].m_obj;
lean_object* v_res_4416_;
v_res_4416_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_box(0), v_msg_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
stack->m_obj
 = v_res_4416_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4417_, lean_object* v_msg_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4417_, v_msg_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
return v_res_4424_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4425_, lean_object* v_maxFVars_x3f_4426_, lean_object* v_k_4427_, uint8_t v_cleanupAnnotations_4428_, uint8_t v_whnfType_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___f_4435_; lean_object* v___x_4436_; 
v___f_4435_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4435_, 0, v_k_4427_);
v___x_4436_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4425_, v_maxFVars_x3f_4426_, v___f_4435_, v_cleanupAnnotations_4428_, v_whnfType_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4436_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
v_a_4445_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4436_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4436_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4425_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_4426_ = stack[1].m_obj;
lean_object* v_k_4427_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_4428_ = stack[3].m_num;
uint8_t v_whnfType_4429_ = stack[4].m_num;
lean_object* v___y_4430_ = stack[5].m_obj;
lean_object* v___y_4431_ = stack[6].m_obj;
lean_object* v___y_4432_ = stack[7].m_obj;
lean_object* v___y_4433_ = stack[8].m_obj;
lean_object* v_res_4453_;
v_res_4453_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4425_, v_maxFVars_x3f_4426_, v_k_4427_, v_cleanupAnnotations_4428_, v_whnfType_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
stack->m_obj
 = v_res_4453_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4454_, lean_object* v_maxFVars_x3f_4455_, lean_object* v_k_4456_, lean_object* v_cleanupAnnotations_4457_, lean_object* v_whnfType_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4464_; uint8_t v_whnfType_boxed_4465_; lean_object* v_res_4466_; 
v_cleanupAnnotations_boxed_4464_ = lean_unbox(v_cleanupAnnotations_4457_);
v_whnfType_boxed_4465_ = lean_unbox(v_whnfType_4458_);
v_res_4466_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4454_, v_maxFVars_x3f_4455_, v_k_4456_, v_cleanupAnnotations_boxed_4464_, v_whnfType_boxed_4465_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
return v_res_4466_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4467_, lean_object* v_type_4468_, lean_object* v_maxFVars_x3f_4469_, lean_object* v_k_4470_, uint8_t v_cleanupAnnotations_4471_, uint8_t v_whnfType_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4468_, v_maxFVars_x3f_4469_, v_k_4470_, v_cleanupAnnotations_4471_, v_whnfType_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
return v___x_4478_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4468_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_4469_ = stack[2].m_obj;
lean_object* v_k_4470_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_4471_ = stack[4].m_num;
uint8_t v_whnfType_4472_ = stack[5].m_num;
lean_object* v___y_4473_ = stack[6].m_obj;
lean_object* v___y_4474_ = stack[7].m_obj;
lean_object* v___y_4475_ = stack[8].m_obj;
lean_object* v___y_4476_ = stack[9].m_obj;
lean_object* v_res_4479_;
v_res_4479_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_box(0), v_type_4468_, v_maxFVars_x3f_4469_, v_k_4470_, v_cleanupAnnotations_4471_, v_whnfType_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
stack->m_obj
 = v_res_4479_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4480_, lean_object* v_type_4481_, lean_object* v_maxFVars_x3f_4482_, lean_object* v_k_4483_, lean_object* v_cleanupAnnotations_4484_, lean_object* v_whnfType_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4491_; uint8_t v_whnfType_boxed_4492_; lean_object* v_res_4493_; 
v_cleanupAnnotations_boxed_4491_ = lean_unbox(v_cleanupAnnotations_4484_);
v_whnfType_boxed_4492_ = lean_unbox(v_whnfType_4485_);
v_res_4493_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4480_, v_type_4481_, v_maxFVars_x3f_4482_, v_k_4483_, v_cleanupAnnotations_boxed_4491_, v_whnfType_boxed_4492_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
return v_res_4493_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4496_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4497_ = lean_unsigned_to_nat(6u);
v___x_4498_ = lean_unsigned_to_nat(329u);
v___x_4499_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4500_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4501_ = l_mkPanicMessageWithDecl(v___x_4500_, v___x_4499_, v___x_4498_, v___x_4497_, v___x_4496_);
return v___x_4501_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4506_ = lean_unsigned_to_nat(8u);
v___x_4507_ = lean_unsigned_to_nat(322u);
v___x_4508_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4509_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4510_ = l_mkPanicMessageWithDecl(v___x_4509_, v___x_4508_, v___x_4507_, v___x_4506_, v___x_4505_);
return v___x_4510_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4512_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4513_ = lean_unsigned_to_nat(8u);
v___x_4514_ = lean_unsigned_to_nat(325u);
v___x_4515_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4516_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4517_ = l_mkPanicMessageWithDecl(v___x_4516_, v___x_4515_, v___x_4514_, v___x_4513_, v___x_4512_);
return v___x_4517_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4519_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4520_ = lean_unsigned_to_nat(8u);
v___x_4521_ = lean_unsigned_to_nat(324u);
v___x_4522_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4524_ = l_mkPanicMessageWithDecl(v___x_4523_, v___x_4522_, v___x_4521_, v___x_4520_, v___x_4519_);
return v___x_4524_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4525_, lean_object* v___x_4526_, lean_object* v_xs_4527_, lean_object* v_val_4528_, lean_object* v_i_4529_, lean_object* v_perm_4530_, lean_object* v_k_4531_, lean_object* v_xs_x27_4532_, lean_object* v_type_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v___x_4539_; uint8_t v___x_4540_; 
v___x_4539_ = lean_array_get_size(v_xs_x27_4532_);
v___x_4540_ = lean_nat_dec_eq(v___x_4539_, v___x_4525_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
lean_dec_ref(v_type_4533_);
lean_dec_ref(v_k_4531_);
lean_dec_ref(v_perm_4530_);
lean_dec_ref(v_xs_4527_);
v___x_4541_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4542_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4541_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
return v___x_4542_;
}
else
{
lean_object* v___x_4543_; lean_object* v_x_4544_; lean_object* v___x_4545_; 
v___x_4543_ = lean_unsigned_to_nat(0u);
v_x_4544_ = lean_array_get_borrowed(v___x_4526_, v_xs_x27_4532_, v___x_4543_);
lean_inc(v___y_4537_);
lean_inc_ref(v___y_4536_);
lean_inc(v___y_4535_);
lean_inc_ref(v___y_4534_);
lean_inc(v_x_4544_);
v___x_4545_ = lean_infer_type(v_x_4544_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; uint8_t v___x_4547_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v___x_4545_, 1);
v___x_4547_ = l_Lean_Expr_hasLooseBVars(v_a_4546_);
lean_dec(v_a_4546_);
if (v___x_4547_ == 0)
{
lean_object* v___x_4548_; uint8_t v___x_4549_; 
v___x_4548_ = lean_array_get_size(v_xs_4527_);
v___x_4549_ = lean_nat_dec_lt(v_val_4528_, v___x_4548_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
lean_dec_ref(v_type_4533_);
lean_dec_ref(v_k_4531_);
lean_dec_ref(v_perm_4530_);
lean_dec_ref(v_xs_4527_);
v___x_4550_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4551_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4550_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
return v___x_4551_;
}
else
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4552_ = lean_nat_add(v_i_4529_, v___x_4525_);
lean_inc(v_x_4544_);
v___x_4553_ = lean_array_set(v_xs_4527_, v_val_4528_, v_x_4544_);
v___x_4554_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4530_, v_k_4531_, v___x_4552_, v_type_4533_, v___x_4553_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
return v___x_4554_;
}
}
else
{
lean_object* v___x_4555_; lean_object* v___x_4556_; 
lean_dec_ref(v_type_4533_);
lean_dec_ref(v_k_4531_);
lean_dec_ref(v_perm_4530_);
lean_dec_ref(v_xs_4527_);
v___x_4555_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4556_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4555_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
return v___x_4556_;
}
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec_ref(v_type_4533_);
lean_dec_ref(v_k_4531_);
lean_dec_ref(v_perm_4530_);
lean_dec_ref(v_xs_4527_);
v_a_4557_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4545_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4545_);
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
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4525_ = stack[0].m_obj;
lean_object* v___x_4526_ = stack[1].m_obj;
lean_object* v_xs_4527_ = stack[2].m_obj;
lean_object* v_val_4528_ = stack[3].m_obj;
lean_object* v_i_4529_ = stack[4].m_obj;
lean_object* v_perm_4530_ = stack[5].m_obj;
lean_object* v_k_4531_ = stack[6].m_obj;
lean_object* v_xs_x27_4532_ = stack[7].m_obj;
lean_object* v_type_4533_ = stack[8].m_obj;
lean_object* v___y_4534_ = stack[9].m_obj;
lean_object* v___y_4535_ = stack[10].m_obj;
lean_object* v___y_4536_ = stack[11].m_obj;
lean_object* v___y_4537_ = stack[12].m_obj;
lean_object* v_res_4565_;
v_res_4565_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4525_, v___x_4526_, v_xs_4527_, v_val_4528_, v_i_4529_, v_perm_4530_, v_k_4531_, v_xs_x27_4532_, v_type_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
stack->m_obj
 = v_res_4565_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4566_, lean_object* v___x_4567_, lean_object* v_xs_4568_, lean_object* v_val_4569_, lean_object* v_i_4570_, lean_object* v_perm_4571_, lean_object* v_k_4572_, lean_object* v_xs_x27_4573_, lean_object* v_type_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4566_, v___x_4567_, v_xs_4568_, v_val_4569_, v_i_4570_, v_perm_4571_, v_k_4572_, v_xs_x27_4573_, v_type_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec_ref(v_xs_x27_4573_);
lean_dec(v_i_4570_);
lean_dec(v_val_4569_);
lean_dec_ref(v___x_4567_);
lean_dec(v___x_4566_);
return v_res_4580_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4581_, lean_object* v_k_4582_, lean_object* v_i_4583_, lean_object* v_type_4584_, lean_object* v_xs_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v___x_4591_; uint8_t v___x_4592_; 
v___x_4591_ = lean_array_get_size(v_perm_4581_);
v___x_4592_ = lean_nat_dec_lt(v_i_4583_, v___x_4591_);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; 
lean_dec_ref(v_type_4584_);
lean_dec(v_i_4583_);
lean_dec_ref(v_perm_4581_);
lean_inc(v_a_4589_);
lean_inc_ref(v_a_4588_);
lean_inc(v_a_4587_);
lean_inc_ref(v_a_4586_);
v___x_4593_ = lean_apply_6(v_k_4582_, v_xs_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, lean_box(0));
return v___x_4593_;
}
else
{
lean_object* v___x_4594_; 
v___x_4594_ = lean_array_fget_borrowed(v_perm_4581_, v_i_4583_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v___x_4595_; 
lean_inc(v_a_4589_);
lean_inc_ref(v_a_4588_);
lean_inc(v_a_4587_);
lean_inc_ref(v_a_4586_);
v___x_4595_ = lean_whnf(v_type_4584_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; uint8_t v___x_4597_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
lean_inc(v_a_4596_);
lean_dec_ref_known(v___x_4595_, 1);
v___x_4597_ = l_Lean_Expr_isForall(v_a_4596_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
lean_dec(v_a_4596_);
lean_dec_ref(v_xs_4585_);
lean_dec(v_i_4583_);
lean_dec_ref(v_k_4582_);
lean_dec_ref(v_perm_4581_);
v___x_4598_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4599_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4598_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4599_;
}
else
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v___x_4600_ = lean_unsigned_to_nat(1u);
v___x_4601_ = lean_nat_add(v_i_4583_, v___x_4600_);
lean_dec(v_i_4583_);
v___x_4602_ = l_Lean_Expr_bindingBody_x21(v_a_4596_);
lean_dec(v_a_4596_);
v_i_4583_ = v___x_4601_;
v_type_4584_ = v___x_4602_;
goto _start;
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
lean_dec_ref(v_xs_4585_);
lean_dec(v_i_4583_);
lean_dec_ref(v_k_4582_);
lean_dec_ref(v_perm_4581_);
v_a_4604_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4595_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4595_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
else
{
lean_object* v_val_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___f_4615_; lean_object* v___x_4616_; uint8_t v___x_4617_; lean_object* v___x_4618_; 
v_val_4612_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_val_4612_);
v___x_4613_ = l_Lean_instInhabitedExpr;
v___x_4614_ = lean_unsigned_to_nat(1u);
v___f_4615_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4615_, 0, v___x_4614_);
lean_closure_set(v___f_4615_, 1, v___x_4613_);
lean_closure_set(v___f_4615_, 2, v_xs_4585_);
lean_closure_set(v___f_4615_, 3, v_val_4612_);
lean_closure_set(v___f_4615_, 4, v_i_4583_);
lean_closure_set(v___f_4615_, 5, v_perm_4581_);
lean_closure_set(v___f_4615_, 6, v_k_4582_);
v___x_4616_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4617_ = 0;
v___x_4618_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4584_, v___x_4616_, v___f_4615_, v___x_4592_, v___x_4617_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
return v___x_4618_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_4581_ = stack[0].m_obj;
lean_object* v_k_4582_ = stack[1].m_obj;
lean_object* v_i_4583_ = stack[2].m_obj;
lean_object* v_type_4584_ = stack[3].m_obj;
lean_object* v_xs_4585_ = stack[4].m_obj;
lean_object* v_a_4586_ = stack[5].m_obj;
lean_object* v_a_4587_ = stack[6].m_obj;
lean_object* v_a_4588_ = stack[7].m_obj;
lean_object* v_a_4589_ = stack[8].m_obj;
lean_object* v_res_4619_;
v_res_4619_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4581_, v_k_4582_, v_i_4583_, v_type_4584_, v_xs_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
stack->m_obj
 = v_res_4619_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4620_, lean_object* v_k_4621_, lean_object* v_i_4622_, lean_object* v_type_4623_, lean_object* v_xs_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4620_, v_k_4621_, v_i_4622_, v_type_4623_, v_xs_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
return v_res_4630_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4631_, lean_object* v_perm_4632_, lean_object* v_k_4633_, lean_object* v_i_4634_, lean_object* v_type_4635_, lean_object* v_xs_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4642_; 
v___x_4642_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4632_, v_k_4633_, v_i_4634_, v_type_4635_, v_xs_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
return v___x_4642_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_4632_ = stack[1].m_obj;
lean_object* v_k_4633_ = stack[2].m_obj;
lean_object* v_i_4634_ = stack[3].m_obj;
lean_object* v_type_4635_ = stack[4].m_obj;
lean_object* v_xs_4636_ = stack[5].m_obj;
lean_object* v_a_4637_ = stack[6].m_obj;
lean_object* v_a_4638_ = stack[7].m_obj;
lean_object* v_a_4639_ = stack[8].m_obj;
lean_object* v_a_4640_ = stack[9].m_obj;
lean_object* v_res_4643_;
v_res_4643_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_box(0), v_perm_4632_, v_k_4633_, v_i_4634_, v_type_4635_, v_xs_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
stack->m_obj
 = v_res_4643_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4644_, lean_object* v_perm_4645_, lean_object* v_k_4646_, lean_object* v_i_4647_, lean_object* v_type_4648_, lean_object* v_xs_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4644_, v_perm_4645_, v_k_4646_, v_i_4647_, v_type_4648_, v_xs_4649_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_);
lean_dec(v_a_4653_);
lean_dec_ref(v_a_4652_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
return v_res_4655_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_unsigned_to_nat(0u);
v___x_4657_ = l_Lean_Level_ofNat(v___x_4656_);
return v___x_4657_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4658_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4659_ = l_Lean_mkSort(v___x_4658_);
return v___x_4659_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4660_, lean_object* v_type_4661_, lean_object* v_k_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4668_ = lean_unsigned_to_nat(0u);
v___x_4669_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4660_);
v___x_4670_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4671_ = lean_mk_array(v___x_4669_, v___x_4670_);
v___x_4672_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4660_, v_k_4662_, v___x_4668_, v_type_4661_, v___x_4671_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
return v___x_4672_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_4660_ = stack[0].m_obj;
lean_object* v_type_4661_ = stack[1].m_obj;
lean_object* v_k_4662_ = stack[2].m_obj;
lean_object* v_a_4663_ = stack[3].m_obj;
lean_object* v_a_4664_ = stack[4].m_obj;
lean_object* v_a_4665_ = stack[5].m_obj;
lean_object* v_a_4666_ = stack[6].m_obj;
lean_object* v_res_4673_;
v_res_4673_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4660_, v_type_4661_, v_k_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
stack->m_obj
 = v_res_4673_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4674_, lean_object* v_type_4675_, lean_object* v_k_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4674_, v_type_4675_, v_k_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
return v_res_4682_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4683_, lean_object* v_perm_4684_, lean_object* v_type_4685_, lean_object* v_k_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v___x_4692_; 
v___x_4692_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4684_, v_type_4685_, v_k_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_);
return v___x_4692_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_4684_ = stack[1].m_obj;
lean_object* v_type_4685_ = stack[2].m_obj;
lean_object* v_k_4686_ = stack[3].m_obj;
lean_object* v_a_4687_ = stack[4].m_obj;
lean_object* v_a_4688_ = stack[5].m_obj;
lean_object* v_a_4689_ = stack[6].m_obj;
lean_object* v_a_4690_ = stack[7].m_obj;
lean_object* v_res_4693_;
v_res_4693_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_4684_, v_type_4685_, v_k_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_);
stack->m_obj
 = v_res_4693_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4694_, lean_object* v_perm_4695_, lean_object* v_type_4696_, lean_object* v_k_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4694_, v_perm_4695_, v_type_4696_, v_k_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_);
lean_dec(v_a_4701_);
lean_dec_ref(v_a_4700_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
return v_res_4703_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4704_, lean_object* v_runInBase_4705_, lean_object* v_b_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4712_ = lean_apply_1(v_k_4704_, v_b_4706_);
lean_inc(v___y_4710_);
lean_inc_ref(v___y_4709_);
lean_inc(v___y_4708_);
lean_inc_ref(v___y_4707_);
v___x_4713_ = lean_apply_7(v_runInBase_4705_, lean_box(0), v___x_4712_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, lean_box(0));
return v___x_4713_;
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4704_ = stack[0].m_obj;
lean_object* v_runInBase_4705_ = stack[1].m_obj;
lean_object* v_b_4706_ = stack[2].m_obj;
lean_object* v___y_4707_ = stack[3].m_obj;
lean_object* v___y_4708_ = stack[4].m_obj;
lean_object* v___y_4709_ = stack[5].m_obj;
lean_object* v___y_4710_ = stack[6].m_obj;
lean_object* v_res_4714_;
v_res_4714_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4704_, v_runInBase_4705_, v_b_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
stack->m_obj
 = v_res_4714_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4715_, lean_object* v_runInBase_4716_, lean_object* v_b_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4715_, v_runInBase_4716_, v_b_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
return v_res_4723_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4724_, lean_object* v_perm_4725_, lean_object* v_type_4726_, lean_object* v_runInBase_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v___f_4733_; lean_object* v___x_4734_; 
v___f_4733_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4733_, 0, v_k_4724_);
lean_closure_set(v___f_4733_, 1, v_runInBase_4727_);
v___x_4734_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4725_, v_type_4726_, v___f_4733_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
return v___x_4734_;
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4724_ = stack[0].m_obj;
lean_object* v_perm_4725_ = stack[1].m_obj;
lean_object* v_type_4726_ = stack[2].m_obj;
lean_object* v_runInBase_4727_ = stack[3].m_obj;
lean_object* v___y_4728_ = stack[4].m_obj;
lean_object* v___y_4729_ = stack[5].m_obj;
lean_object* v___y_4730_ = stack[6].m_obj;
lean_object* v___y_4731_ = stack[7].m_obj;
lean_object* v_res_4735_;
v_res_4735_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4724_, v_perm_4725_, v_type_4726_, v_runInBase_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
stack->m_obj
 = v_res_4735_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4736_, lean_object* v_perm_4737_, lean_object* v_type_4738_, lean_object* v_runInBase_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4736_, v_perm_4737_, v_type_4738_, v_runInBase_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4746_, lean_object* v_inst_4747_, lean_object* v_perm_4748_, lean_object* v_type_4749_, lean_object* v_k_4750_){
_start:
{
lean_object* v_toBind_4751_; lean_object* v_liftWith_4752_; lean_object* v_restoreM_4753_; lean_object* v___f_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v_toBind_4751_ = lean_ctor_get(v_inst_4747_, 1);
lean_inc(v_toBind_4751_);
lean_dec_ref(v_inst_4747_);
v_liftWith_4752_ = lean_ctor_get(v_inst_4746_, 0);
lean_inc(v_liftWith_4752_);
v_restoreM_4753_ = lean_ctor_get(v_inst_4746_, 1);
lean_inc(v_restoreM_4753_);
lean_dec_ref(v_inst_4746_);
v___f_4754_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4754_, 0, v_k_4750_);
lean_closure_set(v___f_4754_, 1, v_perm_4748_);
lean_closure_set(v___f_4754_, 2, v_type_4749_);
v___x_4755_ = lean_apply_2(v_liftWith_4752_, lean_box(0), v___f_4754_);
v___x_4756_ = lean_apply_1(v_restoreM_4753_, lean_box(0));
v___x_4757_ = lean_apply_4(v_toBind_4751_, lean_box(0), lean_box(0), v___x_4755_, v___x_4756_);
return v___x_4757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4758_, lean_object* v_00_u03b1_4759_, lean_object* v_inst_4760_, lean_object* v_inst_4761_, lean_object* v_perm_4762_, lean_object* v_type_4763_, lean_object* v_k_4764_){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4760_, v_inst_4761_, v_perm_4762_, v_type_4763_, v_k_4764_);
return v___x_4765_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v___f_4772_; lean_object* v___x_512__overap_4773_; lean_object* v___x_4774_; 
v___f_4772_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_512__overap_4773_ = lean_panic_fn_borrowed(v___f_4772_, v_msg_4766_);
lean_inc(v___y_4770_);
lean_inc_ref(v___y_4769_);
lean_inc(v___y_4768_);
lean_inc_ref(v___y_4767_);
v___x_4774_ = lean_apply_5(v___x_512__overap_4773_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, lean_box(0));
return v___x_4774_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4766_ = stack[0].m_obj;
lean_object* v___y_4767_ = stack[1].m_obj;
lean_object* v___y_4768_ = stack[2].m_obj;
lean_object* v___y_4769_ = stack[3].m_obj;
lean_object* v___y_4770_ = stack[4].m_obj;
lean_object* v_res_4775_;
v_res_4775_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_);
stack->m_obj
 = v_res_4775_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
return v_res_4782_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4785_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4786_ = lean_unsigned_to_nat(10u);
v___x_4787_ = lean_unsigned_to_nat(353u);
v___x_4788_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4789_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4790_ = l_mkPanicMessageWithDecl(v___x_4789_, v___x_4788_, v___x_4787_, v___x_4786_, v___x_4785_);
return v___x_4790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4791_, lean_object* v_xs_4792_, lean_object* v_tail_4793_, lean_object* v_ys_4794_, lean_object* v_type_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v_res_4801_; 
v_res_4801_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4791_, v_xs_4792_, v_tail_4793_, v_ys_4794_, v_type_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec_ref(v_ys_4794_);
lean_dec(v___x_4791_);
return v_res_4801_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4802_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4803_ = lean_unsigned_to_nat(8u);
v___x_4804_ = lean_unsigned_to_nat(349u);
v___x_4805_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4806_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4807_ = l_mkPanicMessageWithDecl(v___x_4806_, v___x_4805_, v___x_4804_, v___x_4803_, v___x_4802_);
return v___x_4807_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4808_, lean_object* v_x_4809_, lean_object* v_x_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_){
_start:
{
if (lean_obj_tag(v_x_4809_) == 0)
{
lean_object* v___x_4816_; 
lean_dec_ref(v_xs_4808_);
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v_x_4810_);
return v___x_4816_;
}
else
{
lean_object* v_head_4817_; 
v_head_4817_ = lean_ctor_get(v_x_4809_, 0);
if (lean_obj_tag(v_head_4817_) == 0)
{
lean_object* v_tail_4818_; lean_object* v___x_4819_; lean_object* v___f_4820_; lean_object* v___x_4821_; uint8_t v___x_4822_; lean_object* v___x_4823_; 
v_tail_4818_ = lean_ctor_get(v_x_4809_, 1);
lean_inc(v_tail_4818_);
lean_dec_ref_known(v_x_4809_, 2);
v___x_4819_ = lean_unsigned_to_nat(1u);
v___f_4820_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4820_, 0, v___x_4819_);
lean_closure_set(v___f_4820_, 1, v_xs_4808_);
lean_closure_set(v___f_4820_, 2, v_tail_4818_);
v___x_4821_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4822_ = 0;
v___x_4823_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4810_, v___x_4821_, v___f_4820_, v___x_4822_, v___x_4822_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
return v___x_4823_;
}
else
{
lean_object* v_tail_4824_; lean_object* v_val_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
lean_inc_ref(v_head_4817_);
v_tail_4824_ = lean_ctor_get(v_x_4809_, 1);
lean_inc(v_tail_4824_);
lean_dec_ref_known(v_x_4809_, 2);
v_val_4825_ = lean_ctor_get(v_head_4817_, 0);
lean_inc(v_val_4825_);
lean_dec_ref_known(v_head_4817_, 1);
v___x_4826_ = lean_array_get_size(v_xs_4808_);
v___x_4827_ = lean_nat_dec_lt(v_val_4825_, v___x_4826_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
lean_dec(v_val_4825_);
lean_dec(v_tail_4824_);
lean_dec_ref(v_x_4810_);
lean_dec_ref(v_xs_4808_);
v___x_4828_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4829_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4828_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
return v___x_4829_;
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4830_ = l_Lean_instInhabitedExpr;
v___x_4831_ = lean_array_get_borrowed(v___x_4830_, v_xs_4808_, v_val_4825_);
lean_dec(v_val_4825_);
v___x_4832_ = lean_unsigned_to_nat(1u);
v___x_4833_ = lean_mk_empty_array_with_capacity(v___x_4832_);
lean_inc(v___x_4831_);
v___x_4834_ = lean_array_push(v___x_4833_, v___x_4831_);
v___x_4835_ = l_Lean_Meta_instantiateForall(v_x_4810_, v___x_4834_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
lean_dec_ref(v___x_4834_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref_known(v___x_4835_, 1);
v_x_4809_ = v_tail_4824_;
v_x_4810_ = v_a_4836_;
goto _start;
}
else
{
lean_dec(v_tail_4824_);
lean_dec_ref(v_xs_4808_);
return v___x_4835_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_4808_ = stack[0].m_obj;
lean_object* v_x_4809_ = stack[1].m_obj;
lean_object* v_x_4810_ = stack[2].m_obj;
lean_object* v_a_4811_ = stack[3].m_obj;
lean_object* v_a_4812_ = stack[4].m_obj;
lean_object* v_a_4813_ = stack[5].m_obj;
lean_object* v_a_4814_ = stack[6].m_obj;
lean_object* v_res_4838_;
v_res_4838_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4808_, v_x_4809_, v_x_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_);
stack->m_obj
 = v_res_4838_;
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4839_, lean_object* v_xs_4840_, lean_object* v_tail_4841_, lean_object* v_ys_4842_, lean_object* v_type_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; uint8_t v___x_4850_; 
v___x_4849_ = lean_array_get_size(v_ys_4842_);
v___x_4850_ = lean_nat_dec_eq(v___x_4849_, v___x_4839_);
if (v___x_4850_ == 0)
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
lean_dec_ref(v_type_4843_);
lean_dec(v_tail_4841_);
lean_dec_ref(v_xs_4840_);
v___x_4851_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4852_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4851_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4852_;
}
else
{
lean_object* v___x_4853_; 
v___x_4853_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4840_, v_tail_4841_, v_type_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v_a_4854_; uint8_t v___x_4855_; uint8_t v___x_4856_; lean_object* v___x_4857_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
lean_inc(v_a_4854_);
lean_dec_ref_known(v___x_4853_, 1);
v___x_4855_ = 0;
v___x_4856_ = 1;
v___x_4857_ = l_Lean_Meta_mkForallFVars(v_ys_4842_, v_a_4854_, v___x_4855_, v___x_4850_, v___x_4850_, v___x_4856_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4857_;
}
else
{
return v___x_4853_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4839_ = stack[0].m_obj;
lean_object* v_xs_4840_ = stack[1].m_obj;
lean_object* v_tail_4841_ = stack[2].m_obj;
lean_object* v_ys_4842_ = stack[3].m_obj;
lean_object* v_type_4843_ = stack[4].m_obj;
lean_object* v___y_4844_ = stack[5].m_obj;
lean_object* v___y_4845_ = stack[6].m_obj;
lean_object* v___y_4846_ = stack[7].m_obj;
lean_object* v___y_4847_ = stack[8].m_obj;
lean_object* v_res_4858_;
v_res_4858_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4839_, v_xs_4840_, v_tail_4841_, v_ys_4842_, v_type_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
stack->m_obj
 = v_res_4858_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4859_, lean_object* v_x_4860_, lean_object* v_x_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4859_, v_x_4860_, v_x_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_);
lean_dec(v_a_4865_);
lean_dec_ref(v_a_4864_);
lean_dec(v_a_4863_);
lean_dec_ref(v_a_4862_);
return v_res_4867_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4870_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4871_ = lean_unsigned_to_nat(2u);
v___x_4872_ = lean_unsigned_to_nat(343u);
v___x_4873_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4874_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4875_ = l_mkPanicMessageWithDecl(v___x_4874_, v___x_4873_, v___x_4872_, v___x_4871_, v___x_4870_);
return v___x_4875_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4876_, lean_object* v_type_u2080_4877_, lean_object* v_xs_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; uint8_t v___x_4886_; 
v___x_4884_ = lean_array_get_size(v_xs_4878_);
v___x_4885_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4876_);
v___x_4886_ = lean_nat_dec_eq(v___x_4884_, v___x_4885_);
lean_dec(v___x_4885_);
if (v___x_4886_ == 0)
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
lean_dec_ref(v_xs_4878_);
lean_dec_ref(v_type_u2080_4877_);
lean_dec_ref(v_perm_4876_);
v___x_4887_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4888_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4887_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
return v___x_4888_;
}
else
{
lean_object* v_mask_4889_; lean_object* v___x_4890_; 
v_mask_4889_ = lean_array_to_list(v_perm_4876_);
v___x_4890_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4878_, v_mask_4889_, v_type_u2080_4877_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
return v___x_4890_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_instantiateForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_4876_ = stack[0].m_obj;
lean_object* v_type_u2080_4877_ = stack[1].m_obj;
lean_object* v_xs_4878_ = stack[2].m_obj;
lean_object* v_a_4879_ = stack[3].m_obj;
lean_object* v_a_4880_ = stack[4].m_obj;
lean_object* v_a_4881_ = stack[5].m_obj;
lean_object* v_a_4882_ = stack[6].m_obj;
lean_object* v_res_4891_;
v_res_4891_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4876_, v_type_u2080_4877_, v_xs_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_);
stack->m_obj
 = v_res_4891_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4892_, lean_object* v_type_u2080_4893_, lean_object* v_xs_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4892_, v_type_u2080_4893_, v_xs_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_);
lean_dec(v_a_4898_);
lean_dec_ref(v_a_4897_);
lean_dec(v_a_4896_);
lean_dec_ref(v_a_4895_);
return v_res_4900_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4901_, lean_object* v_maxFVars_4902_, lean_object* v_k_4903_, uint8_t v_cleanupAnnotations_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_){
_start:
{
lean_object* v___f_4910_; uint8_t v___x_4911_; uint8_t v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___f_4910_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4910_, 0, v_k_4903_);
v___x_4911_ = 1;
v___x_4912_ = 0;
v___x_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4913_, 0, v_maxFVars_4902_);
v___x_4914_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4901_, v___x_4911_, v___x_4912_, v___x_4911_, v___x_4912_, v___x_4913_, v___f_4910_, v_cleanupAnnotations_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
lean_dec_ref_known(v___x_4913_, 1);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4914_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4914_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
v_a_4923_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4914_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4914_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4901_ = stack[0].m_obj;
lean_object* v_maxFVars_4902_ = stack[1].m_obj;
lean_object* v_k_4903_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_4904_ = stack[3].m_num;
lean_object* v___y_4905_ = stack[4].m_obj;
lean_object* v___y_4906_ = stack[5].m_obj;
lean_object* v___y_4907_ = stack[6].m_obj;
lean_object* v___y_4908_ = stack[7].m_obj;
lean_object* v_res_4931_;
v_res_4931_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4901_, v_maxFVars_4902_, v_k_4903_, v_cleanupAnnotations_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
stack->m_obj
 = v_res_4931_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4932_, lean_object* v_maxFVars_4933_, lean_object* v_k_4934_, lean_object* v_cleanupAnnotations_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4941_; lean_object* v_res_4942_; 
v_cleanupAnnotations_boxed_4941_ = lean_unbox(v_cleanupAnnotations_4935_);
v_res_4942_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4932_, v_maxFVars_4933_, v_k_4934_, v_cleanupAnnotations_boxed_4941_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
return v_res_4942_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4943_, lean_object* v_e_4944_, lean_object* v_maxFVars_4945_, lean_object* v_k_4946_, uint8_t v_cleanupAnnotations_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4944_, v_maxFVars_4945_, v_k_4946_, v_cleanupAnnotations_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
return v___x_4953_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4944_ = stack[1].m_obj;
lean_object* v_maxFVars_4945_ = stack[2].m_obj;
lean_object* v_k_4946_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_4947_ = stack[4].m_num;
lean_object* v___y_4948_ = stack[5].m_obj;
lean_object* v___y_4949_ = stack[6].m_obj;
lean_object* v___y_4950_ = stack[7].m_obj;
lean_object* v___y_4951_ = stack[8].m_obj;
lean_object* v_res_4954_;
v_res_4954_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_box(0), v_e_4944_, v_maxFVars_4945_, v_k_4946_, v_cleanupAnnotations_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
stack->m_obj
 = v_res_4954_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4955_, lean_object* v_e_4956_, lean_object* v_maxFVars_4957_, lean_object* v_k_4958_, lean_object* v_cleanupAnnotations_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4965_; lean_object* v_res_4966_; 
v_cleanupAnnotations_boxed_4965_ = lean_unbox(v_cleanupAnnotations_4959_);
v_res_4966_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4955_, v_e_4956_, v_maxFVars_4957_, v_k_4958_, v_cleanupAnnotations_boxed_4965_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
return v_res_4966_;
}
}
uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4967_){
_start:
{
if (lean_obj_tag(v_x_4967_) == 0)
{
uint8_t v___x_4968_; 
v___x_4968_ = 1;
return v___x_4968_;
}
else
{
lean_object* v_head_4969_; 
v_head_4969_ = lean_ctor_get(v_x_4967_, 0);
if (lean_obj_tag(v_head_4969_) == 0)
{
lean_object* v_tail_4970_; 
v_tail_4970_ = lean_ctor_get(v_x_4967_, 1);
v_x_4967_ = v_tail_4970_;
goto _start;
}
else
{
uint8_t v___x_4972_; 
v___x_4972_ = 0;
return v___x_4972_;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4967_ = stack[0].m_obj;
uint8_t v_res_4973_;
v_res_4973_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4967_);
stack->m_num = v_res_4973_;
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4974_){
_start:
{
uint8_t v_res_4975_; lean_object* v_r_4976_; 
v_res_4975_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4974_);
lean_dec(v_x_4974_);
v_r_4976_ = lean_box(v_res_4975_);
return v_r_4976_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4979_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4980_ = lean_unsigned_to_nat(12u);
v___x_4981_ = lean_unsigned_to_nat(376u);
v___x_4982_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4983_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4984_ = l_mkPanicMessageWithDecl(v___x_4983_, v___x_4982_, v___x_4981_, v___x_4980_, v___x_4979_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4985_, lean_object* v_xs_4986_, lean_object* v_tail_4987_, lean_object* v___x_4988_, lean_object* v___x_4989_, lean_object* v_ys_4990_, lean_object* v_value_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
uint8_t v___x_1176__boxed_4997_; uint8_t v___x_1177__boxed_4998_; lean_object* v_res_4999_; 
v___x_1176__boxed_4997_ = lean_unbox(v___x_4988_);
v___x_1177__boxed_4998_ = lean_unbox(v___x_4989_);
v_res_4999_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4985_, v_xs_4986_, v_tail_4987_, v___x_1176__boxed_4997_, v___x_1177__boxed_4998_, v_ys_4990_, v_value_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec_ref(v_ys_4990_);
lean_dec(v___x_4985_);
return v_res_4999_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5000_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_5001_ = lean_unsigned_to_nat(8u);
v___x_5002_ = lean_unsigned_to_nat(368u);
v___x_5003_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_5004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5005_ = l_mkPanicMessageWithDecl(v___x_5004_, v___x_5003_, v___x_5002_, v___x_5001_, v___x_5000_);
return v___x_5005_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_5006_, lean_object* v_x_5007_, lean_object* v_x_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
if (lean_obj_tag(v_x_5007_) == 0)
{
lean_object* v___x_5014_; 
lean_dec_ref(v_xs_5006_);
v___x_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5014_, 0, v_x_5008_);
return v___x_5014_;
}
else
{
lean_object* v_head_5015_; 
v_head_5015_ = lean_ctor_get(v_x_5007_, 0);
if (lean_obj_tag(v_head_5015_) == 0)
{
lean_object* v_tail_5016_; uint8_t v___x_5017_; 
v_tail_5016_ = lean_ctor_get(v_x_5007_, 1);
lean_inc(v_tail_5016_);
lean_dec_ref_known(v_x_5007_, 2);
v___x_5017_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_5016_);
if (v___x_5017_ == 0)
{
uint8_t v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___f_5022_; lean_object* v___x_5023_; 
v___x_5018_ = 1;
v___x_5019_ = lean_unsigned_to_nat(1u);
v___x_5020_ = lean_box(v___x_5017_);
v___x_5021_ = lean_box(v___x_5018_);
v___f_5022_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_5022_, 0, v___x_5019_);
lean_closure_set(v___f_5022_, 1, v_xs_5006_);
lean_closure_set(v___f_5022_, 2, v_tail_5016_);
lean_closure_set(v___f_5022_, 3, v___x_5020_);
lean_closure_set(v___f_5022_, 4, v___x_5021_);
v___x_5023_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_5008_, v___x_5019_, v___f_5022_, v___x_5017_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5023_;
}
else
{
lean_object* v___x_5024_; 
lean_dec(v_tail_5016_);
lean_dec_ref(v_xs_5006_);
v___x_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5024_, 0, v_x_5008_);
return v___x_5024_;
}
}
else
{
lean_object* v_tail_5025_; lean_object* v_val_5026_; lean_object* v___x_5027_; uint8_t v___x_5028_; 
lean_inc_ref(v_head_5015_);
v_tail_5025_ = lean_ctor_get(v_x_5007_, 1);
lean_inc(v_tail_5025_);
lean_dec_ref_known(v_x_5007_, 2);
v_val_5026_ = lean_ctor_get(v_head_5015_, 0);
lean_inc(v_val_5026_);
lean_dec_ref_known(v_head_5015_, 1);
v___x_5027_ = lean_array_get_size(v_xs_5006_);
v___x_5028_ = lean_nat_dec_lt(v_val_5026_, v___x_5027_);
if (v___x_5028_ == 0)
{
lean_object* v___x_5029_; lean_object* v___x_5030_; 
lean_dec(v_val_5026_);
lean_dec(v_tail_5025_);
lean_dec_ref(v_x_5008_);
lean_dec_ref(v_xs_5006_);
v___x_5029_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_5030_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5029_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
return v___x_5030_;
}
else
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
v___x_5031_ = l_Lean_instInhabitedExpr;
v___x_5032_ = lean_array_get_borrowed(v___x_5031_, v_xs_5006_, v_val_5026_);
lean_dec(v_val_5026_);
v___x_5033_ = lean_unsigned_to_nat(1u);
v___x_5034_ = lean_mk_empty_array_with_capacity(v___x_5033_);
lean_inc(v___x_5032_);
v___x_5035_ = lean_array_push(v___x_5034_, v___x_5032_);
v___x_5036_ = l_Lean_Meta_instantiateLambda(v_x_5008_, v___x_5035_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
lean_dec_ref(v___x_5035_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v_x_5007_ = v_tail_5025_;
v_x_5008_ = v_a_5037_;
goto _start;
}
else
{
lean_dec(v_tail_5025_);
lean_dec_ref(v_xs_5006_);
return v___x_5036_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_5006_ = stack[0].m_obj;
lean_object* v_x_5007_ = stack[1].m_obj;
lean_object* v_x_5008_ = stack[2].m_obj;
lean_object* v_a_5009_ = stack[3].m_obj;
lean_object* v_a_5010_ = stack[4].m_obj;
lean_object* v_a_5011_ = stack[5].m_obj;
lean_object* v_a_5012_ = stack[6].m_obj;
lean_object* v_res_5039_;
v_res_5039_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5006_, v_x_5007_, v_x_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
stack->m_obj
 = v_res_5039_;
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_5040_, lean_object* v_xs_5041_, lean_object* v_tail_5042_, uint8_t v___x_5043_, uint8_t v___x_5044_, lean_object* v_ys_5045_, lean_object* v_value_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_){
_start:
{
lean_object* v___x_5052_; uint8_t v___x_5053_; 
v___x_5052_ = lean_array_get_size(v_ys_5045_);
v___x_5053_ = lean_nat_dec_eq(v___x_5052_, v___x_5040_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; lean_object* v___x_5055_; 
lean_dec_ref(v_value_5046_);
lean_dec(v_tail_5042_);
lean_dec_ref(v_xs_5041_);
v___x_5054_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_5055_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5054_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
return v___x_5055_;
}
else
{
lean_object* v___x_5056_; 
v___x_5056_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5041_, v_tail_5042_, v_value_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v_a_5057_; uint8_t v___x_5058_; lean_object* v___x_5059_; 
v_a_5057_ = lean_ctor_get(v___x_5056_, 0);
lean_inc(v_a_5057_);
lean_dec_ref_known(v___x_5056_, 1);
v___x_5058_ = 1;
v___x_5059_ = l_Lean_Meta_mkLambdaFVars(v_ys_5045_, v_a_5057_, v___x_5043_, v___x_5044_, v___x_5043_, v___x_5044_, v___x_5058_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
return v___x_5059_;
}
else
{
return v___x_5056_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5040_ = stack[0].m_obj;
lean_object* v_xs_5041_ = stack[1].m_obj;
lean_object* v_tail_5042_ = stack[2].m_obj;
uint8_t v___x_5043_ = stack[3].m_num;
uint8_t v___x_5044_ = stack[4].m_num;
lean_object* v_ys_5045_ = stack[5].m_obj;
lean_object* v_value_5046_ = stack[6].m_obj;
lean_object* v___y_5047_ = stack[7].m_obj;
lean_object* v___y_5048_ = stack[8].m_obj;
lean_object* v___y_5049_ = stack[9].m_obj;
lean_object* v___y_5050_ = stack[10].m_obj;
lean_object* v_res_5060_;
v_res_5060_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_5040_, v_xs_5041_, v_tail_5042_, v___x_5043_, v___x_5044_, v_ys_5045_, v_value_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
stack->m_obj
 = v_res_5060_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_5061_, lean_object* v_x_5062_, lean_object* v_x_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5061_, v_x_5062_, v_x_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
lean_dec(v_a_5067_);
lean_dec_ref(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
return v_res_5069_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5071_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5072_ = lean_unsigned_to_nat(2u);
v___x_5073_ = lean_unsigned_to_nat(362u);
v___x_5074_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5075_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5076_ = l_mkPanicMessageWithDecl(v___x_5075_, v___x_5074_, v___x_5073_, v___x_5072_, v___x_5071_);
return v___x_5076_;
}
}
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5077_, lean_object* v_value_u2080_5078_, lean_object* v_xs_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_){
_start:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; 
v___x_5085_ = lean_array_get_size(v_xs_5079_);
v___x_5086_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5077_);
v___x_5087_ = lean_nat_dec_eq(v___x_5085_, v___x_5086_);
lean_dec(v___x_5086_);
if (v___x_5087_ == 0)
{
lean_object* v___x_5088_; lean_object* v___x_5089_; 
lean_dec_ref(v_xs_5079_);
lean_dec_ref(v_value_u2080_5078_);
lean_dec_ref(v_perm_5077_);
v___x_5088_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5089_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5088_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
return v___x_5089_;
}
else
{
lean_object* v_mask_5090_; lean_object* v___x_5091_; 
v_mask_5090_ = lean_array_to_list(v_perm_5077_);
v___x_5091_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5079_, v_mask_5090_, v_value_u2080_5078_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
return v___x_5091_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerm_instantiateLambda_0interp(lean_interpreter_value* stack)
{
lean_object* v_perm_5077_ = stack[0].m_obj;
lean_object* v_value_u2080_5078_ = stack[1].m_obj;
lean_object* v_xs_5079_ = stack[2].m_obj;
lean_object* v_a_5080_ = stack[3].m_obj;
lean_object* v_a_5081_ = stack[4].m_obj;
lean_object* v_a_5082_ = stack[5].m_obj;
lean_object* v_a_5083_ = stack[6].m_obj;
lean_object* v_res_5092_;
v_res_5092_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5077_, v_value_u2080_5078_, v_xs_5079_, v_a_5080_, v_a_5081_, v_a_5082_, v_a_5083_);
stack->m_obj
 = v_res_5092_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5093_, lean_object* v_value_u2080_5094_, lean_object* v_xs_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5093_, v_value_u2080_5094_, v_xs_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_a_5097_);
lean_dec_ref(v_a_5096_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5109_){
_start:
{
lean_object* v___f_5110_; lean_object* v___f_5111_; lean_object* v___f_5112_; lean_object* v___f_5113_; lean_object* v___f_5114_; lean_object* v___f_5115_; lean_object* v___f_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___f_5110_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5111_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5112_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5113_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5114_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5115_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5116_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5117_, 0, v___f_5110_);
lean_ctor_set(v___x_5117_, 1, v___f_5111_);
v___x_5118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5117_);
lean_ctor_set(v___x_5118_, 1, v___f_5112_);
lean_ctor_set(v___x_5118_, 2, v___f_5113_);
lean_ctor_set(v___x_5118_, 3, v___f_5114_);
lean_ctor_set(v___x_5118_, 4, v___f_5115_);
v___x_5119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5119_, 0, v___x_5118_);
lean_ctor_set(v___x_5119_, 1, v___f_5116_);
v___x_5120_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5121_ = l_instInhabitedOfMonad___redArg(v___x_5119_, v___x_5120_);
v___x_5122_ = lean_panic_fn_borrowed(v___x_5121_, v_msg_5109_);
lean_dec(v___x_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5123_, lean_object* v_msg_5124_){
_start:
{
lean_object* v___x_5125_; 
v___x_5125_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5124_);
return v___x_5125_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5128_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5129_ = lean_unsigned_to_nat(8u);
v___x_5130_ = lean_unsigned_to_nat(394u);
v___x_5131_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5132_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5133_ = l_mkPanicMessageWithDecl(v___x_5132_, v___x_5131_, v___x_5130_, v___x_5129_, v___x_5128_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5134_, lean_object* v_x_5135_){
_start:
{
if (lean_obj_tag(v_x_5134_) == 0)
{
return v_x_5135_;
}
else
{
lean_object* v_head_5136_; lean_object* v_fst_5137_; 
v_head_5136_ = lean_ctor_get(v_x_5134_, 0);
v_fst_5137_ = lean_ctor_get(v_head_5136_, 0);
if (lean_obj_tag(v_fst_5137_) == 0)
{
lean_object* v_tail_5138_; 
v_tail_5138_ = lean_ctor_get(v_x_5134_, 1);
lean_inc(v_tail_5138_);
lean_dec_ref_known(v_x_5134_, 2);
v_x_5134_ = v_tail_5138_;
goto _start;
}
else
{
lean_object* v_tail_5140_; lean_object* v_snd_5141_; lean_object* v_val_5142_; lean_object* v___x_5143_; uint8_t v___x_5144_; 
lean_inc_ref(v_fst_5137_);
lean_inc(v_head_5136_);
v_tail_5140_ = lean_ctor_get(v_x_5134_, 1);
lean_inc(v_tail_5140_);
lean_dec_ref_known(v_x_5134_, 2);
v_snd_5141_ = lean_ctor_get(v_head_5136_, 1);
lean_inc(v_snd_5141_);
lean_dec(v_head_5136_);
v_val_5142_ = lean_ctor_get(v_fst_5137_, 0);
lean_inc(v_val_5142_);
lean_dec_ref_known(v_fst_5137_, 1);
v___x_5143_ = lean_array_get_size(v_x_5135_);
v___x_5144_ = lean_nat_dec_lt(v_val_5142_, v___x_5143_);
if (v___x_5144_ == 0)
{
lean_object* v___x_5145_; lean_object* v___x_5146_; 
lean_dec(v_val_5142_);
lean_dec(v_snd_5141_);
lean_dec(v_tail_5140_);
lean_dec_ref(v_x_5135_);
v___x_5145_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5146_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5145_);
return v___x_5146_;
}
else
{
lean_object* v___x_5147_; 
v___x_5147_ = lean_array_set(v_x_5135_, v_val_5142_, v_snd_5141_);
lean_dec(v_val_5142_);
v_x_5134_ = v_tail_5140_;
v_x_5135_ = v___x_5147_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5149_, lean_object* v_x_5150_, lean_object* v_x_5151_){
_start:
{
lean_object* v___x_5152_; 
v___x_5152_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5150_, v_x_5151_);
return v___x_5152_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
v___x_5155_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5156_ = lean_unsigned_to_nat(2u);
v___x_5157_ = lean_unsigned_to_nat(384u);
v___x_5158_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5159_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5160_ = l_mkPanicMessageWithDecl(v___x_5159_, v___x_5158_, v___x_5157_, v___x_5156_, v___x_5155_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5163_, lean_object* v_xs_5164_){
_start:
{
lean_object* v___x_5165_; lean_object* v___x_5166_; uint8_t v___x_5167_; 
v___x_5165_ = lean_array_get_size(v_xs_5164_);
v___x_5166_ = lean_array_get_size(v_perm_5163_);
v___x_5167_ = lean_nat_dec_eq(v___x_5165_, v___x_5166_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5168_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5169_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5168_);
return v___x_5169_;
}
else
{
lean_object* v___x_5170_; uint8_t v___x_5171_; 
v___x_5170_ = lean_unsigned_to_nat(0u);
v___x_5171_ = lean_nat_dec_eq(v___x_5165_, v___x_5170_);
if (v___x_5171_ == 0)
{
lean_object* v_dummy_5172_; lean_object* v___x_5173_; lean_object* v_ys_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; 
v_dummy_5172_ = lean_array_fget_borrowed(v_xs_5164_, v___x_5170_);
v___x_5173_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5163_);
lean_inc(v_dummy_5172_);
v_ys_5174_ = lean_mk_array(v___x_5173_, v_dummy_5172_);
v___x_5175_ = l_Array_zip___redArg(v_perm_5163_, v_xs_5164_);
v___x_5176_ = lean_array_to_list(v___x_5175_);
v___x_5177_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5176_, v_ys_5174_);
return v___x_5177_;
}
else
{
lean_object* v___x_5178_; 
v___x_5178_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5179_, lean_object* v_xs_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5179_, v_xs_5180_);
lean_dec_ref(v_xs_5180_);
lean_dec_ref(v_perm_5179_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5182_, lean_object* v_perm_5183_, lean_object* v_xs_5184_){
_start:
{
lean_object* v___x_5185_; 
v___x_5185_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5183_, v_xs_5184_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5186_, lean_object* v_perm_5187_, lean_object* v_xs_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5186_, v_perm_5187_, v_xs_5188_);
lean_dec_ref(v_xs_5188_);
lean_dec_ref(v_perm_5187_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5190_, lean_object* v_upperBound_5191_, lean_object* v_perm_5192_, lean_object* v_a_5193_, lean_object* v_b_5194_){
_start:
{
lean_object* v_a_5196_; uint8_t v___x_5203_; 
v___x_5203_ = lean_nat_dec_lt(v_a_5193_, v_upperBound_5191_);
if (v___x_5203_ == 0)
{
lean_dec(v_a_5193_);
return v_b_5194_;
}
else
{
lean_object* v___x_5204_; uint8_t v___x_5205_; 
v___x_5204_ = lean_array_get_size(v_perm_5192_);
v___x_5205_ = lean_nat_dec_lt(v_a_5193_, v___x_5204_);
if (v___x_5205_ == 0)
{
goto v___jp_5200_;
}
else
{
lean_object* v___x_5206_; 
v___x_5206_ = lean_array_fget_borrowed(v_perm_5192_, v_a_5193_);
if (lean_obj_tag(v___x_5206_) == 0)
{
goto v___jp_5200_;
}
else
{
v_a_5196_ = v_b_5194_;
goto v___jp_5195_;
}
}
}
v___jp_5195_:
{
lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5197_ = lean_unsigned_to_nat(1u);
v___x_5198_ = lean_nat_add(v_a_5193_, v___x_5197_);
lean_dec(v_a_5193_);
v_a_5193_ = v___x_5198_;
v_b_5194_ = v_a_5196_;
goto _start;
}
v___jp_5200_:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; 
v___x_5201_ = lean_array_fget_borrowed(v_xs_5190_, v_a_5193_);
lean_inc(v___x_5201_);
v___x_5202_ = lean_array_push(v_b_5194_, v___x_5201_);
v_a_5196_ = v___x_5202_;
goto v___jp_5195_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5207_, lean_object* v_upperBound_5208_, lean_object* v_perm_5209_, lean_object* v_a_5210_, lean_object* v_b_5211_){
_start:
{
lean_object* v_res_5212_; 
v_res_5212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5207_, v_upperBound_5208_, v_perm_5209_, v_a_5210_, v_b_5211_);
lean_dec_ref(v_perm_5209_);
lean_dec(v_upperBound_5208_);
lean_dec_ref(v_xs_5207_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5213_, lean_object* v_xs_5214_){
_start:
{
lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v_ys_5217_; lean_object* v___x_5218_; 
v___x_5215_ = lean_array_get_size(v_xs_5214_);
v___x_5216_ = lean_unsigned_to_nat(0u);
v_ys_5217_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5214_, v___x_5215_, v_perm_5213_, v___x_5216_, v_ys_5217_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5219_, lean_object* v_xs_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5219_, v_xs_5220_);
lean_dec_ref(v_xs_5220_);
lean_dec_ref(v_perm_5219_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5222_, lean_object* v_perm_5223_, lean_object* v_xs_5224_){
_start:
{
lean_object* v___x_5225_; 
v___x_5225_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5223_, v_xs_5224_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5226_, lean_object* v_perm_5227_, lean_object* v_xs_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5226_, v_perm_5227_, v_xs_5228_);
lean_dec_ref(v_xs_5228_);
lean_dec_ref(v_perm_5227_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5230_, lean_object* v_xs_5231_, lean_object* v_upperBound_5232_, lean_object* v_perm_5233_, lean_object* v_inst_5234_, lean_object* v_R_5235_, lean_object* v_a_5236_, lean_object* v_b_5237_, lean_object* v_c_5238_){
_start:
{
lean_object* v___x_5239_; 
v___x_5239_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5231_, v_upperBound_5232_, v_perm_5233_, v_a_5236_, v_b_5237_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5240_, lean_object* v_xs_5241_, lean_object* v_upperBound_5242_, lean_object* v_perm_5243_, lean_object* v_inst_5244_, lean_object* v_R_5245_, lean_object* v_a_5246_, lean_object* v_b_5247_, lean_object* v_c_5248_){
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5240_, v_xs_5241_, v_upperBound_5242_, v_perm_5243_, v_inst_5244_, v_R_5245_, v_a_5246_, v_b_5247_, v_c_5248_);
lean_dec_ref(v_perm_5243_);
lean_dec(v_upperBound_5242_);
lean_dec_ref(v_xs_5241_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5250_){
_start:
{
lean_object* v___x_5251_; lean_object* v___x_5252_; 
v___x_5251_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5252_ = lean_panic_fn_borrowed(v___x_5251_, v_msg_5250_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5253_, lean_object* v_msg_5254_){
_start:
{
lean_object* v___x_5255_; 
v___x_5255_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5254_);
return v___x_5255_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5256_, lean_object* v___x_5257_, lean_object* v_i_5258_, lean_object* v___x_5259_, lean_object* v_as_5260_, size_t v_i_5261_, size_t v_stop_5262_){
_start:
{
uint8_t v___x_5263_; 
v___x_5263_ = lean_usize_dec_eq(v_i_5261_, v_stop_5262_);
if (v___x_5263_ == 0)
{
uint8_t v___x_5264_; uint8_t v___y_5266_; lean_object* v___x_5270_; 
v___x_5264_ = 1;
v___x_5270_ = lean_array_uget_borrowed(v_as_5260_, v_i_5261_);
if (lean_obj_tag(v___x_5270_) == 0)
{
uint8_t v___x_5271_; 
v___x_5271_ = lean_nat_dec_lt(v_j_5256_, v___x_5257_);
v___y_5266_ = v___x_5271_;
goto v___jp_5265_;
}
else
{
uint8_t v___x_5272_; 
v___x_5272_ = lean_nat_dec_lt(v_i_5258_, v___x_5259_);
v___y_5266_ = v___x_5272_;
goto v___jp_5265_;
}
v___jp_5265_:
{
if (v___y_5266_ == 0)
{
size_t v___x_5267_; size_t v___x_5268_; 
v___x_5267_ = ((size_t)1ULL);
v___x_5268_ = lean_usize_add(v_i_5261_, v___x_5267_);
v_i_5261_ = v___x_5268_;
goto _start;
}
else
{
return v___x_5264_;
}
}
}
else
{
uint8_t v___x_5273_; 
v___x_5273_ = 0;
return v___x_5273_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_j_5256_ = stack[0].m_obj;
lean_object* v___x_5257_ = stack[1].m_obj;
lean_object* v_i_5258_ = stack[2].m_obj;
lean_object* v___x_5259_ = stack[3].m_obj;
lean_object* v_as_5260_ = stack[4].m_obj;
size_t v_i_5261_ = stack[5].m_num;
size_t v_stop_5262_ = stack[6].m_num;
uint8_t v_res_5274_;
v_res_5274_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5256_, v___x_5257_, v_i_5258_, v___x_5259_, v_as_5260_, v_i_5261_, v_stop_5262_);
stack->m_num = v_res_5274_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5275_, lean_object* v___x_5276_, lean_object* v_i_5277_, lean_object* v___x_5278_, lean_object* v_as_5279_, lean_object* v_i_5280_, lean_object* v_stop_5281_){
_start:
{
size_t v_i_boxed_5282_; size_t v_stop_boxed_5283_; uint8_t v_res_5284_; lean_object* v_r_5285_; 
v_i_boxed_5282_ = lean_unbox_usize(v_i_5280_);
lean_dec(v_i_5280_);
v_stop_boxed_5283_ = lean_unbox_usize(v_stop_5281_);
lean_dec(v_stop_5281_);
v_res_5284_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5275_, v___x_5276_, v_i_5277_, v___x_5278_, v_as_5279_, v_i_boxed_5282_, v_stop_boxed_5283_);
lean_dec_ref(v_as_5279_);
lean_dec(v___x_5278_);
lean_dec(v_i_5277_);
lean_dec(v___x_5276_);
lean_dec(v_j_5275_);
v_r_5285_ = lean_box(v_res_5284_);
return v_r_5285_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5288_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5289_ = lean_unsigned_to_nat(10u);
v___x_5290_ = lean_unsigned_to_nat(425u);
v___x_5291_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5292_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5293_ = l_mkPanicMessageWithDecl(v___x_5292_, v___x_5291_, v___x_5290_, v___x_5289_, v___x_5288_);
return v___x_5293_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; 
v___x_5295_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5296_ = lean_unsigned_to_nat(12u);
v___x_5297_ = lean_unsigned_to_nat(433u);
v___x_5298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5299_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5300_ = l_mkPanicMessageWithDecl(v___x_5299_, v___x_5298_, v___x_5297_, v___x_5296_, v___x_5295_);
return v___x_5300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5301_, lean_object* v_fixedArgs_5302_, lean_object* v_varyingArgs_5303_, lean_object* v_i_5304_, lean_object* v_j_5305_, lean_object* v_xs_5306_){
_start:
{
lean_object* v_lower_5308_; lean_object* v_upper_5309_; lean_object* v___x_5313_; uint8_t v___x_5314_; 
v___x_5313_ = lean_array_get_size(v_perm_5301_);
v___x_5314_ = lean_nat_dec_lt(v_i_5304_, v___x_5313_);
if (v___x_5314_ == 0)
{
lean_object* v___x_5315_; lean_object* v___x_5316_; uint8_t v___x_5317_; 
lean_dec(v_i_5304_);
lean_dec_ref(v_perm_5301_);
v___x_5315_ = lean_unsigned_to_nat(0u);
v___x_5316_ = lean_array_get_size(v_varyingArgs_5303_);
v___x_5317_ = lean_nat_dec_le(v_j_5305_, v___x_5315_);
if (v___x_5317_ == 0)
{
v_lower_5308_ = v_j_5305_;
v_upper_5309_ = v___x_5316_;
goto v___jp_5307_;
}
else
{
lean_dec(v_j_5305_);
v_lower_5308_ = v___x_5315_;
v_upper_5309_ = v___x_5316_;
goto v___jp_5307_;
}
}
else
{
lean_object* v___x_5318_; 
v___x_5318_ = lean_array_fget_borrowed(v_perm_5301_, v_i_5304_);
if (lean_obj_tag(v___x_5318_) == 1)
{
lean_object* v_val_5319_; lean_object* v___x_5320_; uint8_t v___x_5321_; 
v_val_5319_ = lean_ctor_get(v___x_5318_, 0);
v___x_5320_ = lean_array_get_size(v_fixedArgs_5302_);
v___x_5321_ = lean_nat_dec_lt(v_val_5319_, v___x_5320_);
if (v___x_5321_ == 0)
{
lean_object* v___x_5322_; lean_object* v___x_5323_; 
lean_dec_ref(v_xs_5306_);
lean_dec(v_j_5305_);
lean_dec(v_i_5304_);
lean_dec_ref(v_varyingArgs_5303_);
lean_dec_ref(v_perm_5301_);
v___x_5322_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5323_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5322_);
return v___x_5323_;
}
else
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; 
v___x_5324_ = lean_unsigned_to_nat(1u);
v___x_5325_ = lean_nat_add(v_i_5304_, v___x_5324_);
lean_dec(v_i_5304_);
v___x_5326_ = lean_array_fget_borrowed(v_fixedArgs_5302_, v_val_5319_);
lean_inc(v___x_5326_);
v___x_5327_ = lean_array_push(v_xs_5306_, v___x_5326_);
v_i_5304_ = v___x_5325_;
v_xs_5306_ = v___x_5327_;
goto _start;
}
}
else
{
lean_object* v___x_5329_; lean_object* v___y_5331_; lean_object* v___y_5332_; lean_object* v___y_5333_; lean_object* v_lower_5341_; lean_object* v_upper_5342_; uint8_t v___x_5350_; 
v___x_5329_ = lean_array_get_size(v_varyingArgs_5303_);
v___x_5350_ = lean_nat_dec_lt(v_j_5305_, v___x_5329_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; uint8_t v___x_5352_; 
lean_dec_ref(v_varyingArgs_5303_);
v___x_5351_ = lean_unsigned_to_nat(0u);
v___x_5352_ = lean_nat_dec_le(v_i_5304_, v___x_5351_);
if (v___x_5352_ == 0)
{
lean_inc(v_i_5304_);
v_lower_5341_ = v_i_5304_;
v_upper_5342_ = v___x_5313_;
goto v___jp_5340_;
}
else
{
v_lower_5341_ = v___x_5351_;
v_upper_5342_ = v___x_5313_;
goto v___jp_5340_;
}
}
else
{
lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; 
v___x_5353_ = lean_unsigned_to_nat(1u);
v___x_5354_ = lean_nat_add(v_i_5304_, v___x_5353_);
lean_dec(v_i_5304_);
v___x_5355_ = lean_nat_add(v_j_5305_, v___x_5353_);
v___x_5356_ = lean_array_fget_borrowed(v_varyingArgs_5303_, v_j_5305_);
lean_dec(v_j_5305_);
lean_inc(v___x_5356_);
v___x_5357_ = lean_array_push(v_xs_5306_, v___x_5356_);
v_i_5304_ = v___x_5354_;
v_j_5305_ = v___x_5355_;
v_xs_5306_ = v___x_5357_;
goto _start;
}
v___jp_5330_:
{
uint8_t v___x_5334_; 
v___x_5334_ = lean_nat_dec_lt(v___y_5331_, v___y_5333_);
if (v___x_5334_ == 0)
{
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec(v_j_5305_);
lean_dec(v_i_5304_);
return v_xs_5306_;
}
else
{
size_t v___x_5335_; size_t v___x_5336_; uint8_t v___x_5337_; 
v___x_5335_ = lean_usize_of_nat(v___y_5331_);
lean_dec(v___y_5331_);
v___x_5336_ = lean_usize_of_nat(v___y_5333_);
lean_dec(v___y_5333_);
v___x_5337_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5305_, v___x_5329_, v_i_5304_, v___x_5313_, v___y_5332_, v___x_5335_, v___x_5336_);
lean_dec_ref(v___y_5332_);
lean_dec(v_i_5304_);
lean_dec(v_j_5305_);
if (v___x_5337_ == 0)
{
return v_xs_5306_;
}
else
{
lean_object* v___x_5338_; lean_object* v___x_5339_; 
lean_dec_ref(v_xs_5306_);
v___x_5338_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5339_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5338_);
return v___x_5339_;
}
}
}
v___jp_5340_:
{
lean_object* v___x_5343_; lean_object* v_array_5344_; lean_object* v_start_5345_; lean_object* v_stop_5346_; uint8_t v___x_5347_; 
v___x_5343_ = l_Array_toSubarray___redArg(v_perm_5301_, v_lower_5341_, v_upper_5342_);
v_array_5344_ = lean_ctor_get(v___x_5343_, 0);
lean_inc_ref(v_array_5344_);
v_start_5345_ = lean_ctor_get(v___x_5343_, 1);
lean_inc(v_start_5345_);
v_stop_5346_ = lean_ctor_get(v___x_5343_, 2);
lean_inc(v_stop_5346_);
lean_dec_ref(v___x_5343_);
v___x_5347_ = lean_nat_dec_lt(v_start_5345_, v_stop_5346_);
if (v___x_5347_ == 0)
{
lean_dec(v_stop_5346_);
lean_dec(v_start_5345_);
lean_dec_ref(v_array_5344_);
lean_dec(v_j_5305_);
lean_dec(v_i_5304_);
return v_xs_5306_;
}
else
{
lean_object* v___x_5348_; uint8_t v___x_5349_; 
v___x_5348_ = lean_array_get_size(v_array_5344_);
v___x_5349_ = lean_nat_dec_le(v_stop_5346_, v___x_5348_);
if (v___x_5349_ == 0)
{
lean_dec(v_stop_5346_);
v___y_5331_ = v_start_5345_;
v___y_5332_ = v_array_5344_;
v___y_5333_ = v___x_5348_;
goto v___jp_5330_;
}
else
{
v___y_5331_ = v_start_5345_;
v___y_5332_ = v_array_5344_;
v___y_5333_ = v_stop_5346_;
goto v___jp_5330_;
}
}
}
}
}
v___jp_5307_:
{
lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; 
v___x_5310_ = l_Array_toSubarray___redArg(v_varyingArgs_5303_, v_lower_5308_, v_upper_5309_);
v___x_5311_ = l_Subarray_copy___redArg(v___x_5310_);
v___x_5312_ = l_Array_append___redArg(v_xs_5306_, v___x_5311_);
lean_dec_ref(v___x_5311_);
return v___x_5312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5359_, lean_object* v_fixedArgs_5360_, lean_object* v_varyingArgs_5361_, lean_object* v_i_5362_, lean_object* v_j_5363_, lean_object* v_xs_5364_){
_start:
{
lean_object* v_res_5365_; 
v_res_5365_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5359_, v_fixedArgs_5360_, v_varyingArgs_5361_, v_i_5362_, v_j_5363_, v_xs_5364_);
lean_dec_ref(v_fixedArgs_5360_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5366_, lean_object* v_perm_5367_, lean_object* v_fixedArgs_5368_, lean_object* v_varyingArgs_5369_, lean_object* v_i_5370_, lean_object* v_j_5371_, lean_object* v_xs_5372_){
_start:
{
lean_object* v___x_5373_; 
v___x_5373_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5367_, v_fixedArgs_5368_, v_varyingArgs_5369_, v_i_5370_, v_j_5371_, v_xs_5372_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5374_, lean_object* v_perm_5375_, lean_object* v_fixedArgs_5376_, lean_object* v_varyingArgs_5377_, lean_object* v_i_5378_, lean_object* v_j_5379_, lean_object* v_xs_5380_){
_start:
{
lean_object* v_res_5381_; 
v_res_5381_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5374_, v_perm_5375_, v_fixedArgs_5376_, v_varyingArgs_5377_, v_i_5378_, v_j_5379_, v_xs_5380_);
lean_dec_ref(v_fixedArgs_5376_);
return v_res_5381_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
v___x_5384_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5385_ = lean_unsigned_to_nat(2u);
v___x_5386_ = lean_unsigned_to_nat(416u);
v___x_5387_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5388_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5389_ = l_mkPanicMessageWithDecl(v___x_5388_, v___x_5387_, v___x_5386_, v___x_5385_, v___x_5384_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5390_, lean_object* v_fixedArgs_5391_, lean_object* v_varyingArgs_5392_){
_start:
{
lean_object* v___x_5393_; lean_object* v___x_5394_; uint8_t v___x_5395_; 
v___x_5393_ = lean_array_get_size(v_fixedArgs_5391_);
v___x_5394_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5390_);
v___x_5395_ = lean_nat_dec_eq(v___x_5393_, v___x_5394_);
lean_dec(v___x_5394_);
if (v___x_5395_ == 0)
{
lean_object* v___x_5396_; lean_object* v___x_5397_; 
lean_dec_ref(v_varyingArgs_5392_);
lean_dec_ref(v_perm_5390_);
v___x_5396_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5397_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5396_);
return v___x_5397_;
}
else
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5398_ = lean_unsigned_to_nat(0u);
v___x_5399_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5400_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5390_, v_fixedArgs_5391_, v_varyingArgs_5392_, v___x_5398_, v___x_5398_, v___x_5399_);
return v___x_5400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5401_, lean_object* v_fixedArgs_5402_, lean_object* v_varyingArgs_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5401_, v_fixedArgs_5402_, v_varyingArgs_5403_);
lean_dec_ref(v_fixedArgs_5402_);
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5405_, lean_object* v_perm_5406_, lean_object* v_fixedArgs_5407_, lean_object* v_varyingArgs_5408_){
_start:
{
lean_object* v___x_5409_; 
v___x_5409_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5406_, v_fixedArgs_5407_, v_varyingArgs_5408_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5410_, lean_object* v_perm_5411_, lean_object* v_fixedArgs_5412_, lean_object* v_varyingArgs_5413_){
_start:
{
lean_object* v_res_5414_; 
v_res_5414_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5410_, v_perm_5411_, v_fixedArgs_5412_, v_varyingArgs_5413_);
lean_dec_ref(v_fixedArgs_5412_);
return v_res_5414_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5415_, lean_object* v_x_5416_){
_start:
{
if (lean_obj_tag(v_x_5415_) == 0)
{
if (lean_obj_tag(v_x_5416_) == 0)
{
uint8_t v___x_5417_; 
v___x_5417_ = 1;
return v___x_5417_;
}
else
{
uint8_t v___x_5418_; 
v___x_5418_ = 0;
return v___x_5418_;
}
}
else
{
if (lean_obj_tag(v_x_5416_) == 0)
{
uint8_t v___x_5419_; 
v___x_5419_ = 0;
return v___x_5419_;
}
else
{
lean_object* v_val_5420_; lean_object* v_val_5421_; uint8_t v___x_5422_; 
v_val_5420_ = lean_ctor_get(v_x_5415_, 0);
v_val_5421_ = lean_ctor_get(v_x_5416_, 0);
v___x_5422_ = lean_nat_dec_eq(v_val_5420_, v_val_5421_);
return v___x_5422_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5415_ = stack[0].m_obj;
lean_object* v_x_5416_ = stack[1].m_obj;
uint8_t v_res_5423_;
v_res_5423_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5415_, v_x_5416_);
stack->m_num = v_res_5423_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5424_, lean_object* v_x_5425_){
_start:
{
uint8_t v_res_5426_; lean_object* v_r_5427_; 
v_res_5426_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5424_, v_x_5425_);
lean_dec(v_x_5425_);
lean_dec(v_x_5424_);
v_r_5427_ = lean_box(v_res_5426_);
return v_r_5427_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5428_, lean_object* v_ys_5429_, lean_object* v_x_5430_){
_start:
{
lean_object* v_zero_5431_; uint8_t v_isZero_5432_; 
v_zero_5431_ = lean_unsigned_to_nat(0u);
v_isZero_5432_ = lean_nat_dec_eq(v_x_5430_, v_zero_5431_);
if (v_isZero_5432_ == 1)
{
lean_dec(v_x_5430_);
return v_isZero_5432_;
}
else
{
lean_object* v_one_5433_; lean_object* v_n_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; uint8_t v___x_5437_; 
v_one_5433_ = lean_unsigned_to_nat(1u);
v_n_5434_ = lean_nat_sub(v_x_5430_, v_one_5433_);
lean_dec(v_x_5430_);
v___x_5435_ = lean_array_fget_borrowed(v_xs_5428_, v_n_5434_);
v___x_5436_ = lean_array_fget_borrowed(v_ys_5429_, v_n_5434_);
v___x_5437_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5435_, v___x_5436_);
if (v___x_5437_ == 0)
{
lean_dec(v_n_5434_);
return v___x_5437_;
}
else
{
v_x_5430_ = v_n_5434_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_5428_ = stack[0].m_obj;
lean_object* v_ys_5429_ = stack[1].m_obj;
lean_object* v_x_5430_ = stack[2].m_obj;
uint8_t v_res_5439_;
v_res_5439_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5428_, v_ys_5429_, v_x_5430_);
stack->m_num = v_res_5439_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5440_, lean_object* v_ys_5441_, lean_object* v_x_5442_){
_start:
{
uint8_t v_res_5443_; lean_object* v_r_5444_; 
v_res_5443_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5440_, v_ys_5441_, v_x_5442_);
lean_dec_ref(v_ys_5441_);
lean_dec_ref(v_xs_5440_);
v_r_5444_ = lean_box(v_res_5443_);
return v_r_5444_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5445_, size_t v_i_5446_, lean_object* v_bs_5447_){
_start:
{
uint8_t v___x_5448_; 
v___x_5448_ = lean_usize_dec_lt(v_i_5446_, v_sz_5445_);
if (v___x_5448_ == 0)
{
return v_bs_5447_;
}
else
{
lean_object* v_v_5449_; lean_object* v___x_5450_; lean_object* v_bs_x27_5451_; lean_object* v___x_5452_; size_t v___x_5453_; size_t v___x_5454_; lean_object* v___x_5455_; 
v_v_5449_ = lean_array_uget(v_bs_5447_, v_i_5446_);
v___x_5450_ = lean_unsigned_to_nat(0u);
v_bs_x27_5451_ = lean_array_uset(v_bs_5447_, v_i_5446_, v___x_5450_);
v___x_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5452_, 0, v_v_5449_);
v___x_5453_ = ((size_t)1ULL);
v___x_5454_ = lean_usize_add(v_i_5446_, v___x_5453_);
v___x_5455_ = lean_array_uset(v_bs_x27_5451_, v_i_5446_, v___x_5452_);
v_i_5446_ = v___x_5454_;
v_bs_5447_ = v___x_5455_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_5445_ = stack[0].m_num;
size_t v_i_5446_ = stack[1].m_num;
lean_object* v_bs_5447_ = stack[2].m_obj;
lean_object* v_res_5457_;
v_res_5457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5445_, v_i_5446_, v_bs_5447_);
stack->m_obj
 = v_res_5457_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5458_, lean_object* v_i_5459_, lean_object* v_bs_5460_){
_start:
{
size_t v_sz_boxed_5461_; size_t v_i_boxed_5462_; lean_object* v_res_5463_; 
v_sz_boxed_5461_ = lean_unbox_usize(v_sz_5458_);
lean_dec(v_sz_5458_);
v_i_boxed_5462_ = lean_unbox_usize(v_i_5459_);
lean_dec(v_i_5459_);
v_res_5463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5461_, v_i_boxed_5462_, v_bs_5460_);
return v_res_5463_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5464_, lean_object* v_as_5465_, size_t v_i_5466_, size_t v_stop_5467_){
_start:
{
uint8_t v___x_5468_; 
v___x_5468_ = lean_usize_dec_eq(v_i_5466_, v_stop_5467_);
if (v___x_5468_ == 0)
{
lean_object* v_numFixed_5469_; uint8_t v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; size_t v_sz_5473_; size_t v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; uint8_t v___x_5482_; 
v_numFixed_5469_ = lean_ctor_get(v_fixedParamPerms_5464_, 0);
v___x_5470_ = 1;
v___x_5471_ = lean_array_uget_borrowed(v_as_5465_, v_i_5466_);
lean_inc(v_numFixed_5469_);
v___x_5472_ = l_Array_range(v_numFixed_5469_);
v_sz_5473_ = lean_array_size(v___x_5472_);
v___x_5474_ = ((size_t)0ULL);
v___x_5475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5473_, v___x_5474_, v___x_5472_);
v___x_5476_ = lean_array_get_size(v___x_5471_);
v___x_5477_ = lean_nat_sub(v___x_5476_, v_numFixed_5469_);
v___x_5478_ = lean_box(0);
v___x_5479_ = lean_mk_array(v___x_5477_, v___x_5478_);
v___x_5480_ = l_Array_append___redArg(v___x_5475_, v___x_5479_);
lean_dec_ref(v___x_5479_);
v___x_5481_ = lean_array_get_size(v___x_5480_);
v___x_5482_ = lean_nat_dec_eq(v___x_5476_, v___x_5481_);
if (v___x_5482_ == 0)
{
lean_dec_ref(v___x_5480_);
lean_dec_ref(v_fixedParamPerms_5464_);
return v___x_5470_;
}
else
{
uint8_t v___x_5483_; 
v___x_5483_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5471_, v___x_5480_, v___x_5476_);
lean_dec_ref(v___x_5480_);
if (v___x_5483_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5464_);
return v___x_5470_;
}
else
{
size_t v___x_5484_; size_t v___x_5485_; 
v___x_5484_ = ((size_t)1ULL);
v___x_5485_ = lean_usize_add(v_i_5466_, v___x_5484_);
v_i_5466_ = v___x_5485_;
goto _start;
}
}
}
else
{
uint8_t v___x_5487_; 
lean_dec_ref(v_fixedParamPerms_5464_);
v___x_5487_ = 0;
return v___x_5487_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_5464_ = stack[0].m_obj;
lean_object* v_as_5465_ = stack[1].m_obj;
size_t v_i_5466_ = stack[2].m_num;
size_t v_stop_5467_ = stack[3].m_num;
uint8_t v_res_5488_;
v_res_5488_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5464_, v_as_5465_, v_i_5466_, v_stop_5467_);
stack->m_num = v_res_5488_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5489_, lean_object* v_as_5490_, lean_object* v_i_5491_, lean_object* v_stop_5492_){
_start:
{
size_t v_i_boxed_5493_; size_t v_stop_boxed_5494_; uint8_t v_res_5495_; lean_object* v_r_5496_; 
v_i_boxed_5493_ = lean_unbox_usize(v_i_5491_);
lean_dec(v_i_5491_);
v_stop_boxed_5494_ = lean_unbox_usize(v_stop_5492_);
lean_dec(v_stop_5492_);
v_res_5495_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5489_, v_as_5490_, v_i_boxed_5493_, v_stop_boxed_5494_);
lean_dec_ref(v_as_5490_);
v_r_5496_ = lean_box(v_res_5495_);
return v_r_5496_;
}
}
uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5497_){
_start:
{
lean_object* v_perms_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; uint8_t v___x_5501_; 
v_perms_5498_ = lean_ctor_get(v_fixedParamPerms_5497_, 1);
lean_inc_ref(v_perms_5498_);
v___x_5499_ = lean_unsigned_to_nat(0u);
v___x_5500_ = lean_array_get_size(v_perms_5498_);
v___x_5501_ = lean_nat_dec_lt(v___x_5499_, v___x_5500_);
if (v___x_5501_ == 0)
{
uint8_t v___x_5502_; 
lean_dec_ref(v_perms_5498_);
lean_dec_ref(v_fixedParamPerms_5497_);
v___x_5502_ = 1;
return v___x_5502_;
}
else
{
if (v___x_5501_ == 0)
{
lean_dec_ref(v_perms_5498_);
lean_dec_ref(v_fixedParamPerms_5497_);
return v___x_5501_;
}
else
{
size_t v___x_5503_; size_t v___x_5504_; uint8_t v___x_5505_; 
v___x_5503_ = ((size_t)0ULL);
v___x_5504_ = lean_usize_of_nat(v___x_5500_);
v___x_5505_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5497_, v_perms_5498_, v___x_5503_, v___x_5504_);
lean_dec_ref(v_perms_5498_);
if (v___x_5505_ == 0)
{
return v___x_5501_;
}
else
{
uint8_t v___x_5506_; 
v___x_5506_ = 0;
return v___x_5506_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_FixedParamPerms_fixedArePrefix_0interp(lean_interpreter_value* stack)
{
lean_object* v_fixedParamPerms_5497_ = stack[0].m_obj;
uint8_t v_res_5507_;
v_res_5507_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5497_);
stack->m_num = v_res_5507_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5508_){
_start:
{
uint8_t v_res_5509_; lean_object* v_r_5510_; 
v_res_5509_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5508_);
v_r_5510_ = lean_box(v_res_5509_);
return v_r_5510_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5511_, lean_object* v_ys_5512_, lean_object* v_hsz_5513_, lean_object* v_x_5514_, lean_object* v_x_5515_){
_start:
{
uint8_t v___x_5516_; 
v___x_5516_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5511_, v_ys_5512_, v_x_5514_);
return v___x_5516_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_5511_ = stack[0].m_obj;
lean_object* v_ys_5512_ = stack[1].m_obj;
lean_object* v_x_5514_ = stack[3].m_obj;
uint8_t v_res_5517_;
v_res_5517_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5511_, v_ys_5512_, lean_box(0), v_x_5514_, lean_box(0));
stack->m_num = v_res_5517_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5518_, lean_object* v_ys_5519_, lean_object* v_hsz_5520_, lean_object* v_x_5521_, lean_object* v_x_5522_){
_start:
{
uint8_t v_res_5523_; lean_object* v_r_5524_; 
v_res_5523_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5518_, v_ys_5519_, v_hsz_5520_, v_x_5521_, v_x_5522_);
lean_dec_ref(v_ys_5519_);
lean_dec_ref(v_xs_5518_);
v_r_5524_ = lean_box(v_res_5523_);
return v_r_5524_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5525_; lean_object* v___x_5526_; 
v___x_5525_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5526_, 0, v___x_5525_);
lean_ctor_set(v___x_5526_, 1, v___x_5525_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5527_){
_start:
{
lean_object* v___f_5528_; lean_object* v___f_5529_; lean_object* v___f_5530_; lean_object* v___f_5531_; lean_object* v___f_5532_; lean_object* v___f_5533_; lean_object* v___f_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; 
v___f_5528_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5529_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5530_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5531_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5532_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5533_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5534_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5535_, 0, v___f_5528_);
lean_ctor_set(v___x_5535_, 1, v___f_5529_);
v___x_5536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5536_, 0, v___x_5535_);
lean_ctor_set(v___x_5536_, 1, v___f_5530_);
lean_ctor_set(v___x_5536_, 2, v___f_5531_);
lean_ctor_set(v___x_5536_, 3, v___f_5532_);
lean_ctor_set(v___x_5536_, 4, v___f_5533_);
v___x_5537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5536_);
lean_ctor_set(v___x_5537_, 1, v___f_5534_);
v___x_5538_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5539_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5540_, 0, v___x_5538_);
lean_ctor_set(v___x_5540_, 1, v___x_5539_);
v___x_5541_ = l_instInhabitedOfMonad___redArg(v___x_5537_, v___x_5540_);
v___x_5542_ = lean_panic_fn_borrowed(v___x_5541_, v_msg_5527_);
lean_dec(v___x_5541_);
return v___x_5542_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5543_; lean_object* v___x_5544_; 
v___x_5543_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5543_);
return v___x_5544_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5545_){
_start:
{
lean_object* v___f_5546_; lean_object* v___f_5547_; lean_object* v___f_5548_; lean_object* v___f_5549_; lean_object* v___f_5550_; lean_object* v___f_5551_; lean_object* v___f_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___f_5546_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5547_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5548_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5549_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5550_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5551_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5552_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5553_, 0, v___f_5546_);
lean_ctor_set(v___x_5553_, 1, v___f_5547_);
v___x_5554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5554_, 0, v___x_5553_);
lean_ctor_set(v___x_5554_, 1, v___f_5548_);
lean_ctor_set(v___x_5554_, 2, v___f_5549_);
lean_ctor_set(v___x_5554_, 3, v___f_5550_);
lean_ctor_set(v___x_5554_, 4, v___f_5551_);
v___x_5555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5554_);
lean_ctor_set(v___x_5555_, 1, v___f_5552_);
v___x_5556_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5557_ = l_instInhabitedOfMonad___redArg(v___x_5555_, v___x_5556_);
v___x_5558_ = lean_panic_fn_borrowed(v___x_5557_, v_msg_5545_);
lean_dec(v___x_5557_);
return v___x_5558_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5559_, uint8_t v___x_5560_, lean_object* v___x_5561_, lean_object* v___x_5562_, lean_object* v_as_5563_, size_t v_sz_5564_, size_t v_i_5565_, lean_object* v_b_5566_){
_start:
{
lean_object* v_a_5568_; uint8_t v___x_5572_; 
v___x_5572_ = lean_usize_dec_lt(v_i_5565_, v_sz_5564_);
if (v___x_5572_ == 0)
{
return v_b_5566_;
}
else
{
lean_object* v_fst_5573_; lean_object* v_snd_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5596_; 
v_fst_5573_ = lean_ctor_get(v_b_5566_, 0);
v_snd_5574_ = lean_ctor_get(v_b_5566_, 1);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_b_5566_);
if (v_isSharedCheck_5596_ == 0)
{
v___x_5576_ = v_b_5566_;
v_isShared_5577_ = v_isSharedCheck_5596_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_snd_5574_);
lean_inc(v_fst_5573_);
lean_dec(v_b_5566_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5596_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5582_; lean_object* v_a_5583_; lean_object* v___x_5584_; 
v___x_5582_ = lean_box(0);
v_a_5583_ = lean_array_uget_borrowed(v_as_5563_, v_i_5565_);
v___x_5584_ = lean_array_get_borrowed(v___x_5582_, v___x_5559_, v_a_5583_);
if (lean_obj_tag(v___x_5584_) == 1)
{
lean_object* v_val_5585_; uint8_t v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; uint8_t v___x_5589_; 
v_val_5585_ = lean_ctor_get(v___x_5584_, 0);
v___x_5586_ = 0;
v___x_5587_ = lean_box(v___x_5586_);
v___x_5588_ = lean_array_get(v___x_5587_, v_fst_5573_, v_val_5585_);
lean_dec(v___x_5587_);
v___x_5589_ = lean_unbox(v___x_5588_);
lean_dec(v___x_5588_);
if (v___x_5589_ == 0)
{
if (v___x_5560_ == 0)
{
goto v___jp_5578_;
}
else
{
uint8_t v_changed_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
lean_del_object(v___x_5576_);
lean_dec(v_snd_5574_);
v_changed_5590_ = lean_nat_dec_eq(v___x_5561_, v___x_5562_);
v___x_5591_ = lean_box(v_changed_5590_);
v___x_5592_ = lean_array_set(v_fst_5573_, v_val_5585_, v___x_5591_);
v___x_5593_ = lean_box(v_changed_5590_);
v___x_5594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5594_, 0, v___x_5592_);
lean_ctor_set(v___x_5594_, 1, v___x_5593_);
v_a_5568_ = v___x_5594_;
goto v___jp_5567_;
}
}
else
{
goto v___jp_5578_;
}
}
else
{
lean_object* v___x_5595_; 
lean_del_object(v___x_5576_);
v___x_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5595_, 0, v_fst_5573_);
lean_ctor_set(v___x_5595_, 1, v_snd_5574_);
v_a_5568_ = v___x_5595_;
goto v___jp_5567_;
}
v___jp_5578_:
{
lean_object* v___x_5580_; 
if (v_isShared_5577_ == 0)
{
v___x_5580_ = v___x_5576_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_fst_5573_);
lean_ctor_set(v_reuseFailAlloc_5581_, 1, v_snd_5574_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
v_a_5568_ = v___x_5580_;
goto v___jp_5567_;
}
}
}
}
v___jp_5567_:
{
size_t v___x_5569_; size_t v___x_5570_; 
v___x_5569_ = ((size_t)1ULL);
v___x_5570_ = lean_usize_add(v_i_5565_, v___x_5569_);
v_i_5565_ = v___x_5570_;
v_b_5566_ = v_a_5568_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5559_ = stack[0].m_obj;
uint8_t v___x_5560_ = stack[1].m_num;
lean_object* v___x_5561_ = stack[2].m_obj;
lean_object* v___x_5562_ = stack[3].m_obj;
lean_object* v_as_5563_ = stack[4].m_obj;
size_t v_sz_5564_ = stack[5].m_num;
size_t v_i_5565_ = stack[6].m_num;
lean_object* v_b_5566_ = stack[7].m_obj;
lean_object* v_res_5597_;
v_res_5597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5559_, v___x_5560_, v___x_5561_, v___x_5562_, v_as_5563_, v_sz_5564_, v_i_5565_, v_b_5566_);
stack->m_obj
 = v_res_5597_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5598_, lean_object* v___x_5599_, lean_object* v___x_5600_, lean_object* v___x_5601_, lean_object* v_as_5602_, lean_object* v_sz_5603_, lean_object* v_i_5604_, lean_object* v_b_5605_){
_start:
{
uint8_t v___x_7038__boxed_5606_; size_t v_sz_boxed_5607_; size_t v_i_boxed_5608_; lean_object* v_res_5609_; 
v___x_7038__boxed_5606_ = lean_unbox(v___x_5599_);
v_sz_boxed_5607_ = lean_unbox_usize(v_sz_5603_);
lean_dec(v_sz_5603_);
v_i_boxed_5608_ = lean_unbox_usize(v_i_5604_);
lean_dec(v_i_5604_);
v_res_5609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5598_, v___x_7038__boxed_5606_, v___x_5600_, v___x_5601_, v_as_5602_, v_sz_boxed_5607_, v_i_boxed_5608_, v_b_5605_);
lean_dec_ref(v_as_5602_);
lean_dec(v___x_5601_);
lean_dec(v___x_5600_);
lean_dec_ref(v___x_5598_);
return v_res_5609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object* v_upperBound_5610_, lean_object* v___x_5611_, lean_object* v_fixedParamPerms_5612_, lean_object* v_next_5613_, lean_object* v___x_5614_, lean_object* v___x_5615_, lean_object* v_a_5616_, lean_object* v_b_5617_){
_start:
{
lean_object* v_a_5619_; uint8_t v___x_5623_; 
v___x_5623_ = lean_nat_dec_lt(v_a_5616_, v_upperBound_5610_);
if (v___x_5623_ == 0)
{
lean_dec(v_a_5616_);
return v_b_5617_;
}
else
{
lean_object* v_fst_5624_; lean_object* v_snd_5625_; lean_object* v___x_5627_; uint8_t v_isShared_5628_; uint8_t v_isSharedCheck_5661_; 
v_fst_5624_ = lean_ctor_get(v_b_5617_, 0);
v_snd_5625_ = lean_ctor_get(v_b_5617_, 1);
v_isSharedCheck_5661_ = !lean_is_exclusive(v_b_5617_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5627_ = v_b_5617_;
v_isShared_5628_ = v_isSharedCheck_5661_;
goto v_resetjp_5626_;
}
else
{
lean_inc(v_snd_5625_);
lean_inc(v_fst_5624_);
lean_dec(v_b_5617_);
v___x_5627_ = lean_box(0);
v_isShared_5628_ = v_isSharedCheck_5661_;
goto v_resetjp_5626_;
}
v_resetjp_5626_:
{
lean_object* v___x_5629_; 
v___x_5629_ = lean_array_fget_borrowed(v___x_5611_, v_a_5616_);
if (lean_obj_tag(v___x_5629_) == 1)
{
lean_object* v_val_5630_; uint8_t v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; uint8_t v___x_5634_; 
v_val_5630_ = lean_ctor_get(v___x_5629_, 0);
v___x_5631_ = 0;
v___x_5632_ = lean_box(v___x_5631_);
v___x_5633_ = lean_array_get(v___x_5632_, v_fst_5624_, v_val_5630_);
lean_dec(v___x_5632_);
v___x_5634_ = lean_unbox(v___x_5633_);
if (v___x_5634_ == 0)
{
lean_object* v___x_5636_; 
lean_dec(v___x_5633_);
if (v_isShared_5628_ == 0)
{
v___x_5636_ = v___x_5627_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_fst_5624_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v_snd_5625_);
v___x_5636_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
v_a_5619_ = v___x_5636_;
goto v___jp_5618_;
}
}
else
{
lean_object* v_revDeps_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5643_; 
v_revDeps_5638_ = lean_ctor_get(v_fixedParamPerms_5612_, 2);
v___x_5639_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5640_ = lean_array_get_borrowed(v___x_5639_, v_revDeps_5638_, v_next_5613_);
v___x_5641_ = lean_array_get_borrowed(v___x_5639_, v___x_5640_, v_a_5616_);
if (v_isShared_5628_ == 0)
{
v___x_5643_ = v___x_5627_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_fst_5624_);
lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_snd_5625_);
v___x_5643_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
size_t v_sz_5644_; size_t v___x_5645_; uint8_t v___x_5646_; lean_object* v___x_5647_; lean_object* v_fst_5648_; lean_object* v_snd_5649_; lean_object* v___x_5651_; uint8_t v_isShared_5652_; uint8_t v_isSharedCheck_5656_; 
v_sz_5644_ = lean_array_size(v___x_5641_);
v___x_5645_ = ((size_t)0ULL);
v___x_5646_ = lean_unbox(v___x_5633_);
lean_dec(v___x_5633_);
v___x_5647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5611_, v___x_5646_, v___x_5614_, v___x_5615_, v___x_5641_, v_sz_5644_, v___x_5645_, v___x_5643_);
v_fst_5648_ = lean_ctor_get(v___x_5647_, 0);
v_snd_5649_ = lean_ctor_get(v___x_5647_, 1);
v_isSharedCheck_5656_ = !lean_is_exclusive(v___x_5647_);
if (v_isSharedCheck_5656_ == 0)
{
v___x_5651_ = v___x_5647_;
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
else
{
lean_inc(v_snd_5649_);
lean_inc(v_fst_5648_);
lean_dec(v___x_5647_);
v___x_5651_ = lean_box(0);
v_isShared_5652_ = v_isSharedCheck_5656_;
goto v_resetjp_5650_;
}
v_resetjp_5650_:
{
lean_object* v___x_5654_; 
if (v_isShared_5652_ == 0)
{
v___x_5654_ = v___x_5651_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_fst_5648_);
lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_snd_5649_);
v___x_5654_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
v_a_5619_ = v___x_5654_;
goto v___jp_5618_;
}
}
}
}
}
else
{
lean_object* v___x_5659_; 
if (v_isShared_5628_ == 0)
{
v___x_5659_ = v___x_5627_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_fst_5624_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v_snd_5625_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
v_a_5619_ = v___x_5659_;
goto v___jp_5618_;
}
}
}
}
v___jp_5618_:
{
lean_object* v___x_5620_; lean_object* v___x_5621_; 
v___x_5620_ = lean_unsigned_to_nat(1u);
v___x_5621_ = lean_nat_add(v_a_5616_, v___x_5620_);
lean_dec(v_a_5616_);
v_a_5616_ = v___x_5621_;
v_b_5617_ = v_a_5619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object* v_upperBound_5662_, lean_object* v___x_5663_, lean_object* v_fixedParamPerms_5664_, lean_object* v_next_5665_, lean_object* v___x_5666_, lean_object* v___x_5667_, lean_object* v_a_5668_, lean_object* v_b_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5662_, v___x_5663_, v_fixedParamPerms_5664_, v_next_5665_, v___x_5666_, v___x_5667_, v_a_5668_, v_b_5669_);
lean_dec(v___x_5667_);
lean_dec(v___x_5666_);
lean_dec(v_next_5665_);
lean_dec_ref(v_fixedParamPerms_5664_);
lean_dec_ref(v___x_5663_);
lean_dec(v_upperBound_5662_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5671_, lean_object* v___x_5672_, lean_object* v___x_5673_, lean_object* v___x_5674_, lean_object* v_fixedParamPerms_5675_, lean_object* v_next_5676_, lean_object* v_a_5677_, lean_object* v_b_5678_){
_start:
{
lean_object* v_a_5680_; uint8_t v___x_5684_; 
v___x_5684_ = lean_nat_dec_lt(v_a_5677_, v_upperBound_5671_);
if (v___x_5684_ == 0)
{
return v_b_5678_;
}
else
{
lean_object* v_fst_5685_; lean_object* v_snd_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5722_; 
v_fst_5685_ = lean_ctor_get(v_b_5678_, 0);
v_snd_5686_ = lean_ctor_get(v_b_5678_, 1);
v_isSharedCheck_5722_ = !lean_is_exclusive(v_b_5678_);
if (v_isSharedCheck_5722_ == 0)
{
v___x_5688_ = v_b_5678_;
v_isShared_5689_ = v_isSharedCheck_5722_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_snd_5686_);
lean_inc(v_fst_5685_);
lean_dec(v_b_5678_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5722_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5690_; 
v___x_5690_ = lean_array_fget_borrowed(v___x_5672_, v_a_5677_);
if (lean_obj_tag(v___x_5690_) == 1)
{
lean_object* v_val_5691_; uint8_t v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; uint8_t v___x_5695_; 
v_val_5691_ = lean_ctor_get(v___x_5690_, 0);
v___x_5692_ = 0;
v___x_5693_ = lean_box(v___x_5692_);
v___x_5694_ = lean_array_get(v___x_5693_, v_fst_5685_, v_val_5691_);
lean_dec(v___x_5693_);
v___x_5695_ = lean_unbox(v___x_5694_);
if (v___x_5695_ == 0)
{
lean_object* v___x_5697_; 
lean_dec(v___x_5694_);
if (v_isShared_5689_ == 0)
{
v___x_5697_ = v___x_5688_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_fst_5685_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v_snd_5686_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
v_a_5680_ = v___x_5697_;
goto v___jp_5679_;
}
}
else
{
lean_object* v_revDeps_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5704_; 
v_revDeps_5699_ = lean_ctor_get(v_fixedParamPerms_5675_, 2);
v___x_5700_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5701_ = lean_array_get_borrowed(v___x_5700_, v_revDeps_5699_, v_next_5676_);
v___x_5702_ = lean_array_get_borrowed(v___x_5700_, v___x_5701_, v_a_5677_);
if (v_isShared_5689_ == 0)
{
v___x_5704_ = v___x_5688_;
goto v_reusejp_5703_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_fst_5685_);
lean_ctor_set(v_reuseFailAlloc_5718_, 1, v_snd_5686_);
v___x_5704_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5703_;
}
v_reusejp_5703_:
{
size_t v_sz_5705_; size_t v___x_5706_; uint8_t v___x_5707_; lean_object* v___x_5708_; lean_object* v_fst_5709_; lean_object* v_snd_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5717_; 
v_sz_5705_ = lean_array_size(v___x_5702_);
v___x_5706_ = ((size_t)0ULL);
v___x_5707_ = lean_unbox(v___x_5694_);
lean_dec(v___x_5694_);
v___x_5708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5672_, v___x_5707_, v___x_5673_, v___x_5674_, v___x_5702_, v_sz_5705_, v___x_5706_, v___x_5704_);
v_fst_5709_ = lean_ctor_get(v___x_5708_, 0);
v_snd_5710_ = lean_ctor_get(v___x_5708_, 1);
v_isSharedCheck_5717_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5712_ = v___x_5708_;
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_snd_5710_);
lean_inc(v_fst_5709_);
lean_dec(v___x_5708_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v___x_5715_; 
if (v_isShared_5713_ == 0)
{
v___x_5715_ = v___x_5712_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_fst_5709_);
lean_ctor_set(v_reuseFailAlloc_5716_, 1, v_snd_5710_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
v_a_5680_ = v___x_5715_;
goto v___jp_5679_;
}
}
}
}
}
else
{
lean_object* v___x_5720_; 
if (v_isShared_5689_ == 0)
{
v___x_5720_ = v___x_5688_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_fst_5685_);
lean_ctor_set(v_reuseFailAlloc_5721_, 1, v_snd_5686_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
v_a_5680_ = v___x_5720_;
goto v___jp_5679_;
}
}
}
}
v___jp_5679_:
{
lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; 
v___x_5681_ = lean_unsigned_to_nat(1u);
v___x_5682_ = lean_nat_add(v_a_5677_, v___x_5681_);
v___x_5683_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5671_, v___x_5672_, v_fixedParamPerms_5675_, v_next_5676_, v___x_5673_, v___x_5674_, v___x_5682_, v_a_5680_);
return v___x_5683_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5723_, lean_object* v___x_5724_, lean_object* v___x_5725_, lean_object* v___x_5726_, lean_object* v_fixedParamPerms_5727_, lean_object* v_next_5728_, lean_object* v_a_5729_, lean_object* v_b_5730_){
_start:
{
lean_object* v_res_5731_; 
v_res_5731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5723_, v___x_5724_, v___x_5725_, v___x_5726_, v_fixedParamPerms_5727_, v_next_5728_, v_a_5729_, v_b_5730_);
lean_dec(v_a_5729_);
lean_dec(v_next_5728_);
lean_dec_ref(v_fixedParamPerms_5727_);
lean_dec(v___x_5726_);
lean_dec(v___x_5725_);
lean_dec_ref(v___x_5724_);
lean_dec(v_upperBound_5723_);
return v_res_5731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5732_, lean_object* v___x_5733_, lean_object* v___x_5734_, lean_object* v___x_5735_, lean_object* v_fixedParamPerms_5736_, lean_object* v_a_5737_, lean_object* v_b_5738_){
_start:
{
uint8_t v___x_5739_; 
v___x_5739_ = lean_nat_dec_lt(v_a_5737_, v_upperBound_5732_);
if (v___x_5739_ == 0)
{
lean_dec(v_a_5737_);
return v_b_5738_;
}
else
{
lean_object* v_fst_5740_; lean_object* v_snd_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5764_; 
v_fst_5740_ = lean_ctor_get(v_b_5738_, 0);
v_snd_5741_ = lean_ctor_get(v_b_5738_, 1);
v_isSharedCheck_5764_ = !lean_is_exclusive(v_b_5738_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5743_ = v_b_5738_;
v_isShared_5744_ = v_isSharedCheck_5764_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_snd_5741_);
lean_inc(v_fst_5740_);
lean_dec(v_b_5738_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5764_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5749_; 
v___x_5745_ = lean_array_fget_borrowed(v___x_5733_, v_a_5737_);
v___x_5746_ = lean_array_get_size(v___x_5745_);
v___x_5747_ = lean_unsigned_to_nat(0u);
if (v_isShared_5744_ == 0)
{
v___x_5749_ = v___x_5743_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_fst_5740_);
lean_ctor_set(v_reuseFailAlloc_5763_, 1, v_snd_5741_);
v___x_5749_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
lean_object* v___x_5750_; lean_object* v_fst_5751_; lean_object* v_snd_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5762_; 
v___x_5750_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5746_, v___x_5745_, v___x_5734_, v___x_5735_, v_fixedParamPerms_5736_, v_a_5737_, v___x_5747_, v___x_5749_);
v_fst_5751_ = lean_ctor_get(v___x_5750_, 0);
v_snd_5752_ = lean_ctor_get(v___x_5750_, 1);
v_isSharedCheck_5762_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5754_ = v___x_5750_;
v_isShared_5755_ = v_isSharedCheck_5762_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_snd_5752_);
lean_inc(v_fst_5751_);
lean_dec(v___x_5750_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5762_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v___x_5757_; 
if (v_isShared_5755_ == 0)
{
v___x_5757_ = v___x_5754_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v_fst_5751_);
lean_ctor_set(v_reuseFailAlloc_5761_, 1, v_snd_5752_);
v___x_5757_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
lean_object* v___x_5758_; lean_object* v___x_5759_; 
v___x_5758_ = lean_unsigned_to_nat(1u);
v___x_5759_ = lean_nat_add(v_a_5737_, v___x_5758_);
lean_dec(v_a_5737_);
v_a_5737_ = v___x_5759_;
v_b_5738_ = v___x_5757_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5765_, lean_object* v___x_5766_, lean_object* v___x_5767_, lean_object* v___x_5768_, lean_object* v_fixedParamPerms_5769_, lean_object* v_a_5770_, lean_object* v_b_5771_){
_start:
{
lean_object* v_res_5772_; 
v_res_5772_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5765_, v___x_5766_, v___x_5767_, v___x_5768_, v_fixedParamPerms_5769_, v_a_5770_, v_b_5771_);
lean_dec_ref(v_fixedParamPerms_5769_);
lean_dec(v___x_5768_);
lean_dec(v___x_5767_);
lean_dec_ref(v___x_5766_);
lean_dec(v_upperBound_5765_);
return v_res_5772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5773_, lean_object* v___x_5774_, lean_object* v___x_5775_, lean_object* v_fixedParamPerms_5776_, lean_object* v_a_5777_){
_start:
{
lean_object* v_snd_5778_; uint8_t v___x_5779_; 
v_snd_5778_ = lean_ctor_get(v_a_5777_, 1);
v___x_5779_ = lean_unbox(v_snd_5778_);
if (v___x_5779_ == 0)
{
lean_object* v_fst_5780_; lean_object* v___x_5782_; uint8_t v_isShared_5783_; uint8_t v_isSharedCheck_5787_; 
lean_inc(v_snd_5778_);
v_fst_5780_ = lean_ctor_get(v_a_5777_, 0);
v_isSharedCheck_5787_ = !lean_is_exclusive(v_a_5777_);
if (v_isSharedCheck_5787_ == 0)
{
lean_object* v_unused_5788_; 
v_unused_5788_ = lean_ctor_get(v_a_5777_, 1);
lean_dec(v_unused_5788_);
v___x_5782_ = v_a_5777_;
v_isShared_5783_ = v_isSharedCheck_5787_;
goto v_resetjp_5781_;
}
else
{
lean_inc(v_fst_5780_);
lean_dec(v_a_5777_);
v___x_5782_ = lean_box(0);
v_isShared_5783_ = v_isSharedCheck_5787_;
goto v_resetjp_5781_;
}
v_resetjp_5781_:
{
lean_object* v___x_5785_; 
if (v_isShared_5783_ == 0)
{
v___x_5785_ = v___x_5782_;
goto v_reusejp_5784_;
}
else
{
lean_object* v_reuseFailAlloc_5786_; 
v_reuseFailAlloc_5786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5786_, 0, v_fst_5780_);
lean_ctor_set(v_reuseFailAlloc_5786_, 1, v_snd_5778_);
v___x_5785_ = v_reuseFailAlloc_5786_;
goto v_reusejp_5784_;
}
v_reusejp_5784_:
{
return v___x_5785_;
}
}
}
else
{
lean_object* v_fst_5789_; lean_object* v___x_5791_; uint8_t v_isShared_5792_; uint8_t v_isSharedCheck_5810_; 
v_fst_5789_ = lean_ctor_get(v_a_5777_, 0);
v_isSharedCheck_5810_ = !lean_is_exclusive(v_a_5777_);
if (v_isSharedCheck_5810_ == 0)
{
lean_object* v_unused_5811_; 
v_unused_5811_ = lean_ctor_get(v_a_5777_, 1);
lean_dec(v_unused_5811_);
v___x_5791_ = v_a_5777_;
v_isShared_5792_ = v_isSharedCheck_5810_;
goto v_resetjp_5790_;
}
else
{
lean_inc(v_fst_5789_);
lean_dec(v_a_5777_);
v___x_5791_ = lean_box(0);
v_isShared_5792_ = v_isSharedCheck_5810_;
goto v_resetjp_5790_;
}
v_resetjp_5790_:
{
uint8_t v_changed_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5797_; 
v_changed_5793_ = 0;
v___x_5794_ = lean_unsigned_to_nat(0u);
v___x_5795_ = lean_box(v_changed_5793_);
if (v_isShared_5792_ == 0)
{
lean_ctor_set(v___x_5791_, 1, v___x_5795_);
v___x_5797_ = v___x_5791_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5809_; 
v_reuseFailAlloc_5809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5809_, 0, v_fst_5789_);
lean_ctor_set(v_reuseFailAlloc_5809_, 1, v___x_5795_);
v___x_5797_ = v_reuseFailAlloc_5809_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
lean_object* v___x_5798_; lean_object* v_fst_5799_; lean_object* v_snd_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5808_; 
v___x_5798_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5773_, v___x_5774_, v___x_5775_, v___x_5773_, v_fixedParamPerms_5776_, v___x_5794_, v___x_5797_);
v_fst_5799_ = lean_ctor_get(v___x_5798_, 0);
v_snd_5800_ = lean_ctor_get(v___x_5798_, 1);
v_isSharedCheck_5808_ = !lean_is_exclusive(v___x_5798_);
if (v_isSharedCheck_5808_ == 0)
{
v___x_5802_ = v___x_5798_;
v_isShared_5803_ = v_isSharedCheck_5808_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_snd_5800_);
lean_inc(v_fst_5799_);
lean_dec(v___x_5798_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5808_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
lean_object* v___x_5805_; 
if (v_isShared_5803_ == 0)
{
v___x_5805_ = v___x_5802_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v_fst_5799_);
lean_ctor_set(v_reuseFailAlloc_5807_, 1, v_snd_5800_);
v___x_5805_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
v_a_5777_ = v___x_5805_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5812_, lean_object* v___x_5813_, lean_object* v___x_5814_, lean_object* v_fixedParamPerms_5815_, lean_object* v_a_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5812_, v___x_5813_, v___x_5814_, v_fixedParamPerms_5815_, v_a_5816_);
lean_dec_ref(v_fixedParamPerms_5815_);
lean_dec(v___x_5814_);
lean_dec_ref(v___x_5813_);
lean_dec(v___x_5812_);
return v_res_5817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5818_, lean_object* v_a_5819_, lean_object* v_b_5820_){
_start:
{
lean_object* v_a_5822_; uint8_t v___x_5826_; 
v___x_5826_ = lean_nat_dec_lt(v_a_5819_, v_upperBound_5818_);
if (v___x_5826_ == 0)
{
lean_dec(v_a_5819_);
return v_b_5820_;
}
else
{
lean_object* v_snd_5827_; lean_object* v_snd_5828_; lean_object* v_snd_5829_; lean_object* v_snd_5830_; lean_object* v_fst_5831_; lean_object* v___x_5833_; uint8_t v_isShared_5834_; uint8_t v_isSharedCheck_5943_; 
v_snd_5827_ = lean_ctor_get(v_b_5820_, 1);
lean_inc(v_snd_5827_);
v_snd_5828_ = lean_ctor_get(v_snd_5827_, 1);
lean_inc(v_snd_5828_);
v_snd_5829_ = lean_ctor_get(v_snd_5828_, 1);
lean_inc(v_snd_5829_);
v_snd_5830_ = lean_ctor_get(v_snd_5829_, 1);
lean_inc(v_snd_5830_);
v_fst_5831_ = lean_ctor_get(v_b_5820_, 0);
v_isSharedCheck_5943_ = !lean_is_exclusive(v_b_5820_);
if (v_isSharedCheck_5943_ == 0)
{
lean_object* v_unused_5944_; 
v_unused_5944_ = lean_ctor_get(v_b_5820_, 1);
lean_dec(v_unused_5944_);
v___x_5833_ = v_b_5820_;
v_isShared_5834_ = v_isSharedCheck_5943_;
goto v_resetjp_5832_;
}
else
{
lean_inc(v_fst_5831_);
lean_dec(v_b_5820_);
v___x_5833_ = lean_box(0);
v_isShared_5834_ = v_isSharedCheck_5943_;
goto v_resetjp_5832_;
}
v_resetjp_5832_:
{
lean_object* v_fst_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5941_; 
v_fst_5835_ = lean_ctor_get(v_snd_5827_, 0);
v_isSharedCheck_5941_ = !lean_is_exclusive(v_snd_5827_);
if (v_isSharedCheck_5941_ == 0)
{
lean_object* v_unused_5942_; 
v_unused_5942_ = lean_ctor_get(v_snd_5827_, 1);
lean_dec(v_unused_5942_);
v___x_5837_ = v_snd_5827_;
v_isShared_5838_ = v_isSharedCheck_5941_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_fst_5835_);
lean_dec(v_snd_5827_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5941_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v_fst_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5939_; 
v_fst_5839_ = lean_ctor_get(v_snd_5828_, 0);
v_isSharedCheck_5939_ = !lean_is_exclusive(v_snd_5828_);
if (v_isSharedCheck_5939_ == 0)
{
lean_object* v_unused_5940_; 
v_unused_5940_ = lean_ctor_get(v_snd_5828_, 1);
lean_dec(v_unused_5940_);
v___x_5841_ = v_snd_5828_;
v_isShared_5842_ = v_isSharedCheck_5939_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_fst_5839_);
lean_dec(v_snd_5828_);
v___x_5841_ = lean_box(0);
v_isShared_5842_ = v_isSharedCheck_5939_;
goto v_resetjp_5840_;
}
v_resetjp_5840_:
{
lean_object* v_fst_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5937_; 
v_fst_5843_ = lean_ctor_get(v_snd_5829_, 0);
v_isSharedCheck_5937_ = !lean_is_exclusive(v_snd_5829_);
if (v_isSharedCheck_5937_ == 0)
{
lean_object* v_unused_5938_; 
v_unused_5938_ = lean_ctor_get(v_snd_5829_, 1);
lean_dec(v_unused_5938_);
v___x_5845_ = v_snd_5829_;
v_isShared_5846_ = v_isSharedCheck_5937_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_fst_5843_);
lean_dec(v_snd_5829_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5937_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v_array_5847_; lean_object* v_start_5848_; lean_object* v_stop_5849_; uint8_t v___x_5850_; 
v_array_5847_ = lean_ctor_get(v_snd_5830_, 0);
v_start_5848_ = lean_ctor_get(v_snd_5830_, 1);
v_stop_5849_ = lean_ctor_get(v_snd_5830_, 2);
v___x_5850_ = lean_nat_dec_lt(v_start_5848_, v_stop_5849_);
if (v___x_5850_ == 0)
{
lean_object* v___x_5852_; 
lean_dec(v_a_5819_);
if (v_isShared_5846_ == 0)
{
v___x_5852_ = v___x_5845_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_fst_5843_);
lean_ctor_set(v_reuseFailAlloc_5862_, 1, v_snd_5830_);
v___x_5852_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
lean_object* v___x_5854_; 
if (v_isShared_5842_ == 0)
{
lean_ctor_set(v___x_5841_, 1, v___x_5852_);
v___x_5854_ = v___x_5841_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_fst_5839_);
lean_ctor_set(v_reuseFailAlloc_5861_, 1, v___x_5852_);
v___x_5854_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
lean_object* v___x_5856_; 
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 1, v___x_5854_);
v___x_5856_ = v___x_5837_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_fst_5835_);
lean_ctor_set(v_reuseFailAlloc_5860_, 1, v___x_5854_);
v___x_5856_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
lean_object* v___x_5858_; 
if (v_isShared_5834_ == 0)
{
lean_ctor_set(v___x_5833_, 1, v___x_5856_);
v___x_5858_ = v___x_5833_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_fst_5831_);
lean_ctor_set(v_reuseFailAlloc_5859_, 1, v___x_5856_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
return v___x_5858_;
}
}
}
}
}
else
{
lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5933_; 
lean_inc(v_stop_5849_);
lean_inc(v_start_5848_);
lean_inc_ref(v_array_5847_);
v_isSharedCheck_5933_ = !lean_is_exclusive(v_snd_5830_);
if (v_isSharedCheck_5933_ == 0)
{
lean_object* v_unused_5934_; lean_object* v_unused_5935_; lean_object* v_unused_5936_; 
v_unused_5934_ = lean_ctor_get(v_snd_5830_, 2);
lean_dec(v_unused_5934_);
v_unused_5935_ = lean_ctor_get(v_snd_5830_, 1);
lean_dec(v_unused_5935_);
v_unused_5936_ = lean_ctor_get(v_snd_5830_, 0);
lean_dec(v_unused_5936_);
v___x_5864_ = v_snd_5830_;
v_isShared_5865_ = v_isSharedCheck_5933_;
goto v_resetjp_5863_;
}
else
{
lean_dec(v_snd_5830_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5933_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v_array_5866_; lean_object* v_start_5867_; lean_object* v_stop_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5873_; 
v_array_5866_ = lean_ctor_get(v_fst_5843_, 0);
v_start_5867_ = lean_ctor_get(v_fst_5843_, 1);
v_stop_5868_ = lean_ctor_get(v_fst_5843_, 2);
v___x_5869_ = lean_array_fget(v_array_5847_, v_start_5848_);
v___x_5870_ = lean_unsigned_to_nat(1u);
v___x_5871_ = lean_nat_add(v_start_5848_, v___x_5870_);
lean_dec(v_start_5848_);
if (v_isShared_5865_ == 0)
{
lean_ctor_set(v___x_5864_, 1, v___x_5871_);
v___x_5873_ = v___x_5864_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_array_5847_);
lean_ctor_set(v_reuseFailAlloc_5932_, 1, v___x_5871_);
lean_ctor_set(v_reuseFailAlloc_5932_, 2, v_stop_5849_);
v___x_5873_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
uint8_t v___x_5874_; 
v___x_5874_ = lean_nat_dec_lt(v_start_5867_, v_stop_5868_);
if (v___x_5874_ == 0)
{
lean_object* v___x_5876_; 
lean_dec(v___x_5869_);
lean_dec(v_a_5819_);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 1, v___x_5873_);
v___x_5876_ = v___x_5845_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_fst_5843_);
lean_ctor_set(v_reuseFailAlloc_5886_, 1, v___x_5873_);
v___x_5876_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
lean_object* v___x_5878_; 
if (v_isShared_5842_ == 0)
{
lean_ctor_set(v___x_5841_, 1, v___x_5876_);
v___x_5878_ = v___x_5841_;
goto v_reusejp_5877_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_fst_5839_);
lean_ctor_set(v_reuseFailAlloc_5885_, 1, v___x_5876_);
v___x_5878_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5877_;
}
v_reusejp_5877_:
{
lean_object* v___x_5880_; 
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 1, v___x_5878_);
v___x_5880_ = v___x_5837_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v_fst_5835_);
lean_ctor_set(v_reuseFailAlloc_5884_, 1, v___x_5878_);
v___x_5880_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
lean_object* v___x_5882_; 
if (v_isShared_5834_ == 0)
{
lean_ctor_set(v___x_5833_, 1, v___x_5880_);
v___x_5882_ = v___x_5833_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5883_; 
v_reuseFailAlloc_5883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_fst_5831_);
lean_ctor_set(v_reuseFailAlloc_5883_, 1, v___x_5880_);
v___x_5882_ = v_reuseFailAlloc_5883_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
return v___x_5882_;
}
}
}
}
}
else
{
lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5928_; 
lean_inc(v_stop_5868_);
lean_inc(v_start_5867_);
lean_inc_ref(v_array_5866_);
v_isSharedCheck_5928_ = !lean_is_exclusive(v_fst_5843_);
if (v_isSharedCheck_5928_ == 0)
{
lean_object* v_unused_5929_; lean_object* v_unused_5930_; lean_object* v_unused_5931_; 
v_unused_5929_ = lean_ctor_get(v_fst_5843_, 2);
lean_dec(v_unused_5929_);
v_unused_5930_ = lean_ctor_get(v_fst_5843_, 1);
lean_dec(v_unused_5930_);
v_unused_5931_ = lean_ctor_get(v_fst_5843_, 0);
lean_dec(v_unused_5931_);
v___x_5888_ = v_fst_5843_;
v_isShared_5889_ = v_isSharedCheck_5928_;
goto v_resetjp_5887_;
}
else
{
lean_dec(v_fst_5843_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5928_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5893_; 
v___x_5890_ = lean_array_fget(v_array_5866_, v_start_5867_);
v___x_5891_ = lean_nat_add(v_start_5867_, v___x_5870_);
lean_dec(v_start_5867_);
if (v_isShared_5889_ == 0)
{
lean_ctor_set(v___x_5888_, 1, v___x_5891_);
v___x_5893_ = v___x_5888_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5927_; 
v_reuseFailAlloc_5927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_array_5866_);
lean_ctor_set(v_reuseFailAlloc_5927_, 1, v___x_5891_);
lean_ctor_set(v_reuseFailAlloc_5927_, 2, v_stop_5868_);
v___x_5893_ = v_reuseFailAlloc_5927_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
uint8_t v___x_5894_; 
v___x_5894_ = lean_unbox(v___x_5890_);
lean_dec(v___x_5890_);
if (v___x_5894_ == 0)
{
lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5900_; 
v___x_5895_ = lean_array_get_size(v_fst_5839_);
v___x_5896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5895_);
v___x_5897_ = lean_array_push(v_fst_5831_, v___x_5896_);
v___x_5898_ = lean_array_push(v_fst_5839_, v___x_5869_);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 1, v___x_5873_);
lean_ctor_set(v___x_5845_, 0, v___x_5893_);
v___x_5900_ = v___x_5845_;
goto v_reusejp_5899_;
}
else
{
lean_object* v_reuseFailAlloc_5910_; 
v_reuseFailAlloc_5910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5910_, 0, v___x_5893_);
lean_ctor_set(v_reuseFailAlloc_5910_, 1, v___x_5873_);
v___x_5900_ = v_reuseFailAlloc_5910_;
goto v_reusejp_5899_;
}
v_reusejp_5899_:
{
lean_object* v___x_5902_; 
if (v_isShared_5842_ == 0)
{
lean_ctor_set(v___x_5841_, 1, v___x_5900_);
lean_ctor_set(v___x_5841_, 0, v___x_5898_);
v___x_5902_ = v___x_5841_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5909_; 
v_reuseFailAlloc_5909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5909_, 0, v___x_5898_);
lean_ctor_set(v_reuseFailAlloc_5909_, 1, v___x_5900_);
v___x_5902_ = v_reuseFailAlloc_5909_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
lean_object* v___x_5904_; 
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 1, v___x_5902_);
v___x_5904_ = v___x_5837_;
goto v_reusejp_5903_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_fst_5835_);
lean_ctor_set(v_reuseFailAlloc_5908_, 1, v___x_5902_);
v___x_5904_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5903_;
}
v_reusejp_5903_:
{
lean_object* v___x_5906_; 
if (v_isShared_5834_ == 0)
{
lean_ctor_set(v___x_5833_, 1, v___x_5904_);
lean_ctor_set(v___x_5833_, 0, v___x_5897_);
v___x_5906_ = v___x_5833_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5907_; 
v_reuseFailAlloc_5907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5907_, 0, v___x_5897_);
lean_ctor_set(v_reuseFailAlloc_5907_, 1, v___x_5904_);
v___x_5906_ = v_reuseFailAlloc_5907_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
v_a_5822_ = v___x_5906_;
goto v___jp_5821_;
}
}
}
}
}
else
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5916_; 
v___x_5911_ = lean_box(0);
v___x_5912_ = lean_array_push(v_fst_5831_, v___x_5911_);
v___x_5913_ = l_Lean_Expr_fvarId_x21(v___x_5869_);
lean_dec(v___x_5869_);
v___x_5914_ = lean_array_push(v_fst_5835_, v___x_5913_);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 1, v___x_5873_);
lean_ctor_set(v___x_5845_, 0, v___x_5893_);
v___x_5916_ = v___x_5845_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5926_; 
v_reuseFailAlloc_5926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5893_);
lean_ctor_set(v_reuseFailAlloc_5926_, 1, v___x_5873_);
v___x_5916_ = v_reuseFailAlloc_5926_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
lean_object* v___x_5918_; 
if (v_isShared_5842_ == 0)
{
lean_ctor_set(v___x_5841_, 1, v___x_5916_);
v___x_5918_ = v___x_5841_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5925_; 
v_reuseFailAlloc_5925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_fst_5839_);
lean_ctor_set(v_reuseFailAlloc_5925_, 1, v___x_5916_);
v___x_5918_ = v_reuseFailAlloc_5925_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
lean_object* v___x_5920_; 
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 1, v___x_5918_);
lean_ctor_set(v___x_5837_, 0, v___x_5914_);
v___x_5920_ = v___x_5837_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5924_; 
v_reuseFailAlloc_5924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5924_, 0, v___x_5914_);
lean_ctor_set(v_reuseFailAlloc_5924_, 1, v___x_5918_);
v___x_5920_ = v_reuseFailAlloc_5924_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
lean_object* v___x_5922_; 
if (v_isShared_5834_ == 0)
{
lean_ctor_set(v___x_5833_, 1, v___x_5920_);
lean_ctor_set(v___x_5833_, 0, v___x_5912_);
v___x_5922_ = v___x_5833_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v___x_5912_);
lean_ctor_set(v_reuseFailAlloc_5923_, 1, v___x_5920_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
v_a_5822_ = v___x_5922_;
goto v___jp_5821_;
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
v___jp_5821_:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___x_5823_ = lean_unsigned_to_nat(1u);
v___x_5824_ = lean_nat_add(v_a_5819_, v___x_5823_);
lean_dec(v_a_5819_);
v_a_5819_ = v___x_5824_;
v_b_5820_ = v_a_5822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5945_, lean_object* v_a_5946_, lean_object* v_b_5947_){
_start:
{
lean_object* v_res_5948_; 
v_res_5948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5945_, v_a_5946_, v_b_5947_);
lean_dec(v_upperBound_5945_);
return v_res_5948_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5949_, size_t v_i_5950_, size_t v_stop_5951_){
_start:
{
uint8_t v___x_5952_; 
v___x_5952_ = lean_usize_dec_eq(v_i_5950_, v_stop_5951_);
if (v___x_5952_ == 0)
{
lean_object* v___x_5953_; uint8_t v___x_5954_; 
v___x_5953_ = lean_array_uget_borrowed(v_as_5949_, v_i_5950_);
v___x_5954_ = l_Lean_Expr_isFVar(v___x_5953_);
if (v___x_5954_ == 0)
{
uint8_t v___x_5955_; 
v___x_5955_ = 1;
return v___x_5955_;
}
else
{
size_t v___x_5956_; size_t v___x_5957_; 
v___x_5956_ = ((size_t)1ULL);
v___x_5957_ = lean_usize_add(v_i_5950_, v___x_5956_);
v_i_5950_ = v___x_5957_;
goto _start;
}
}
else
{
uint8_t v___x_5959_; 
v___x_5959_ = 0;
return v___x_5959_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5949_ = stack[0].m_obj;
size_t v_i_5950_ = stack[1].m_num;
size_t v_stop_5951_ = stack[2].m_num;
uint8_t v_res_5960_;
v_res_5960_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5949_, v_i_5950_, v_stop_5951_);
stack->m_num = v_res_5960_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5961_, lean_object* v_i_5962_, lean_object* v_stop_5963_){
_start:
{
size_t v_i_boxed_5964_; size_t v_stop_boxed_5965_; uint8_t v_res_5966_; lean_object* v_r_5967_; 
v_i_boxed_5964_ = lean_unbox_usize(v_i_5962_);
lean_dec(v_i_5962_);
v_stop_boxed_5965_ = lean_unbox_usize(v_stop_5963_);
lean_dec(v_stop_5963_);
v_res_5966_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5961_, v_i_boxed_5964_, v_stop_boxed_5965_);
lean_dec_ref(v_as_5961_);
v_r_5967_ = lean_box(v_res_5966_);
return v_r_5967_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5968_, size_t v_sz_5969_, size_t v_i_5970_, lean_object* v_bs_5971_){
_start:
{
uint8_t v___x_5972_; 
v___x_5972_ = lean_usize_dec_lt(v_i_5970_, v_sz_5969_);
if (v___x_5972_ == 0)
{
return v_bs_5971_;
}
else
{
lean_object* v_v_5973_; lean_object* v___x_5974_; lean_object* v_bs_x27_5975_; lean_object* v___y_5977_; 
v_v_5973_ = lean_array_uget(v_bs_5971_, v_i_5970_);
v___x_5974_ = lean_unsigned_to_nat(0u);
v_bs_x27_5975_ = lean_array_uset(v_bs_5971_, v_i_5970_, v___x_5974_);
if (lean_obj_tag(v_v_5973_) == 0)
{
v___y_5977_ = v_v_5973_;
goto v___jp_5976_;
}
else
{
lean_object* v_val_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; 
v_val_5982_ = lean_ctor_get(v_v_5973_, 0);
lean_inc(v_val_5982_);
lean_dec_ref_known(v_v_5973_, 1);
v___x_5983_ = lean_box(0);
v___x_5984_ = lean_array_get_borrowed(v___x_5983_, v___x_5968_, v_val_5982_);
lean_dec(v_val_5982_);
lean_inc(v___x_5984_);
v___y_5977_ = v___x_5984_;
goto v___jp_5976_;
}
v___jp_5976_:
{
size_t v___x_5978_; size_t v___x_5979_; lean_object* v___x_5980_; 
v___x_5978_ = ((size_t)1ULL);
v___x_5979_ = lean_usize_add(v_i_5970_, v___x_5978_);
v___x_5980_ = lean_array_uset(v_bs_x27_5975_, v_i_5970_, v___y_5977_);
v_i_5970_ = v___x_5979_;
v_bs_5971_ = v___x_5980_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5968_ = stack[0].m_obj;
size_t v_sz_5969_ = stack[1].m_num;
size_t v_i_5970_ = stack[2].m_num;
lean_object* v_bs_5971_ = stack[3].m_obj;
lean_object* v_res_5985_;
v_res_5985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5968_, v_sz_5969_, v_i_5970_, v_bs_5971_);
stack->m_obj
 = v_res_5985_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5986_, lean_object* v_sz_5987_, lean_object* v_i_5988_, lean_object* v_bs_5989_){
_start:
{
size_t v_sz_boxed_5990_; size_t v_i_boxed_5991_; lean_object* v_res_5992_; 
v_sz_boxed_5990_ = lean_unbox_usize(v_sz_5987_);
lean_dec(v_sz_5987_);
v_i_boxed_5991_ = lean_unbox_usize(v_i_5988_);
lean_dec(v_i_5988_);
v_res_5992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5986_, v_sz_boxed_5990_, v_i_boxed_5991_, v_bs_5989_);
lean_dec_ref(v___x_5986_);
return v_res_5992_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5993_, size_t v_sz_5994_, size_t v_i_5995_, lean_object* v_bs_5996_){
_start:
{
uint8_t v___x_5997_; 
v___x_5997_ = lean_usize_dec_lt(v_i_5995_, v_sz_5994_);
if (v___x_5997_ == 0)
{
return v_bs_5996_;
}
else
{
lean_object* v_v_5998_; lean_object* v___x_5999_; lean_object* v_bs_x27_6000_; size_t v_sz_6001_; size_t v___x_6002_; lean_object* v___x_6003_; size_t v___x_6004_; size_t v___x_6005_; lean_object* v___x_6006_; 
v_v_5998_ = lean_array_uget(v_bs_5996_, v_i_5995_);
v___x_5999_ = lean_unsigned_to_nat(0u);
v_bs_x27_6000_ = lean_array_uset(v_bs_5996_, v_i_5995_, v___x_5999_);
v_sz_6001_ = lean_array_size(v_v_5998_);
v___x_6002_ = ((size_t)0ULL);
v___x_6003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5993_, v_sz_6001_, v___x_6002_, v_v_5998_);
v___x_6004_ = ((size_t)1ULL);
v___x_6005_ = lean_usize_add(v_i_5995_, v___x_6004_);
v___x_6006_ = lean_array_uset(v_bs_x27_6000_, v_i_5995_, v___x_6003_);
v_i_5995_ = v___x_6005_;
v_bs_5996_ = v___x_6006_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5993_ = stack[0].m_obj;
size_t v_sz_5994_ = stack[1].m_num;
size_t v_i_5995_ = stack[2].m_num;
lean_object* v_bs_5996_ = stack[3].m_obj;
lean_object* v_res_6008_;
v_res_6008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5993_, v_sz_5994_, v_i_5995_, v_bs_5996_);
stack->m_obj
 = v_res_6008_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_6009_, lean_object* v_sz_6010_, lean_object* v_i_6011_, lean_object* v_bs_6012_){
_start:
{
size_t v_sz_boxed_6013_; size_t v_i_boxed_6014_; lean_object* v_res_6015_; 
v_sz_boxed_6013_ = lean_unbox_usize(v_sz_6010_);
lean_dec(v_sz_6010_);
v_i_boxed_6014_ = lean_unbox_usize(v_i_6011_);
lean_dec(v_i_6011_);
v_res_6015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_6009_, v_sz_boxed_6013_, v_i_boxed_6014_, v_bs_6012_);
lean_dec_ref(v___x_6009_);
return v_res_6015_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_6019_ = lean_unsigned_to_nat(6u);
v___x_6020_ = lean_unsigned_to_nat(463u);
v___x_6021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6022_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6023_ = l_mkPanicMessageWithDecl(v___x_6022_, v___x_6021_, v___x_6020_, v___x_6019_, v___x_6018_);
return v___x_6023_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_6024_, lean_object* v___x_6025_, lean_object* v___x_6026_, lean_object* v_as_6027_, size_t v_sz_6028_, size_t v_i_6029_, lean_object* v_b_6030_){
_start:
{
lean_object* v_a_6032_; uint8_t v___x_6036_; 
v___x_6036_ = lean_usize_dec_lt(v_i_6029_, v_sz_6028_);
if (v___x_6036_ == 0)
{
return v_b_6030_;
}
else
{
lean_object* v_a_6037_; lean_object* v___x_6038_; uint8_t v___x_6039_; 
v_a_6037_ = lean_array_uget_borrowed(v_as_6027_, v_i_6029_);
v___x_6038_ = lean_array_get_size(v___x_6024_);
v___x_6039_ = lean_nat_dec_lt(v_a_6037_, v___x_6038_);
if (v___x_6039_ == 0)
{
lean_object* v___x_6040_; lean_object* v___x_6041_; 
lean_dec_ref(v_b_6030_);
v___x_6040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_6041_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_6040_);
if (lean_obj_tag(v___x_6041_) == 0)
{
lean_object* v_a_6042_; 
v_a_6042_ = lean_ctor_get(v___x_6041_, 0);
lean_inc(v_a_6042_);
lean_dec_ref_known(v___x_6041_, 1);
return v_a_6042_;
}
else
{
lean_object* v_a_6043_; 
v_a_6043_ = lean_ctor_get(v___x_6041_, 0);
lean_inc(v_a_6043_);
lean_dec_ref_known(v___x_6041_, 1);
v_a_6032_ = v_a_6043_;
goto v___jp_6031_;
}
}
else
{
lean_object* v___x_6044_; lean_object* v___x_6045_; 
v___x_6044_ = lean_box(0);
v___x_6045_ = lean_array_get_borrowed(v___x_6044_, v___x_6024_, v_a_6037_);
if (lean_obj_tag(v___x_6045_) == 1)
{
lean_object* v_val_6046_; uint8_t v_changed_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v_val_6046_ = lean_ctor_get(v___x_6045_, 0);
v_changed_6047_ = lean_nat_dec_eq(v___x_6025_, v___x_6026_);
v___x_6048_ = lean_box(v_changed_6047_);
v___x_6049_ = lean_array_set(v_b_6030_, v_val_6046_, v___x_6048_);
v_a_6032_ = v___x_6049_;
goto v___jp_6031_;
}
else
{
v_a_6032_ = v_b_6030_;
goto v___jp_6031_;
}
}
}
v___jp_6031_:
{
size_t v___x_6033_; size_t v___x_6034_; 
v___x_6033_ = ((size_t)1ULL);
v___x_6034_ = lean_usize_add(v_i_6029_, v___x_6033_);
v_i_6029_ = v___x_6034_;
v_b_6030_ = v_a_6032_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_6024_ = stack[0].m_obj;
lean_object* v___x_6025_ = stack[1].m_obj;
lean_object* v___x_6026_ = stack[2].m_obj;
lean_object* v_as_6027_ = stack[3].m_obj;
size_t v_sz_6028_ = stack[4].m_num;
size_t v_i_6029_ = stack[5].m_num;
lean_object* v_b_6030_ = stack[6].m_obj;
lean_object* v_res_6050_;
v_res_6050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_6024_, v___x_6025_, v___x_6026_, v_as_6027_, v_sz_6028_, v_i_6029_, v_b_6030_);
stack->m_obj
 = v_res_6050_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_6051_, lean_object* v___x_6052_, lean_object* v___x_6053_, lean_object* v_as_6054_, lean_object* v_sz_6055_, lean_object* v_i_6056_, lean_object* v_b_6057_){
_start:
{
size_t v_sz_boxed_6058_; size_t v_i_boxed_6059_; lean_object* v_res_6060_; 
v_sz_boxed_6058_ = lean_unbox_usize(v_sz_6055_);
lean_dec(v_sz_6055_);
v_i_boxed_6059_ = lean_unbox_usize(v_i_6056_);
lean_dec(v_i_6056_);
v_res_6060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_6051_, v___x_6052_, v___x_6053_, v_as_6054_, v_sz_boxed_6058_, v_i_boxed_6059_, v_b_6057_);
lean_dec_ref(v_as_6054_);
lean_dec(v___x_6053_);
lean_dec(v___x_6052_);
lean_dec_ref(v___x_6051_);
return v_res_6060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_6061_, lean_object* v___x_6062_, lean_object* v___x_6063_, lean_object* v_a_6064_, lean_object* v_b_6065_){
_start:
{
uint8_t v___x_6066_; 
v___x_6066_ = lean_nat_dec_lt(v_a_6064_, v_upperBound_6061_);
if (v___x_6066_ == 0)
{
lean_dec(v_a_6064_);
return v_b_6065_;
}
else
{
lean_object* v_snd_6067_; lean_object* v_snd_6068_; lean_object* v_fst_6069_; lean_object* v___x_6071_; uint8_t v_isShared_6072_; uint8_t v_isSharedCheck_6135_; 
v_snd_6067_ = lean_ctor_get(v_b_6065_, 1);
lean_inc(v_snd_6067_);
v_snd_6068_ = lean_ctor_get(v_snd_6067_, 1);
lean_inc(v_snd_6068_);
v_fst_6069_ = lean_ctor_get(v_b_6065_, 0);
v_isSharedCheck_6135_ = !lean_is_exclusive(v_b_6065_);
if (v_isSharedCheck_6135_ == 0)
{
lean_object* v_unused_6136_; 
v_unused_6136_ = lean_ctor_get(v_b_6065_, 1);
lean_dec(v_unused_6136_);
v___x_6071_ = v_b_6065_;
v_isShared_6072_ = v_isSharedCheck_6135_;
goto v_resetjp_6070_;
}
else
{
lean_inc(v_fst_6069_);
lean_dec(v_b_6065_);
v___x_6071_ = lean_box(0);
v_isShared_6072_ = v_isSharedCheck_6135_;
goto v_resetjp_6070_;
}
v_resetjp_6070_:
{
lean_object* v_fst_6073_; lean_object* v___x_6075_; uint8_t v_isShared_6076_; uint8_t v_isSharedCheck_6133_; 
v_fst_6073_ = lean_ctor_get(v_snd_6067_, 0);
v_isSharedCheck_6133_ = !lean_is_exclusive(v_snd_6067_);
if (v_isSharedCheck_6133_ == 0)
{
lean_object* v_unused_6134_; 
v_unused_6134_ = lean_ctor_get(v_snd_6067_, 1);
lean_dec(v_unused_6134_);
v___x_6075_ = v_snd_6067_;
v_isShared_6076_ = v_isSharedCheck_6133_;
goto v_resetjp_6074_;
}
else
{
lean_inc(v_fst_6073_);
lean_dec(v_snd_6067_);
v___x_6075_ = lean_box(0);
v_isShared_6076_ = v_isSharedCheck_6133_;
goto v_resetjp_6074_;
}
v_resetjp_6074_:
{
lean_object* v_array_6077_; lean_object* v_start_6078_; lean_object* v_stop_6079_; uint8_t v___x_6080_; 
v_array_6077_ = lean_ctor_get(v_snd_6068_, 0);
v_start_6078_ = lean_ctor_get(v_snd_6068_, 1);
v_stop_6079_ = lean_ctor_get(v_snd_6068_, 2);
v___x_6080_ = lean_nat_dec_lt(v_start_6078_, v_stop_6079_);
if (v___x_6080_ == 0)
{
lean_object* v___x_6082_; 
lean_dec(v_a_6064_);
if (v_isShared_6076_ == 0)
{
v___x_6082_ = v___x_6075_;
goto v_reusejp_6081_;
}
else
{
lean_object* v_reuseFailAlloc_6086_; 
v_reuseFailAlloc_6086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6086_, 0, v_fst_6073_);
lean_ctor_set(v_reuseFailAlloc_6086_, 1, v_snd_6068_);
v___x_6082_ = v_reuseFailAlloc_6086_;
goto v_reusejp_6081_;
}
v_reusejp_6081_:
{
lean_object* v___x_6084_; 
if (v_isShared_6072_ == 0)
{
lean_ctor_set(v___x_6071_, 1, v___x_6082_);
v___x_6084_ = v___x_6071_;
goto v_reusejp_6083_;
}
else
{
lean_object* v_reuseFailAlloc_6085_; 
v_reuseFailAlloc_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_fst_6069_);
lean_ctor_set(v_reuseFailAlloc_6085_, 1, v___x_6082_);
v___x_6084_ = v_reuseFailAlloc_6085_;
goto v_reusejp_6083_;
}
v_reusejp_6083_:
{
return v___x_6084_;
}
}
}
else
{
lean_object* v___x_6088_; uint8_t v_isShared_6089_; uint8_t v_isSharedCheck_6129_; 
lean_inc(v_stop_6079_);
lean_inc(v_start_6078_);
lean_inc_ref(v_array_6077_);
v_isSharedCheck_6129_ = !lean_is_exclusive(v_snd_6068_);
if (v_isSharedCheck_6129_ == 0)
{
lean_object* v_unused_6130_; lean_object* v_unused_6131_; lean_object* v_unused_6132_; 
v_unused_6130_ = lean_ctor_get(v_snd_6068_, 2);
lean_dec(v_unused_6130_);
v_unused_6131_ = lean_ctor_get(v_snd_6068_, 1);
lean_dec(v_unused_6131_);
v_unused_6132_ = lean_ctor_get(v_snd_6068_, 0);
lean_dec(v_unused_6132_);
v___x_6088_ = v_snd_6068_;
v_isShared_6089_ = v_isSharedCheck_6129_;
goto v_resetjp_6087_;
}
else
{
lean_dec(v_snd_6068_);
v___x_6088_ = lean_box(0);
v_isShared_6089_ = v_isSharedCheck_6129_;
goto v_resetjp_6087_;
}
v_resetjp_6087_:
{
lean_object* v_array_6090_; lean_object* v_start_6091_; lean_object* v_stop_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6097_; 
v_array_6090_ = lean_ctor_get(v_fst_6073_, 0);
v_start_6091_ = lean_ctor_get(v_fst_6073_, 1);
v_stop_6092_ = lean_ctor_get(v_fst_6073_, 2);
v___x_6093_ = lean_array_fget(v_array_6077_, v_start_6078_);
v___x_6094_ = lean_unsigned_to_nat(1u);
v___x_6095_ = lean_nat_add(v_start_6078_, v___x_6094_);
lean_dec(v_start_6078_);
if (v_isShared_6089_ == 0)
{
lean_ctor_set(v___x_6088_, 1, v___x_6095_);
v___x_6097_ = v___x_6088_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6128_; 
v_reuseFailAlloc_6128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6128_, 0, v_array_6077_);
lean_ctor_set(v_reuseFailAlloc_6128_, 1, v___x_6095_);
lean_ctor_set(v_reuseFailAlloc_6128_, 2, v_stop_6079_);
v___x_6097_ = v_reuseFailAlloc_6128_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
uint8_t v___x_6098_; 
v___x_6098_ = lean_nat_dec_lt(v_start_6091_, v_stop_6092_);
if (v___x_6098_ == 0)
{
lean_object* v___x_6100_; 
lean_dec(v___x_6093_);
lean_dec(v_a_6064_);
if (v_isShared_6076_ == 0)
{
lean_ctor_set(v___x_6075_, 1, v___x_6097_);
v___x_6100_ = v___x_6075_;
goto v_reusejp_6099_;
}
else
{
lean_object* v_reuseFailAlloc_6104_; 
v_reuseFailAlloc_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6104_, 0, v_fst_6073_);
lean_ctor_set(v_reuseFailAlloc_6104_, 1, v___x_6097_);
v___x_6100_ = v_reuseFailAlloc_6104_;
goto v_reusejp_6099_;
}
v_reusejp_6099_:
{
lean_object* v___x_6102_; 
if (v_isShared_6072_ == 0)
{
lean_ctor_set(v___x_6071_, 1, v___x_6100_);
v___x_6102_ = v___x_6071_;
goto v_reusejp_6101_;
}
else
{
lean_object* v_reuseFailAlloc_6103_; 
v_reuseFailAlloc_6103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6103_, 0, v_fst_6069_);
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
else
{
lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6124_; 
lean_inc(v_stop_6092_);
lean_inc(v_start_6091_);
lean_inc_ref(v_array_6090_);
v_isSharedCheck_6124_ = !lean_is_exclusive(v_fst_6073_);
if (v_isSharedCheck_6124_ == 0)
{
lean_object* v_unused_6125_; lean_object* v_unused_6126_; lean_object* v_unused_6127_; 
v_unused_6125_ = lean_ctor_get(v_fst_6073_, 2);
lean_dec(v_unused_6125_);
v_unused_6126_ = lean_ctor_get(v_fst_6073_, 1);
lean_dec(v_unused_6126_);
v_unused_6127_ = lean_ctor_get(v_fst_6073_, 0);
lean_dec(v_unused_6127_);
v___x_6106_ = v_fst_6073_;
v_isShared_6107_ = v_isSharedCheck_6124_;
goto v_resetjp_6105_;
}
else
{
lean_dec(v_fst_6073_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6124_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6111_; 
v___x_6108_ = lean_array_fget(v_array_6090_, v_start_6091_);
v___x_6109_ = lean_nat_add(v_start_6091_, v___x_6094_);
lean_dec(v_start_6091_);
if (v_isShared_6107_ == 0)
{
lean_ctor_set(v___x_6106_, 1, v___x_6109_);
v___x_6111_ = v___x_6106_;
goto v_reusejp_6110_;
}
else
{
lean_object* v_reuseFailAlloc_6123_; 
v_reuseFailAlloc_6123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6123_, 0, v_array_6090_);
lean_ctor_set(v_reuseFailAlloc_6123_, 1, v___x_6109_);
lean_ctor_set(v_reuseFailAlloc_6123_, 2, v_stop_6092_);
v___x_6111_ = v_reuseFailAlloc_6123_;
goto v_reusejp_6110_;
}
v_reusejp_6110_:
{
size_t v_sz_6112_; size_t v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6116_; 
v_sz_6112_ = lean_array_size(v___x_6108_);
v___x_6113_ = ((size_t)0ULL);
v___x_6114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_6093_, v___x_6062_, v___x_6063_, v___x_6108_, v_sz_6112_, v___x_6113_, v_fst_6069_);
lean_dec(v___x_6108_);
lean_dec(v___x_6093_);
if (v_isShared_6076_ == 0)
{
lean_ctor_set(v___x_6075_, 1, v___x_6097_);
lean_ctor_set(v___x_6075_, 0, v___x_6111_);
v___x_6116_ = v___x_6075_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v___x_6111_);
lean_ctor_set(v_reuseFailAlloc_6122_, 1, v___x_6097_);
v___x_6116_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
lean_object* v___x_6118_; 
if (v_isShared_6072_ == 0)
{
lean_ctor_set(v___x_6071_, 1, v___x_6116_);
lean_ctor_set(v___x_6071_, 0, v___x_6114_);
v___x_6118_ = v___x_6071_;
goto v_reusejp_6117_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v___x_6114_);
lean_ctor_set(v_reuseFailAlloc_6121_, 1, v___x_6116_);
v___x_6118_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6117_;
}
v_reusejp_6117_:
{
lean_object* v___x_6119_; 
v___x_6119_ = lean_nat_add(v_a_6064_, v___x_6094_);
lean_dec(v_a_6064_);
v_a_6064_ = v___x_6119_;
v_b_6065_ = v___x_6118_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6137_, lean_object* v___x_6138_, lean_object* v___x_6139_, lean_object* v_a_6140_, lean_object* v_b_6141_){
_start:
{
lean_object* v_res_6142_; 
v_res_6142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6137_, v___x_6138_, v___x_6139_, v_a_6140_, v_b_6141_);
lean_dec(v___x_6139_);
lean_dec(v___x_6138_);
lean_dec(v_upperBound_6137_);
return v_res_6142_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; 
v___x_6144_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6145_ = lean_unsigned_to_nat(2u);
v___x_6146_ = lean_unsigned_to_nat(457u);
v___x_6147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6148_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6149_ = l_mkPanicMessageWithDecl(v___x_6148_, v___x_6147_, v___x_6146_, v___x_6145_, v___x_6144_);
return v___x_6149_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; 
v___x_6151_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6152_ = lean_unsigned_to_nat(2u);
v___x_6153_ = lean_unsigned_to_nat(458u);
v___x_6154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6155_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6156_ = l_mkPanicMessageWithDecl(v___x_6155_, v___x_6154_, v___x_6153_, v___x_6152_, v___x_6151_);
return v___x_6156_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v___x_6158_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6159_ = lean_unsigned_to_nat(2u);
v___x_6160_ = lean_unsigned_to_nat(456u);
v___x_6161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6162_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6163_ = l_mkPanicMessageWithDecl(v___x_6162_, v___x_6161_, v___x_6160_, v___x_6159_, v___x_6158_);
return v___x_6163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6164_, lean_object* v_xs_6165_, lean_object* v_toErase_6166_){
_start:
{
lean_object* v___x_6167_; lean_object* v___x_6168_; uint8_t v___x_6252_; 
v___x_6167_ = lean_unsigned_to_nat(0u);
v___x_6168_ = lean_array_get_size(v_xs_6165_);
v___x_6252_ = lean_nat_dec_lt(v___x_6167_, v___x_6168_);
if (v___x_6252_ == 0)
{
goto v___jp_6169_;
}
else
{
if (v___x_6252_ == 0)
{
goto v___jp_6169_;
}
else
{
size_t v___x_6253_; size_t v___x_6254_; uint8_t v___x_6255_; 
v___x_6253_ = ((size_t)0ULL);
v___x_6254_ = lean_usize_of_nat(v___x_6168_);
v___x_6255_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6165_, v___x_6253_, v___x_6254_);
if (v___x_6255_ == 0)
{
goto v___jp_6169_;
}
else
{
lean_object* v___x_6256_; lean_object* v___x_6257_; 
lean_dec_ref(v_toErase_6166_);
lean_dec_ref(v_xs_6165_);
lean_dec_ref(v_fixedParamPerms_6164_);
v___x_6256_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6257_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6256_);
return v___x_6257_;
}
}
}
v___jp_6169_:
{
lean_object* v_numFixed_6170_; lean_object* v_perms_6171_; lean_object* v_revDeps_6172_; uint8_t v___x_6173_; 
v_numFixed_6170_ = lean_ctor_get(v_fixedParamPerms_6164_, 0);
v_perms_6171_ = lean_ctor_get(v_fixedParamPerms_6164_, 1);
lean_inc_ref(v_perms_6171_);
v_revDeps_6172_ = lean_ctor_get(v_fixedParamPerms_6164_, 2);
lean_inc_ref(v_revDeps_6172_);
v___x_6173_ = lean_nat_dec_eq(v_numFixed_6170_, v___x_6168_);
if (v___x_6173_ == 0)
{
lean_object* v___x_6174_; lean_object* v___x_6175_; 
lean_dec_ref(v_revDeps_6172_);
lean_dec_ref(v_perms_6171_);
lean_dec_ref(v_toErase_6166_);
lean_dec_ref(v_xs_6165_);
lean_dec_ref(v_fixedParamPerms_6164_);
v___x_6174_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6175_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6174_);
return v___x_6175_;
}
else
{
lean_object* v___x_6176_; lean_object* v___x_6177_; uint8_t v_changed_6178_; 
v___x_6176_ = lean_array_get_size(v_toErase_6166_);
v___x_6177_ = lean_array_get_size(v_perms_6171_);
v_changed_6178_ = lean_nat_dec_eq(v___x_6176_, v___x_6177_);
if (v_changed_6178_ == 0)
{
lean_object* v___x_6179_; lean_object* v___x_6180_; 
lean_dec_ref(v_revDeps_6172_);
lean_dec_ref(v_perms_6171_);
lean_dec_ref(v_toErase_6166_);
lean_dec_ref(v_xs_6165_);
lean_dec_ref(v_fixedParamPerms_6164_);
v___x_6179_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6180_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6179_);
return v___x_6180_;
}
else
{
uint8_t v_changed_6181_; lean_object* v___x_6182_; lean_object* v_mask_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v_fst_6189_; lean_object* v___x_6191_; uint8_t v_isShared_6192_; uint8_t v_isSharedCheck_6250_; 
v_changed_6181_ = 0;
v___x_6182_ = lean_box(v_changed_6181_);
lean_inc(v_numFixed_6170_);
v_mask_6183_ = lean_mk_array(v_numFixed_6170_, v___x_6182_);
v___x_6184_ = l_Array_toSubarray___redArg(v_toErase_6166_, v___x_6167_, v___x_6176_);
lean_inc_ref(v_perms_6171_);
v___x_6185_ = l_Array_toSubarray___redArg(v_perms_6171_, v___x_6167_, v___x_6177_);
v___x_6186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6186_, 0, v___x_6184_);
lean_ctor_set(v___x_6186_, 1, v___x_6185_);
v___x_6187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6187_, 0, v_mask_6183_);
lean_ctor_set(v___x_6187_, 1, v___x_6186_);
v___x_6188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6176_, v___x_6176_, v___x_6177_, v___x_6167_, v___x_6187_);
v_fst_6189_ = lean_ctor_get(v___x_6188_, 0);
v_isSharedCheck_6250_ = !lean_is_exclusive(v___x_6188_);
if (v_isSharedCheck_6250_ == 0)
{
lean_object* v_unused_6251_; 
v_unused_6251_ = lean_ctor_get(v___x_6188_, 1);
lean_dec(v_unused_6251_);
v___x_6191_ = v___x_6188_;
v_isShared_6192_ = v_isSharedCheck_6250_;
goto v_resetjp_6190_;
}
else
{
lean_inc(v_fst_6189_);
lean_dec(v___x_6188_);
v___x_6191_ = lean_box(0);
v_isShared_6192_ = v_isSharedCheck_6250_;
goto v_resetjp_6190_;
}
v_resetjp_6190_:
{
lean_object* v___x_6193_; lean_object* v___x_6195_; 
v___x_6193_ = lean_box(v_changed_6178_);
if (v_isShared_6192_ == 0)
{
lean_ctor_set(v___x_6191_, 1, v___x_6193_);
v___x_6195_ = v___x_6191_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6249_; 
v_reuseFailAlloc_6249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6249_, 0, v_fst_6189_);
lean_ctor_set(v_reuseFailAlloc_6249_, 1, v___x_6193_);
v___x_6195_ = v_reuseFailAlloc_6249_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
lean_object* v___x_6196_; lean_object* v___x_6198_; uint8_t v_isShared_6199_; uint8_t v_isSharedCheck_6245_; 
v___x_6196_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6177_, v_perms_6171_, v___x_6176_, v_fixedParamPerms_6164_, v___x_6195_);
v_isSharedCheck_6245_ = !lean_is_exclusive(v_fixedParamPerms_6164_);
if (v_isSharedCheck_6245_ == 0)
{
lean_object* v_unused_6246_; lean_object* v_unused_6247_; lean_object* v_unused_6248_; 
v_unused_6246_ = lean_ctor_get(v_fixedParamPerms_6164_, 2);
lean_dec(v_unused_6246_);
v_unused_6247_ = lean_ctor_get(v_fixedParamPerms_6164_, 1);
lean_dec(v_unused_6247_);
v_unused_6248_ = lean_ctor_get(v_fixedParamPerms_6164_, 0);
lean_dec(v_unused_6248_);
v___x_6198_ = v_fixedParamPerms_6164_;
v_isShared_6199_ = v_isSharedCheck_6245_;
goto v_resetjp_6197_;
}
else
{
lean_dec(v_fixedParamPerms_6164_);
v___x_6198_ = lean_box(0);
v_isShared_6199_ = v_isSharedCheck_6245_;
goto v_resetjp_6197_;
}
v_resetjp_6197_:
{
lean_object* v_fst_6200_; lean_object* v___x_6202_; uint8_t v_isShared_6203_; uint8_t v_isSharedCheck_6243_; 
v_fst_6200_ = lean_ctor_get(v___x_6196_, 0);
v_isSharedCheck_6243_ = !lean_is_exclusive(v___x_6196_);
if (v_isSharedCheck_6243_ == 0)
{
lean_object* v_unused_6244_; 
v_unused_6244_ = lean_ctor_get(v___x_6196_, 1);
lean_dec(v_unused_6244_);
v___x_6202_ = v___x_6196_;
v_isShared_6203_ = v_isSharedCheck_6243_;
goto v_resetjp_6201_;
}
else
{
lean_inc(v_fst_6200_);
lean_dec(v___x_6196_);
v___x_6202_ = lean_box(0);
v_isShared_6203_ = v_isSharedCheck_6243_;
goto v_resetjp_6201_;
}
v_resetjp_6201_:
{
lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6209_; 
v___x_6204_ = lean_array_get_size(v_fst_6200_);
v___x_6205_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6206_ = l_Array_toSubarray___redArg(v_fst_6200_, v___x_6167_, v___x_6204_);
v___x_6207_ = l_Array_toSubarray___redArg(v_xs_6165_, v___x_6167_, v___x_6168_);
if (v_isShared_6203_ == 0)
{
lean_ctor_set(v___x_6202_, 1, v___x_6207_);
lean_ctor_set(v___x_6202_, 0, v___x_6206_);
v___x_6209_ = v___x_6202_;
goto v_reusejp_6208_;
}
else
{
lean_object* v_reuseFailAlloc_6242_; 
v_reuseFailAlloc_6242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6242_, 0, v___x_6206_);
lean_ctor_set(v_reuseFailAlloc_6242_, 1, v___x_6207_);
v___x_6209_ = v_reuseFailAlloc_6242_;
goto v_reusejp_6208_;
}
v_reusejp_6208_:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v_snd_6214_; lean_object* v_snd_6215_; lean_object* v_fst_6216_; lean_object* v_fst_6217_; lean_object* v___x_6219_; uint8_t v_isShared_6220_; uint8_t v_isSharedCheck_6240_; 
v___x_6210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6205_);
lean_ctor_set(v___x_6210_, 1, v___x_6209_);
v___x_6211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6211_, 0, v___x_6205_);
lean_ctor_set(v___x_6211_, 1, v___x_6210_);
v___x_6212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6205_);
lean_ctor_set(v___x_6212_, 1, v___x_6211_);
v___x_6213_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6204_, v___x_6167_, v___x_6212_);
v_snd_6214_ = lean_ctor_get(v___x_6213_, 1);
lean_inc(v_snd_6214_);
v_snd_6215_ = lean_ctor_get(v_snd_6214_, 1);
lean_inc(v_snd_6215_);
v_fst_6216_ = lean_ctor_get(v___x_6213_, 0);
lean_inc(v_fst_6216_);
lean_dec_ref(v___x_6213_);
v_fst_6217_ = lean_ctor_get(v_snd_6214_, 0);
v_isSharedCheck_6240_ = !lean_is_exclusive(v_snd_6214_);
if (v_isSharedCheck_6240_ == 0)
{
lean_object* v_unused_6241_; 
v_unused_6241_ = lean_ctor_get(v_snd_6214_, 1);
lean_dec(v_unused_6241_);
v___x_6219_ = v_snd_6214_;
v_isShared_6220_ = v_isSharedCheck_6240_;
goto v_resetjp_6218_;
}
else
{
lean_inc(v_fst_6217_);
lean_dec(v_snd_6214_);
v___x_6219_ = lean_box(0);
v_isShared_6220_ = v_isSharedCheck_6240_;
goto v_resetjp_6218_;
}
v_resetjp_6218_:
{
lean_object* v_fst_6221_; lean_object* v___x_6223_; uint8_t v_isShared_6224_; uint8_t v_isSharedCheck_6238_; 
v_fst_6221_ = lean_ctor_get(v_snd_6215_, 0);
v_isSharedCheck_6238_ = !lean_is_exclusive(v_snd_6215_);
if (v_isSharedCheck_6238_ == 0)
{
lean_object* v_unused_6239_; 
v_unused_6239_ = lean_ctor_get(v_snd_6215_, 1);
lean_dec(v_unused_6239_);
v___x_6223_ = v_snd_6215_;
v_isShared_6224_ = v_isSharedCheck_6238_;
goto v_resetjp_6222_;
}
else
{
lean_inc(v_fst_6221_);
lean_dec(v_snd_6215_);
v___x_6223_ = lean_box(0);
v_isShared_6224_ = v_isSharedCheck_6238_;
goto v_resetjp_6222_;
}
v_resetjp_6222_:
{
lean_object* v___x_6225_; size_t v_sz_6226_; size_t v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6230_; 
v___x_6225_ = lean_array_get_size(v_fst_6221_);
v_sz_6226_ = lean_array_size(v_perms_6171_);
v___x_6227_ = ((size_t)0ULL);
v___x_6228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6216_, v_sz_6226_, v___x_6227_, v_perms_6171_);
lean_dec(v_fst_6216_);
if (v_isShared_6199_ == 0)
{
lean_ctor_set(v___x_6198_, 1, v___x_6228_);
lean_ctor_set(v___x_6198_, 0, v___x_6225_);
v___x_6230_ = v___x_6198_;
goto v_reusejp_6229_;
}
else
{
lean_object* v_reuseFailAlloc_6237_; 
v_reuseFailAlloc_6237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6237_, 0, v___x_6225_);
lean_ctor_set(v_reuseFailAlloc_6237_, 1, v___x_6228_);
lean_ctor_set(v_reuseFailAlloc_6237_, 2, v_revDeps_6172_);
v___x_6230_ = v_reuseFailAlloc_6237_;
goto v_reusejp_6229_;
}
v_reusejp_6229_:
{
lean_object* v___x_6232_; 
if (v_isShared_6224_ == 0)
{
lean_ctor_set(v___x_6223_, 1, v_fst_6217_);
v___x_6232_ = v___x_6223_;
goto v_reusejp_6231_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v_fst_6221_);
lean_ctor_set(v_reuseFailAlloc_6236_, 1, v_fst_6217_);
v___x_6232_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6231_;
}
v_reusejp_6231_:
{
lean_object* v___x_6234_; 
if (v_isShared_6220_ == 0)
{
lean_ctor_set(v___x_6219_, 1, v___x_6232_);
lean_ctor_set(v___x_6219_, 0, v___x_6230_);
v___x_6234_ = v___x_6219_;
goto v_reusejp_6233_;
}
else
{
lean_object* v_reuseFailAlloc_6235_; 
v_reuseFailAlloc_6235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6235_, 0, v___x_6230_);
lean_ctor_set(v_reuseFailAlloc_6235_, 1, v___x_6232_);
v___x_6234_ = v_reuseFailAlloc_6235_;
goto v_reusejp_6233_;
}
v_reusejp_6233_:
{
return v___x_6234_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6258_, lean_object* v___x_6259_, lean_object* v___x_6260_, lean_object* v___x_6261_, lean_object* v_fixedParamPerms_6262_, lean_object* v_next_6263_, lean_object* v_inst_6264_, lean_object* v_R_6265_, lean_object* v_a_6266_, lean_object* v_b_6267_, lean_object* v_c_6268_){
_start:
{
lean_object* v___x_6269_; 
v___x_6269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6258_, v___x_6259_, v___x_6260_, v___x_6261_, v_fixedParamPerms_6262_, v_next_6263_, v_a_6266_, v_b_6267_);
return v___x_6269_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6270_, lean_object* v___x_6271_, lean_object* v___x_6272_, lean_object* v___x_6273_, lean_object* v_fixedParamPerms_6274_, lean_object* v_next_6275_, lean_object* v_inst_6276_, lean_object* v_R_6277_, lean_object* v_a_6278_, lean_object* v_b_6279_, lean_object* v_c_6280_){
_start:
{
lean_object* v_res_6281_; 
v_res_6281_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6270_, v___x_6271_, v___x_6272_, v___x_6273_, v_fixedParamPerms_6274_, v_next_6275_, v_inst_6276_, v_R_6277_, v_a_6278_, v_b_6279_, v_c_6280_);
lean_dec(v_a_6278_);
lean_dec(v_next_6275_);
lean_dec_ref(v_fixedParamPerms_6274_);
lean_dec(v___x_6273_);
lean_dec(v___x_6272_);
lean_dec_ref(v___x_6271_);
lean_dec(v_upperBound_6270_);
return v_res_6281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6282_, lean_object* v___x_6283_, lean_object* v___x_6284_, lean_object* v___x_6285_, lean_object* v_fixedParamPerms_6286_, lean_object* v_inst_6287_, lean_object* v_R_6288_, lean_object* v_a_6289_, lean_object* v_b_6290_, lean_object* v_c_6291_){
_start:
{
lean_object* v___x_6292_; 
v___x_6292_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6282_, v___x_6283_, v___x_6284_, v___x_6285_, v_fixedParamPerms_6286_, v_a_6289_, v_b_6290_);
return v___x_6292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6293_, lean_object* v___x_6294_, lean_object* v___x_6295_, lean_object* v___x_6296_, lean_object* v_fixedParamPerms_6297_, lean_object* v_inst_6298_, lean_object* v_R_6299_, lean_object* v_a_6300_, lean_object* v_b_6301_, lean_object* v_c_6302_){
_start:
{
lean_object* v_res_6303_; 
v_res_6303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6293_, v___x_6294_, v___x_6295_, v___x_6296_, v_fixedParamPerms_6297_, v_inst_6298_, v_R_6299_, v_a_6300_, v_b_6301_, v_c_6302_);
lean_dec_ref(v_fixedParamPerms_6297_);
lean_dec(v___x_6296_);
lean_dec(v___x_6295_);
lean_dec_ref(v___x_6294_);
lean_dec(v_upperBound_6293_);
return v_res_6303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6304_, lean_object* v___x_6305_, lean_object* v___x_6306_, lean_object* v_fixedParamPerms_6307_, lean_object* v_inst_6308_, lean_object* v_a_6309_){
_start:
{
lean_object* v___x_6310_; 
v___x_6310_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6304_, v___x_6305_, v___x_6306_, v_fixedParamPerms_6307_, v_a_6309_);
return v___x_6310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6311_, lean_object* v___x_6312_, lean_object* v___x_6313_, lean_object* v_fixedParamPerms_6314_, lean_object* v_inst_6315_, lean_object* v_a_6316_){
_start:
{
lean_object* v_res_6317_; 
v_res_6317_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6311_, v___x_6312_, v___x_6313_, v_fixedParamPerms_6314_, v_inst_6315_, v_a_6316_);
lean_dec_ref(v_fixedParamPerms_6314_);
lean_dec(v___x_6313_);
lean_dec_ref(v___x_6312_);
lean_dec(v___x_6311_);
return v_res_6317_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6318_, lean_object* v_inst_6319_, lean_object* v_R_6320_, lean_object* v_a_6321_, lean_object* v_b_6322_, lean_object* v_c_6323_){
_start:
{
lean_object* v___x_6324_; 
v___x_6324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6318_, v_a_6321_, v_b_6322_);
return v___x_6324_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6325_, lean_object* v_inst_6326_, lean_object* v_R_6327_, lean_object* v_a_6328_, lean_object* v_b_6329_, lean_object* v_c_6330_){
_start:
{
lean_object* v_res_6331_; 
v_res_6331_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6325_, v_inst_6326_, v_R_6327_, v_a_6328_, v_b_6329_, v_c_6330_);
lean_dec(v_upperBound_6325_);
return v_res_6331_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6332_, lean_object* v___x_6333_, lean_object* v___x_6334_, lean_object* v_inst_6335_, lean_object* v_R_6336_, lean_object* v_a_6337_, lean_object* v_b_6338_, lean_object* v_c_6339_){
_start:
{
lean_object* v___x_6340_; 
v___x_6340_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6332_, v___x_6333_, v___x_6334_, v_a_6337_, v_b_6338_);
return v___x_6340_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6341_, lean_object* v___x_6342_, lean_object* v___x_6343_, lean_object* v_inst_6344_, lean_object* v_R_6345_, lean_object* v_a_6346_, lean_object* v_b_6347_, lean_object* v_c_6348_){
_start:
{
lean_object* v_res_6349_; 
v_res_6349_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6341_, v___x_6342_, v___x_6343_, v_inst_6344_, v_R_6345_, v_a_6346_, v_b_6347_, v_c_6348_);
lean_dec(v___x_6343_);
lean_dec(v___x_6342_);
lean_dec(v_upperBound_6341_);
return v_res_6349_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object* v_upperBound_6350_, lean_object* v___x_6351_, lean_object* v_fixedParamPerms_6352_, lean_object* v_next_6353_, lean_object* v___x_6354_, lean_object* v___x_6355_, lean_object* v_inst_6356_, lean_object* v_R_6357_, lean_object* v_a_6358_, lean_object* v_b_6359_, lean_object* v_c_6360_){
_start:
{
lean_object* v___x_6361_; 
v___x_6361_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_6350_, v___x_6351_, v_fixedParamPerms_6352_, v_next_6353_, v___x_6354_, v___x_6355_, v_a_6358_, v_b_6359_);
return v___x_6361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object* v_upperBound_6362_, lean_object* v___x_6363_, lean_object* v_fixedParamPerms_6364_, lean_object* v_next_6365_, lean_object* v___x_6366_, lean_object* v___x_6367_, lean_object* v_inst_6368_, lean_object* v_R_6369_, lean_object* v_a_6370_, lean_object* v_b_6371_, lean_object* v_c_6372_){
_start:
{
lean_object* v_res_6373_; 
v_res_6373_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(v_upperBound_6362_, v___x_6363_, v_fixedParamPerms_6364_, v_next_6365_, v___x_6366_, v___x_6367_, v_inst_6368_, v_R_6369_, v_a_6370_, v_b_6371_, v_c_6372_);
lean_dec(v___x_6367_);
lean_dec(v___x_6366_);
lean_dec(v_next_6365_);
lean_dec_ref(v_fixedParamPerms_6364_);
lean_dec_ref(v___x_6363_);
lean_dec(v_upperBound_6362_);
return v_res_6373_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6431_; uint8_t v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; 
v___x_6431_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6432_ = 0;
v___x_6433_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6434_ = l_Lean_registerTraceClass(v___x_6431_, v___x_6432_, v___x_6433_);
return v___x_6434_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_6435_;
v_res_6435_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
stack->m_obj
 = v_res_6435_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6436_){
_start:
{
lean_object* v_res_6437_; 
v_res_6437_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6437_;
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
