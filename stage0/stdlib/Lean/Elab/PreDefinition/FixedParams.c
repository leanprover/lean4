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
v___x_123_ = l_Array_instInhabited___redArg();
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
lean_object* v___x_192_; lean_object* v___y_194_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_192_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_207_ = lean_array_get_size(v_graph_187_);
v___x_208_ = lean_nat_dec_lt(v_funIdx_183_, v___x_207_);
if (v___x_208_ == 0)
{
v___y_194_ = v_graph_187_;
goto v___jp_193_;
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
v___y_194_ = v___x_214_;
goto v___jp_193_;
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_info_198_; 
v___x_195_ = lean_array_get_size(v___y_194_);
v___x_196_ = lean_unsigned_to_nat(0u);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v___y_194_);
v_info_198_ = v___x_190_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___y_194_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_revDeps_188_);
v_info_198_ = v_reuseFailAlloc_206_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v_revDeps_200_; lean_object* v___x_201_; lean_object* v___x_202_; size_t v_sz_203_; size_t v___x_204_; lean_object* v___x_205_; 
lean_inc(v_paramIdx_184_);
v___x_199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setVarying_spec__2___redArg(v___x_195_, v_funIdx_183_, v_paramIdx_184_, v___x_196_, v_info_198_);
v_revDeps_200_ = lean_ctor_get(v___x_199_, 1);
v___x_201_ = lean_array_get_borrowed(v___x_192_, v_revDeps_200_, v_funIdx_183_);
v___x_202_ = lean_array_get(v___x_192_, v___x_201_, v_paramIdx_184_);
lean_dec(v_paramIdx_184_);
v_sz_203_ = lean_array_size(v___x_202_);
v___x_204_ = ((size_t)0ULL);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParams_Info_setVarying_spec__0(v_funIdx_183_, v___x_202_, v_sz_203_, v___x_204_, v___x_199_);
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
lean_dec_ref_known(v___x_335_, 1);
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
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___y_347_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_344_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_345_ = lean_box(0);
v___x_358_ = lean_array_get_size(v_graph_339_);
v___x_359_ = lean_nat_dec_lt(v_calleeIdx_321_, v___x_358_);
if (v___x_359_ == 0)
{
v___y_347_ = v_graph_339_;
goto v___jp_346_;
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
v___y_347_ = v___x_365_;
goto v___jp_346_;
}
}
v___jp_346_:
{
lean_object* v_info_349_; 
lean_inc_ref(v___y_347_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___y_347_);
v_info_349_ = v___x_342_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___y_347_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_revDeps_340_);
v_info_349_ = v_reuseFailAlloc_357_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_array_get_borrowed(v___x_344_, v___y_347_, v_callerIdx_323_);
v___x_351_ = lean_array_get_borrowed(v___x_345_, v___x_350_, v_paramIdx_324_);
if (lean_obj_tag(v___x_351_) == 1)
{
lean_object* v_val_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_graph_356_; 
lean_inc_ref(v___x_351_);
lean_dec_ref(v___y_347_);
v_val_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_val_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = lean_array_get_size(v_val_352_);
v___x_354_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_322_);
v___x_355_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParams_Info_setCallerParam_spec__2___redArg(v___x_353_, v_val_352_, v_calleeIdx_321_, v_argIdx_322_, v___x_354_, v_info_349_);
lean_dec(v_val_352_);
v_graph_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref(v_graph_356_);
v_info_327_ = v___x_355_;
v_graph_328_ = v_graph_356_;
goto v___jp_326_;
}
else
{
v_info_327_ = v_info_349_;
v_graph_328_ = v___y_347_;
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
lean_dec_ref_known(v_x_537_, 2);
return v_head_541_;
}
else
{
lean_object* v_head_542_; lean_object* v___x_543_; 
lean_inc(v_tail_540_);
v_head_542_ = lean_ctor_get(v_x_537_, 0);
lean_inc(v_head_542_);
lean_dec_ref_known(v_x_537_, 2);
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
lean_dec_ref_known(v_head_598_, 1);
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
lean_object* v___f_680_; lean_object* v___f_681_; lean_object* v___x_682_; uint8_t v_fst_684_; lean_object* v_mctx_685_; lean_object* v___y_703_; lean_object* v_mctx_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___f_680_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__0));
v___f_681_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_681_, 0, v_fvarId_677_);
v___x_682_ = lean_st_ref_get(v___y_678_);
v_mctx_708_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref_n(v_mctx_708_, 2);
lean_dec(v___x_682_);
v___x_709_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v_mctx_708_);
v___x_711_ = l_Lean_Expr_hasFVar(v_e_676_);
if (v___x_711_ == 0)
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_Expr_hasMVar(v_e_676_);
if (v___x_712_ == 0)
{
lean_dec_ref_known(v___x_710_, 2);
lean_dec_ref(v___f_681_);
lean_dec_ref(v_e_676_);
v_fst_684_ = v___x_712_;
v_mctx_685_ = v_mctx_708_;
goto v___jp_683_;
}
else
{
lean_object* v___x_713_; 
lean_dec_ref(v_mctx_708_);
v___x_713_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_681_, v___f_680_, v_e_676_, v___x_710_);
v___y_703_ = v___x_713_;
goto v___jp_702_;
}
}
else
{
lean_object* v___x_714_; 
lean_dec_ref(v_mctx_708_);
v___x_714_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_681_, v___f_680_, v_e_676_, v___x_710_);
v___y_703_ = v___x_714_;
goto v___jp_702_;
}
v___jp_683_:
{
lean_object* v___x_686_; lean_object* v_cache_687_; lean_object* v_zetaDeltaFVarIds_688_; lean_object* v_postponed_689_; lean_object* v_diag_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_700_; 
v___x_686_ = lean_st_ref_take(v___y_678_);
v_cache_687_ = lean_ctor_get(v___x_686_, 1);
v_zetaDeltaFVarIds_688_ = lean_ctor_get(v___x_686_, 2);
v_postponed_689_ = lean_ctor_get(v___x_686_, 3);
v_diag_690_ = lean_ctor_get(v___x_686_, 4);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v___x_686_, 0);
lean_dec(v_unused_701_);
v___x_692_ = v___x_686_;
v_isShared_693_ = v_isSharedCheck_700_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_diag_690_);
lean_inc(v_postponed_689_);
lean_inc(v_zetaDeltaFVarIds_688_);
lean_inc(v_cache_687_);
lean_dec(v___x_686_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_700_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_mctx_685_);
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_mctx_685_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_cache_687_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_zetaDeltaFVarIds_688_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_postponed_689_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v_diag_690_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_st_ref_put(v___y_678_, v___x_695_);
v___x_697_ = lean_box(v_fst_684_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
}
v___jp_702_:
{
lean_object* v_snd_704_; lean_object* v_fst_705_; lean_object* v_mctx_706_; uint8_t v___x_707_; 
v_snd_704_ = lean_ctor_get(v___y_703_, 1);
lean_inc(v_snd_704_);
v_fst_705_ = lean_ctor_get(v___y_703_, 0);
lean_inc(v_fst_705_);
lean_dec_ref(v___y_703_);
v_mctx_706_ = lean_ctor_get(v_snd_704_, 1);
lean_inc_ref(v_mctx_706_);
lean_dec(v_snd_704_);
v___x_707_ = lean_unbox(v_fst_705_);
lean_dec(v_fst_705_);
v_fst_684_ = v___x_707_;
v_mctx_685_ = v_mctx_706_;
goto v___jp_683_;
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
lean_object* v_a_825_; uint8_t v___x_829_; 
v___x_829_ = lean_nat_dec_lt(v_a_817_, v_upperBound_814_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v_a_817_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_b_818_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_array_fget_borrowed(v_xs_815_, v_a_817_);
lean_inc(v___y_822_);
lean_inc_ref(v___y_821_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___x_831_);
v___x_832_ = lean_infer_type(v___x_831_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = lean_array_fget_borrowed(v_xs_815_, v_next_816_);
v___x_835_ = l_Lean_Expr_fvarId_x21(v___x_834_);
v___x_836_ = l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg(v_a_833_, v___x_835_, v___y_820_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; uint8_t v___x_838_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
v___x_838_ = lean_unbox(v_a_837_);
lean_dec(v_a_837_);
if (v___x_838_ == 0)
{
v_a_825_ = v_b_818_;
goto v___jp_824_;
}
else
{
lean_object* v___x_839_; 
lean_inc(v_a_817_);
v___x_839_ = lean_array_push(v_b_818_, v_a_817_);
v_a_825_ = v___x_839_;
goto v___jp_824_;
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_b_818_);
lean_dec(v_a_817_);
v_a_840_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_836_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_836_);
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
v_a_848_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_832_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_832_);
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
v___jp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_nat_add(v_a_817_, v___x_826_);
lean_dec(v_a_817_);
v_a_817_ = v___x_827_;
v_b_818_ = v_a_825_;
goto _start;
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
lean_dec_ref_known(v___x_884_, 1);
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
lean_object* v___f_1008_; lean_object* v___x_27265__overap_1009_; lean_object* v___x_1010_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_27265__overap_1009_ = lean_panic_fn_borrowed(v___f_1008_, v_msg_1002_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1010_ = lean_apply_5(v___x_27265__overap_1009_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, lean_box(0));
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
lean_object* v_v_1046_; lean_object* v_value_1047_; lean_object* v___x_1048_; lean_object* v_bs_x27_1049_; lean_object* v___x_1050_; 
v_v_1046_ = lean_array_uget_borrowed(v_bs_1038_, v_i_1037_);
v_value_1047_ = lean_ctor_get(v_v_1046_, 7);
lean_inc_ref(v_value_1047_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v_bs_x27_1049_ = lean_array_uset(v_bs_1038_, v_i_1037_, v___x_1048_);
v___x_1050_ = l_Lean_Elab_getParamRevDeps(v_value_1047_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; size_t v___x_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = ((size_t)1ULL);
v___x_1053_ = lean_usize_add(v_i_1037_, v___x_1052_);
v___x_1054_ = lean_array_uset(v_bs_x27_1049_, v_i_1037_, v_a_1051_);
v_i_1037_ = v___x_1053_;
v_bs_1038_ = v___x_1054_;
goto _start;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v_bs_x27_1049_);
v_a_1056_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1050_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1050_);
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
lean_object* v___x_1081_; lean_object* v_env_1082_; uint8_t v___x_1083_; lean_object* v_env_1084_; lean_object* v___x_1085_; lean_object* v_toCold_1086_; lean_object* v_mctx_1087_; lean_object* v_lctx_1088_; lean_object* v_options_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1081_ = lean_st_ref_get(v___y_1079_);
v_env_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_env_1082_);
lean_dec(v___x_1081_);
v___x_1083_ = 0;
v_env_1084_ = l_Lean_Environment_setRecordingDeps(v_env_1082_, v___x_1083_);
v___x_1085_ = lean_st_ref_get(v___y_1077_);
v_toCold_1086_ = lean_ctor_get(v___y_1078_, 0);
v_mctx_1087_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_mctx_1087_);
lean_dec(v___x_1085_);
v_lctx_1088_ = lean_ctor_get(v___y_1076_, 2);
v_options_1089_ = lean_ctor_get(v_toCold_1086_, 2);
lean_inc_ref(v_options_1089_);
lean_inc_ref(v_lctx_1088_);
v___x_1090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1090_, 0, v_env_1084_);
lean_ctor_set(v___x_1090_, 1, v_mctx_1087_);
lean_ctor_set(v___x_1090_, 2, v_lctx_1088_);
lean_ctor_set(v___x_1090_, 3, v_options_1089_);
v___x_1091_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_msgData_1075_);
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
lean_object* v_ref_1112_; lean_object* v___x_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1159_; 
v_ref_1112_ = lean_ctor_get(v___y_1109_, 2);
v___x_1113_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1159_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1159_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v_traceState_1119_; lean_object* v_env_1120_; lean_object* v_nextMacroScope_1121_; lean_object* v_ngen_1122_; lean_object* v_auxDeclNGen_1123_; lean_object* v_cache_1124_; lean_object* v_recordedDeps_1125_; lean_object* v_messages_1126_; lean_object* v_infoState_1127_; lean_object* v_snapshotTasks_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1158_; 
v___x_1118_ = lean_st_ref_take(v___y_1110_);
v_traceState_1119_ = lean_ctor_get(v___x_1118_, 4);
v_env_1120_ = lean_ctor_get(v___x_1118_, 0);
v_nextMacroScope_1121_ = lean_ctor_get(v___x_1118_, 1);
v_ngen_1122_ = lean_ctor_get(v___x_1118_, 2);
v_auxDeclNGen_1123_ = lean_ctor_get(v___x_1118_, 3);
v_cache_1124_ = lean_ctor_get(v___x_1118_, 5);
v_recordedDeps_1125_ = lean_ctor_get(v___x_1118_, 6);
v_messages_1126_ = lean_ctor_get(v___x_1118_, 7);
v_infoState_1127_ = lean_ctor_get(v___x_1118_, 8);
v_snapshotTasks_1128_ = lean_ctor_get(v___x_1118_, 9);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1130_ = v___x_1118_;
v_isShared_1131_ = v_isSharedCheck_1158_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snapshotTasks_1128_);
lean_inc(v_infoState_1127_);
lean_inc(v_messages_1126_);
lean_inc(v_recordedDeps_1125_);
lean_inc(v_cache_1124_);
lean_inc(v_traceState_1119_);
lean_inc(v_auxDeclNGen_1123_);
lean_inc(v_ngen_1122_);
lean_inc(v_nextMacroScope_1121_);
lean_inc(v_env_1120_);
lean_dec(v___x_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1158_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint64_t v_tid_1132_; lean_object* v_traces_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1157_; 
v_tid_1132_ = lean_ctor_get_uint64(v_traceState_1119_, sizeof(void*)*1);
v_traces_1133_ = lean_ctor_get(v_traceState_1119_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_traceState_1119_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1135_ = v_traceState_1119_;
v_isShared_1136_ = v_isSharedCheck_1157_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_traces_1133_);
lean_dec(v_traceState_1119_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1157_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; double v___x_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_1140_ = 0;
v___x_1141_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_1142_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1142_, 0, v_cls_1105_);
lean_ctor_set(v___x_1142_, 1, v___x_1138_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
lean_ctor_set_float(v___x_1142_, sizeof(void*)*3, v___x_1139_);
lean_ctor_set_float(v___x_1142_, sizeof(void*)*3 + 8, v___x_1139_);
lean_ctor_set_uint8(v___x_1142_, sizeof(void*)*3 + 16, v___x_1140_);
v___x_1143_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_1144_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v_a_1114_);
lean_ctor_set(v___x_1144_, 2, v___x_1143_);
lean_inc(v_ref_1112_);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_ref_1112_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = l_Lean_PersistentArray_push___redArg(v_traces_1133_, v___x_1145_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1146_);
v___x_1148_ = v___x_1135_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1146_);
lean_ctor_set_uint64(v_reuseFailAlloc_1156_, sizeof(void*)*1, v_tid_1132_);
v___x_1148_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1150_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 4, v___x_1148_);
v___x_1150_ = v___x_1130_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_env_1120_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_nextMacroScope_1121_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_ngen_1122_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_auxDeclNGen_1123_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1155_, 5, v_cache_1124_);
lean_ctor_set(v_reuseFailAlloc_1155_, 6, v_recordedDeps_1125_);
lean_ctor_set(v_reuseFailAlloc_1155_, 7, v_messages_1126_);
lean_ctor_set(v_reuseFailAlloc_1155_, 8, v_infoState_1127_);
lean_ctor_set(v_reuseFailAlloc_1155_, 9, v_snapshotTasks_1128_);
v___x_1150_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = lean_st_ref_put(v___y_1110_, v___x_1150_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1137_);
v___x_1153_ = v___x_1116_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1137_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___boxed(lean_object* v_cls_1160_, lean_object* v_msg_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v_cls_1160_, v_msg_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_object* v_00_u03b1_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_apply_1(v_x_1169_, lean_box(0));
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(v_00_u03b1_1177_, v_x_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object* v_x_1185_, lean_object* v_x_1186_){
_start:
{
if (lean_obj_tag(v_x_1186_) == 0)
{
return v_x_1185_;
}
else
{
lean_object* v_key_1187_; lean_object* v_value_1188_; lean_object* v_tail_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1212_; 
v_key_1187_ = lean_ctor_get(v_x_1186_, 0);
v_value_1188_ = lean_ctor_get(v_x_1186_, 1);
v_tail_1189_ = lean_ctor_get(v_x_1186_, 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1186_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1191_ = v_x_1186_;
v_isShared_1192_ = v_isSharedCheck_1212_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_tail_1189_);
lean_inc(v_value_1188_);
lean_inc(v_key_1187_);
lean_dec(v_x_1186_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1212_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1193_; uint64_t v___x_1194_; uint64_t v___x_1195_; uint64_t v___x_1196_; uint64_t v_fold_1197_; uint64_t v___x_1198_; uint64_t v___x_1199_; uint64_t v___x_1200_; size_t v___x_1201_; size_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1193_ = lean_array_get_size(v_x_1185_);
v___x_1194_ = l_Lean_ExprStructEq_hash(v_key_1187_);
v___x_1195_ = 32ULL;
v___x_1196_ = lean_uint64_shift_right(v___x_1194_, v___x_1195_);
v_fold_1197_ = lean_uint64_xor(v___x_1194_, v___x_1196_);
v___x_1198_ = 16ULL;
v___x_1199_ = lean_uint64_shift_right(v_fold_1197_, v___x_1198_);
v___x_1200_ = lean_uint64_xor(v_fold_1197_, v___x_1199_);
v___x_1201_ = lean_uint64_to_usize(v___x_1200_);
v___x_1202_ = lean_usize_of_nat(v___x_1193_);
v___x_1203_ = ((size_t)1ULL);
v___x_1204_ = lean_usize_sub(v___x_1202_, v___x_1203_);
v___x_1205_ = lean_usize_land(v___x_1201_, v___x_1204_);
v___x_1206_ = lean_array_uget_borrowed(v_x_1185_, v___x_1205_);
lean_inc(v___x_1206_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 2, v___x_1206_);
v___x_1208_ = v___x_1191_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_key_1187_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_value_1188_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_array_uset(v_x_1185_, v___x_1205_, v___x_1208_);
v_x_1185_ = v___x_1209_;
v_x_1186_ = v_tail_1189_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object* v_i_1213_, lean_object* v_source_1214_, lean_object* v_target_1215_){
_start:
{
lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1216_ = lean_array_get_size(v_source_1214_);
v___x_1217_ = lean_nat_dec_lt(v_i_1213_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec_ref(v_source_1214_);
lean_dec(v_i_1213_);
return v_target_1215_;
}
else
{
lean_object* v_es_1218_; lean_object* v___x_1219_; lean_object* v_source_1220_; lean_object* v_target_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_es_1218_ = lean_array_fget(v_source_1214_, v_i_1213_);
v___x_1219_ = lean_box(0);
v_source_1220_ = lean_array_fset(v_source_1214_, v_i_1213_, v___x_1219_);
v_target_1221_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_target_1215_, v_es_1218_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_add(v_i_1213_, v___x_1222_);
lean_dec(v_i_1213_);
v_i_1213_ = v___x_1223_;
v_source_1214_ = v_source_1220_;
v_target_1215_ = v_target_1221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object* v_data_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_nbuckets_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1226_ = lean_array_get_size(v_data_1225_);
v___x_1227_ = lean_unsigned_to_nat(2u);
v_nbuckets_1228_ = lean_nat_mul(v___x_1226_, v___x_1227_);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_mk_array(v_nbuckets_1228_, v___x_1230_);
v___x_1232_ = lean_array_propagate_mark(v_data_1225_, v___x_1231_);
v___x_1233_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1229_, v_data_1225_, v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object* v_a_1234_, lean_object* v_b_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1236_) == 0)
{
lean_dec(v_b_1235_);
lean_dec_ref(v_a_1234_);
return v_x_1236_;
}
else
{
lean_object* v_key_1237_; lean_object* v_value_1238_; lean_object* v_tail_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1251_; 
v_key_1237_ = lean_ctor_get(v_x_1236_, 0);
v_value_1238_ = lean_ctor_get(v_x_1236_, 1);
v_tail_1239_ = lean_ctor_get(v_x_1236_, 2);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_x_1236_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1241_ = v_x_1236_;
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_tail_1239_);
lean_inc(v_value_1238_);
lean_inc(v_key_1237_);
lean_dec(v_x_1236_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1251_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Lean_ExprStructEq_beq(v_key_1237_, v_a_1234_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1234_, v_b_1235_, v_tail_1239_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 2, v___x_1244_);
v___x_1246_ = v___x_1241_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_key_1237_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_value_1238_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
else
{
lean_object* v___x_1249_; 
lean_dec(v_value_1238_);
lean_dec(v_key_1237_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_b_1235_);
lean_ctor_set(v___x_1241_, 0, v_a_1234_);
v___x_1249_ = v___x_1241_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1234_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_b_1235_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_tail_1239_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_a_1252_, lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1253_) == 0)
{
uint8_t v___x_1254_; 
v___x_1254_ = 0;
return v___x_1254_;
}
else
{
lean_object* v_key_1255_; lean_object* v_tail_1256_; uint8_t v___x_1257_; 
v_key_1255_ = lean_ctor_get(v_x_1253_, 0);
v_tail_1256_ = lean_ctor_get(v_x_1253_, 2);
v___x_1257_ = l_Lean_ExprStructEq_beq(v_key_1255_, v_a_1252_);
if (v___x_1257_ == 0)
{
v_x_1253_ = v_tail_1256_;
goto _start;
}
else
{
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_a_1259_, lean_object* v_x_1260_){
_start:
{
uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1259_, v_x_1260_);
lean_dec(v_x_1260_);
lean_dec_ref(v_a_1259_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_){
_start:
{
lean_object* v_size_1266_; lean_object* v_buckets_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1310_; 
v_size_1266_ = lean_ctor_get(v_m_1263_, 0);
v_buckets_1267_ = lean_ctor_get(v_m_1263_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_m_1263_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1269_ = v_m_1263_;
v_isShared_1270_ = v_isSharedCheck_1310_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_buckets_1267_);
lean_inc(v_size_1266_);
lean_dec(v_m_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1310_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; uint64_t v_fold_1275_; uint64_t v___x_1276_; uint64_t v___x_1277_; uint64_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; size_t v___x_1282_; size_t v___x_1283_; lean_object* v_bkt_1284_; uint8_t v___x_1285_; 
v___x_1271_ = lean_array_get_size(v_buckets_1267_);
v___x_1272_ = l_Lean_ExprStructEq_hash(v_a_1264_);
v___x_1273_ = 32ULL;
v___x_1274_ = lean_uint64_shift_right(v___x_1272_, v___x_1273_);
v_fold_1275_ = lean_uint64_xor(v___x_1272_, v___x_1274_);
v___x_1276_ = 16ULL;
v___x_1277_ = lean_uint64_shift_right(v_fold_1275_, v___x_1276_);
v___x_1278_ = lean_uint64_xor(v_fold_1275_, v___x_1277_);
v___x_1279_ = lean_uint64_to_usize(v___x_1278_);
v___x_1280_ = lean_usize_of_nat(v___x_1271_);
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_sub(v___x_1280_, v___x_1281_);
v___x_1283_ = lean_usize_land(v___x_1279_, v___x_1282_);
v_bkt_1284_ = lean_array_uget_borrowed(v_buckets_1267_, v___x_1283_);
v___x_1285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1264_, v_bkt_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v_size_x27_1287_; lean_object* v___x_1288_; lean_object* v_buckets_x27_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1286_ = lean_unsigned_to_nat(1u);
v_size_x27_1287_ = lean_nat_add(v_size_1266_, v___x_1286_);
lean_dec(v_size_1266_);
lean_inc(v_bkt_1284_);
v___x_1288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1288_, 0, v_a_1264_);
lean_ctor_set(v___x_1288_, 1, v_b_1265_);
lean_ctor_set(v___x_1288_, 2, v_bkt_1284_);
v_buckets_x27_1289_ = lean_array_uset(v_buckets_1267_, v___x_1283_, v___x_1288_);
v___x_1290_ = lean_unsigned_to_nat(4u);
v___x_1291_ = lean_nat_mul(v_size_x27_1287_, v___x_1290_);
v___x_1292_ = lean_unsigned_to_nat(3u);
v___x_1293_ = lean_nat_div(v___x_1291_, v___x_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_array_get_size(v_buckets_x27_1289_);
v___x_1295_ = lean_nat_dec_le(v___x_1293_, v___x_1294_);
lean_dec(v___x_1293_);
if (v___x_1295_ == 0)
{
lean_object* v_val_1296_; lean_object* v___x_1298_; 
v_val_1296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_buckets_x27_1289_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_val_1296_);
lean_ctor_set(v___x_1269_, 0, v_size_x27_1287_);
v___x_1298_ = v___x_1269_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_size_x27_1287_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_val_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
else
{
lean_object* v___x_1301_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v_buckets_x27_1289_);
lean_ctor_set(v___x_1269_, 0, v_size_x27_1287_);
v___x_1301_ = v___x_1269_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_size_x27_1287_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_buckets_x27_1289_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v___x_1303_; lean_object* v_buckets_x27_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_inc(v_bkt_1284_);
v___x_1303_ = lean_box(0);
v_buckets_x27_1304_ = lean_array_uset(v_buckets_1267_, v___x_1283_, v___x_1303_);
v___x_1305_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1264_, v_b_1265_, v_bkt_1284_);
v___x_1306_ = lean_array_uset(v_buckets_x27_1304_, v___x_1283_, v___x_1305_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 1, v___x_1306_);
v___x_1308_ = v___x_1269_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_size_1266_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1311_, lean_object* v_e_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1315_ = lean_st_ref_take(v_a_1311_);
v___x_1316_ = lean_box(0);
v___x_1317_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1315_, v_e_1312_, v_a_1313_);
v___x_1318_ = lean_st_ref_put(v_a_1311_, v___x_1317_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1319_, lean_object* v_e_1320_, lean_object* v_a_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1319_, v_e_1320_, v_a_1321_);
lean_dec(v_a_1319_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1324_, lean_object* v___y_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1325_);
v___x_1332_ = lean_apply_7(v_k_1324_, v_b_1326_, v___y_1325_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, lean_box(0));
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1333_, lean_object* v___y_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1333_, v___y_1334_, v_b_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1334_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1342_, uint8_t v_bi_1343_, lean_object* v_type_1344_, lean_object* v_k_1345_, uint8_t v_kind_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___f_1353_; lean_object* v___x_1354_; 
lean_inc(v___y_1347_);
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1353_, 0, v_k_1345_);
lean_closure_set(v___f_1353_, 1, v___y_1347_);
v___x_1354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1342_, v_bi_1343_, v_type_1344_, v___f_1353_, v_kind_1346_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
return v___x_1354_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1363_, lean_object* v_bi_1364_, lean_object* v_type_1365_, lean_object* v_k_1366_, lean_object* v_kind_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v_bi_boxed_1374_; uint8_t v_kind_boxed_1375_; lean_object* v_res_1376_; 
v_bi_boxed_1374_ = lean_unbox(v_bi_1364_);
v_kind_boxed_1375_ = lean_unbox(v_kind_1367_);
v_res_1376_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1363_, v_bi_boxed_1374_, v_type_1365_, v_k_1366_, v_kind_boxed_1375_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(lean_object* v___x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1377_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed(lean_object* v___x_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2(v___x_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1391_, lean_object* v_type_1392_, lean_object* v_val_1393_, lean_object* v_k_1394_, uint8_t v_nondep_1395_, uint8_t v_kind_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___f_1403_; lean_object* v___x_1404_; 
lean_inc(v___y_1397_);
v___f_1403_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1403_, 0, v_k_1394_);
lean_closure_set(v___f_1403_, 1, v___y_1397_);
v___x_1404_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1391_, v_type_1392_, v_val_1393_, v___f_1403_, v_nondep_1395_, v_kind_1396_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1404_) == 0)
{
return v___x_1404_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1413_, lean_object* v_type_1414_, lean_object* v_val_1415_, lean_object* v_k_1416_, lean_object* v_nondep_1417_, lean_object* v_kind_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
uint8_t v_nondep_boxed_1425_; uint8_t v_kind_boxed_1426_; lean_object* v_res_1427_; 
v_nondep_boxed_1425_ = lean_unbox(v_nondep_1417_);
v_kind_boxed_1426_ = lean_unbox(v_kind_1418_);
v_res_1427_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1413_, v_type_1414_, v_val_1415_, v_k_1416_, v_nondep_boxed_1425_, v_kind_boxed_1426_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1428_, lean_object* v_x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_apply_1(v_x_1429_, lean_box(0));
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1437_, v_x_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1444_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = l_Lean_maxRecDepthErrorMessage;
v___x_1451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1453_ = l_Lean_MessageData_ofFormat(v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1455_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1456_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v___x_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1457_){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_ref_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___y_1473_; lean_object* v_toCold_1482_; lean_object* v_currRecDepth_1483_; lean_object* v_ref_1484_; uint16_t v_optionFlags_1485_; uint8_t v_suppressElabErrors_1486_; uint8_t v_isRecordingDeps_1487_; lean_object* v_maxRecDepth_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_toCold_1482_ = lean_ctor_get(v___y_1469_, 0);
v_currRecDepth_1483_ = lean_ctor_get(v___y_1469_, 1);
v_ref_1484_ = lean_ctor_get(v___y_1469_, 2);
v_optionFlags_1485_ = lean_ctor_get_uint16(v___y_1469_, sizeof(void*)*3);
v_suppressElabErrors_1486_ = lean_ctor_get_uint8(v___y_1469_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1487_ = lean_ctor_get_uint8(v___y_1469_, sizeof(void*)*3 + 3);
v_maxRecDepth_1493_ = lean_ctor_get(v_toCold_1482_, 3);
v___x_1494_ = lean_unsigned_to_nat(0u);
v___x_1495_ = lean_nat_dec_eq(v_maxRecDepth_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_eq(v_currRecDepth_1483_, v_maxRecDepth_1493_);
if (v___x_1496_ == 0)
{
goto v___jp_1488_;
}
else
{
lean_object* v___x_1497_; 
lean_dec_ref(v_x_1465_);
lean_inc(v_ref_1484_);
v___x_1497_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1484_);
v___y_1473_ = v___x_1497_;
goto v___jp_1472_;
}
}
else
{
goto v___jp_1488_;
}
v___jp_1472_:
{
if (lean_obj_tag(v___y_1473_) == 0)
{
return v___y_1473_;
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
v_a_1474_ = lean_ctor_get(v___y_1473_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___y_1473_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___y_1473_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___y_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
v___jp_1488_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_unsigned_to_nat(1u);
v___x_1490_ = lean_nat_add(v_currRecDepth_1483_, v___x_1489_);
lean_inc(v_ref_1484_);
lean_inc_ref(v_toCold_1482_);
v___x_1491_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1491_, 0, v_toCold_1482_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
lean_ctor_set(v___x_1491_, 2, v_ref_1484_);
lean_ctor_set_uint16(v___x_1491_, sizeof(void*)*3, v_optionFlags_1485_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*3 + 2, v_suppressElabErrors_1486_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*3 + 3, v_isRecordingDeps_1487_);
lean_inc(v___y_1470_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
v___x_1492_ = lean_apply_6(v_x_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___x_1491_, v___y_1470_, lean_box(0));
v___y_1473_ = v___x_1492_;
goto v___jp_1472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1506_, lean_object* v_x_1507_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_box(0);
return v___x_1508_;
}
else
{
lean_object* v_key_1509_; lean_object* v_value_1510_; lean_object* v_tail_1511_; uint8_t v___x_1512_; 
v_key_1509_ = lean_ctor_get(v_x_1507_, 0);
v_value_1510_ = lean_ctor_get(v_x_1507_, 1);
v_tail_1511_ = lean_ctor_get(v_x_1507_, 2);
v___x_1512_ = l_Lean_ExprStructEq_beq(v_key_1509_, v_a_1506_);
if (v___x_1512_ == 0)
{
v_x_1507_ = v_tail_1511_;
goto _start;
}
else
{
lean_object* v___x_1514_; 
lean_inc(v_value_1510_);
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_value_1510_);
return v___x_1514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1515_, lean_object* v_x_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1515_, v_x_1516_);
lean_dec(v_x_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_buckets_1520_; lean_object* v___x_1521_; uint64_t v___x_1522_; uint64_t v___x_1523_; uint64_t v___x_1524_; uint64_t v_fold_1525_; uint64_t v___x_1526_; uint64_t v___x_1527_; uint64_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; size_t v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_buckets_1520_ = lean_ctor_get(v_m_1518_, 1);
v___x_1521_ = lean_array_get_size(v_buckets_1520_);
v___x_1522_ = l_Lean_ExprStructEq_hash(v_a_1519_);
v___x_1523_ = 32ULL;
v___x_1524_ = lean_uint64_shift_right(v___x_1522_, v___x_1523_);
v_fold_1525_ = lean_uint64_xor(v___x_1522_, v___x_1524_);
v___x_1526_ = 16ULL;
v___x_1527_ = lean_uint64_shift_right(v_fold_1525_, v___x_1526_);
v___x_1528_ = lean_uint64_xor(v_fold_1525_, v___x_1527_);
v___x_1529_ = lean_uint64_to_usize(v___x_1528_);
v___x_1530_ = lean_usize_of_nat(v___x_1521_);
v___x_1531_ = ((size_t)1ULL);
v___x_1532_ = lean_usize_sub(v___x_1530_, v___x_1531_);
v___x_1533_ = lean_usize_land(v___x_1529_, v___x_1532_);
v___x_1534_ = lean_array_uget_borrowed(v_buckets_1520_, v___x_1533_);
v___x_1535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1519_, v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1536_, v_a_1537_);
lean_dec_ref(v_a_1537_);
lean_dec_ref(v_m_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_1539_, lean_object* v_pre_1540_, lean_object* v_post_1541_, lean_object* v_usedLetOnly_1542_, lean_object* v_skipConstInApp_1543_, lean_object* v_skipInstances_1544_, lean_object* v_body_1545_, lean_object* v_x_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
uint8_t v_usedLetOnly_boxed_1553_; uint8_t v_skipConstInApp_boxed_1554_; uint8_t v_skipInstances_boxed_1555_; lean_object* v_res_1556_; 
v_usedLetOnly_boxed_1553_ = lean_unbox(v_usedLetOnly_1542_);
v_skipConstInApp_boxed_1554_ = lean_unbox(v_skipConstInApp_1543_);
v_skipInstances_boxed_1555_ = lean_unbox(v_skipInstances_1544_);
v_res_1556_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_1539_, v_pre_1540_, v_post_1541_, v_usedLetOnly_boxed_1553_, v_skipConstInApp_boxed_1554_, v_skipInstances_boxed_1555_, v_body_1545_, v_x_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1560_, lean_object* v_pre_1561_, lean_object* v_post_1562_, uint8_t v_usedLetOnly_1563_, uint8_t v_skipConstInApp_1564_, uint8_t v_skipInstances_1565_, lean_object* v_body_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_array_push(v_fvars_1560_, v_x_1567_);
v___x_1575_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1561_, v_post_1562_, v_usedLetOnly_1563_, v_skipConstInApp_1564_, v_skipInstances_1565_, v___x_1574_, v_body_1566_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1576_, lean_object* v_pre_1577_, lean_object* v_post_1578_, lean_object* v_usedLetOnly_1579_, lean_object* v_skipConstInApp_1580_, lean_object* v_skipInstances_1581_, lean_object* v_body_1582_, lean_object* v_x_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v_usedLetOnly_boxed_1590_; uint8_t v_skipConstInApp_boxed_1591_; uint8_t v_skipInstances_boxed_1592_; lean_object* v_res_1593_; 
v_usedLetOnly_boxed_1590_ = lean_unbox(v_usedLetOnly_1579_);
v_skipConstInApp_boxed_1591_ = lean_unbox(v_skipConstInApp_1580_);
v_skipInstances_boxed_1592_ = lean_unbox(v_skipInstances_1581_);
v_res_1593_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1576_, v_pre_1577_, v_post_1578_, v_usedLetOnly_boxed_1590_, v_skipConstInApp_boxed_1591_, v_skipInstances_boxed_1592_, v_body_1582_, v_x_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1594_, lean_object* v_post_1595_, uint8_t v_usedLetOnly_1596_, uint8_t v_skipConstInApp_1597_, uint8_t v_skipInstances_1598_, lean_object* v_e_1599_, lean_object* v_a_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; 
lean_inc_ref(v_post_1595_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1603_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc_ref(v_e_1599_);
v___x_1606_ = lean_apply_6(v_post_1595_, v_e_1599_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, lean_box(0));
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1625_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1625_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1625_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
switch(lean_obj_tag(v_a_1607_))
{
case 0:
{
lean_object* v_e_1611_; lean_object* v___x_1613_; 
lean_dec_ref(v_e_1599_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
v_e_1611_ = lean_ctor_get(v_a_1607_, 0);
lean_inc_ref(v_e_1611_);
lean_dec_ref_known(v_a_1607_, 1);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v_e_1611_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_e_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
case 1:
{
lean_object* v_e_1615_; lean_object* v___x_1616_; 
lean_del_object(v___x_1609_);
lean_dec_ref(v_e_1599_);
v_e_1615_ = lean_ctor_get(v_a_1607_, 0);
lean_inc_ref(v_e_1615_);
lean_dec_ref_known(v_a_1607_, 1);
v___x_1616_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1594_, v_post_1595_, v_usedLetOnly_1596_, v_skipConstInApp_1597_, v_skipInstances_1598_, v_e_1615_, v_a_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
return v___x_1616_;
}
default: 
{
lean_object* v_e_x3f_1617_; 
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
v_e_x3f_1617_ = lean_ctor_get(v_a_1607_, 0);
lean_inc(v_e_x3f_1617_);
lean_dec_ref_known(v_a_1607_, 1);
if (lean_obj_tag(v_e_x3f_1617_) == 0)
{
lean_object* v___x_1619_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v_e_1599_);
v___x_1619_ = v___x_1609_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_e_1599_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_object* v_val_1621_; lean_object* v___x_1623_; 
lean_dec_ref(v_e_1599_);
v_val_1621_ = lean_ctor_get(v_e_x3f_1617_, 0);
lean_inc(v_val_1621_);
lean_dec_ref_known(v_e_x3f_1617_, 1);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v_val_1621_);
v___x_1623_ = v___x_1609_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_val_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_e_1599_);
lean_dec_ref(v_post_1595_);
lean_dec_ref(v_pre_1594_);
v_a_1626_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1606_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1606_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1634_, lean_object* v_post_1635_, uint8_t v_usedLetOnly_1636_, uint8_t v_skipConstInApp_1637_, uint8_t v_skipInstances_1638_, lean_object* v_fvars_1639_, lean_object* v_e_1640_, lean_object* v_a_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
if (lean_obj_tag(v_e_1640_) == 6)
{
lean_object* v_binderName_1647_; lean_object* v_binderType_1648_; lean_object* v_body_1649_; uint8_t v_binderInfo_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___f_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_binderName_1647_ = lean_ctor_get(v_e_1640_, 0);
lean_inc(v_binderName_1647_);
v_binderType_1648_ = lean_ctor_get(v_e_1640_, 1);
lean_inc_ref(v_binderType_1648_);
v_body_1649_ = lean_ctor_get(v_e_1640_, 2);
lean_inc_ref(v_body_1649_);
v_binderInfo_1650_ = lean_ctor_get_uint8(v_e_1640_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1640_, 3);
v___x_1651_ = lean_box(v_usedLetOnly_1636_);
v___x_1652_ = lean_box(v_skipConstInApp_1637_);
v___x_1653_ = lean_box(v_skipInstances_1638_);
lean_inc_ref(v_post_1635_);
lean_inc_ref(v_pre_1634_);
lean_inc_ref(v_fvars_1639_);
v___f_1654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1654_, 0, v_fvars_1639_);
lean_closure_set(v___f_1654_, 1, v_pre_1634_);
lean_closure_set(v___f_1654_, 2, v_post_1635_);
lean_closure_set(v___f_1654_, 3, v___x_1651_);
lean_closure_set(v___f_1654_, 4, v___x_1652_);
lean_closure_set(v___f_1654_, 5, v___x_1653_);
lean_closure_set(v___f_1654_, 6, v_body_1649_);
v___x_1655_ = lean_expr_instantiate_rev(v_binderType_1648_, v_fvars_1639_);
lean_dec_ref(v_fvars_1639_);
lean_dec_ref(v_binderType_1648_);
v___x_1656_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1634_, v_post_1635_, v_usedLetOnly_1636_, v_skipConstInApp_1637_, v_skipInstances_1638_, v___x_1655_, v_a_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = 0;
v___x_1659_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1647_, v_binderInfo_1650_, v_a_1657_, v___f_1654_, v___x_1658_, v_a_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1659_;
}
else
{
lean_dec_ref(v___f_1654_);
lean_dec(v_binderName_1647_);
return v___x_1656_;
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_expr_instantiate_rev(v_e_1640_, v_fvars_1639_);
lean_dec_ref(v_e_1640_);
lean_inc_ref(v_post_1635_);
lean_inc_ref(v_pre_1634_);
v___x_1661_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1634_, v_post_1635_, v_usedLetOnly_1636_, v_skipConstInApp_1637_, v_skipInstances_1638_, v___x_1660_, v_a_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; uint8_t v___x_1663_; uint8_t v___x_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1663_ = 0;
v___x_1664_ = 1;
v___x_1665_ = 1;
v___x_1666_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1639_, v_a_1662_, v___x_1663_, v_usedLetOnly_1636_, v___x_1663_, v___x_1664_, v___x_1665_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec_ref(v_fvars_1639_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1634_, v_post_1635_, v_usedLetOnly_1636_, v_skipConstInApp_1637_, v_skipInstances_1638_, v_a_1667_, v_a_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1668_;
}
else
{
lean_dec_ref(v_post_1635_);
lean_dec_ref(v_pre_1634_);
return v___x_1666_;
}
}
else
{
lean_dec_ref(v_fvars_1639_);
lean_dec_ref(v_post_1635_);
lean_dec_ref(v_pre_1634_);
return v___x_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1669_, lean_object* v_pre_1670_, lean_object* v_post_1671_, uint8_t v_usedLetOnly_1672_, uint8_t v_skipConstInApp_1673_, uint8_t v_skipInstances_1674_, lean_object* v_body_1675_, lean_object* v_x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_array_push(v_fvars_1669_, v_x_1676_);
v___x_1684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1670_, v_post_1671_, v_usedLetOnly_1672_, v_skipConstInApp_1673_, v_skipInstances_1674_, v___x_1683_, v_body_1675_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1685_, lean_object* v_pre_1686_, lean_object* v_post_1687_, lean_object* v_usedLetOnly_1688_, lean_object* v_skipConstInApp_1689_, lean_object* v_skipInstances_1690_, lean_object* v_body_1691_, lean_object* v_x_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
uint8_t v_usedLetOnly_boxed_1699_; uint8_t v_skipConstInApp_boxed_1700_; uint8_t v_skipInstances_boxed_1701_; lean_object* v_res_1702_; 
v_usedLetOnly_boxed_1699_ = lean_unbox(v_usedLetOnly_1688_);
v_skipConstInApp_boxed_1700_ = lean_unbox(v_skipConstInApp_1689_);
v_skipInstances_boxed_1701_ = lean_unbox(v_skipInstances_1690_);
v_res_1702_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1685_, v_pre_1686_, v_post_1687_, v_usedLetOnly_boxed_1699_, v_skipConstInApp_boxed_1700_, v_skipInstances_boxed_1701_, v_body_1691_, v_x_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1703_, lean_object* v_post_1704_, uint8_t v_usedLetOnly_1705_, uint8_t v_skipConstInApp_1706_, uint8_t v_skipInstances_1707_, lean_object* v_fvars_1708_, lean_object* v_e_1709_, lean_object* v_a_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
if (lean_obj_tag(v_e_1709_) == 8)
{
lean_object* v_declName_1716_; lean_object* v_type_1717_; lean_object* v_value_1718_; lean_object* v_body_1719_; uint8_t v_nondep_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_declName_1716_ = lean_ctor_get(v_e_1709_, 0);
lean_inc(v_declName_1716_);
v_type_1717_ = lean_ctor_get(v_e_1709_, 1);
lean_inc_ref(v_type_1717_);
v_value_1718_ = lean_ctor_get(v_e_1709_, 2);
lean_inc_ref(v_value_1718_);
v_body_1719_ = lean_ctor_get(v_e_1709_, 3);
lean_inc_ref(v_body_1719_);
v_nondep_1720_ = lean_ctor_get_uint8(v_e_1709_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1709_, 4);
v___x_1721_ = lean_box(v_usedLetOnly_1705_);
v___x_1722_ = lean_box(v_skipConstInApp_1706_);
v___x_1723_ = lean_box(v_skipInstances_1707_);
lean_inc_ref_n(v_post_1704_, 2);
lean_inc_ref_n(v_pre_1703_, 2);
lean_inc_ref(v_fvars_1708_);
v___f_1724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1724_, 0, v_fvars_1708_);
lean_closure_set(v___f_1724_, 1, v_pre_1703_);
lean_closure_set(v___f_1724_, 2, v_post_1704_);
lean_closure_set(v___f_1724_, 3, v___x_1721_);
lean_closure_set(v___f_1724_, 4, v___x_1722_);
lean_closure_set(v___f_1724_, 5, v___x_1723_);
lean_closure_set(v___f_1724_, 6, v_body_1719_);
v___x_1725_ = lean_expr_instantiate_rev(v_type_1717_, v_fvars_1708_);
lean_dec_ref(v_type_1717_);
v___x_1726_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1703_, v_post_1704_, v_usedLetOnly_1705_, v_skipConstInApp_1706_, v_skipInstances_1707_, v___x_1725_, v_a_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = lean_expr_instantiate_rev(v_value_1718_, v_fvars_1708_);
lean_dec_ref(v_fvars_1708_);
lean_dec_ref(v_value_1718_);
v___x_1729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1703_, v_post_1704_, v_usedLetOnly_1705_, v_skipConstInApp_1706_, v_skipInstances_1707_, v___x_1728_, v_a_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = 0;
v___x_1732_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1716_, v_a_1727_, v_a_1730_, v___f_1724_, v_nondep_1720_, v___x_1731_, v_a_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1732_;
}
else
{
lean_dec(v_a_1727_);
lean_dec_ref(v___f_1724_);
lean_dec(v_declName_1716_);
return v___x_1729_;
}
}
else
{
lean_dec_ref(v___f_1724_);
lean_dec_ref(v_value_1718_);
lean_dec(v_declName_1716_);
lean_dec_ref(v_fvars_1708_);
lean_dec_ref(v_post_1704_);
lean_dec_ref(v_pre_1703_);
return v___x_1726_;
}
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = lean_expr_instantiate_rev(v_e_1709_, v_fvars_1708_);
lean_dec_ref(v_e_1709_);
lean_inc_ref(v_post_1704_);
lean_inc_ref(v_pre_1703_);
v___x_1734_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1703_, v_post_1704_, v_usedLetOnly_1705_, v_skipConstInApp_1706_, v_skipInstances_1707_, v___x_1733_, v_a_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; uint8_t v___x_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = 0;
v___x_1737_ = 1;
v___x_1738_ = l_Lean_Meta_mkLetFVars(v_fvars_1708_, v_a_1735_, v_usedLetOnly_1705_, v___x_1736_, v___x_1737_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec_ref(v_fvars_1708_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1703_, v_post_1704_, v_usedLetOnly_1705_, v_skipConstInApp_1706_, v_skipInstances_1707_, v_a_1739_, v_a_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1740_;
}
else
{
lean_dec_ref(v_post_1704_);
lean_dec_ref(v_pre_1703_);
return v___x_1738_;
}
}
else
{
lean_dec_ref(v_fvars_1708_);
lean_dec_ref(v_post_1704_);
lean_dec_ref(v_pre_1703_);
return v___x_1734_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1741_; lean_object* v_dummy_1742_; 
v___x_1741_ = lean_box(0);
v_dummy_1742_ = l_Lean_Expr_sort___override(v___x_1741_);
return v_dummy_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1743_, lean_object* v_post_1744_, uint8_t v_usedLetOnly_1745_, uint8_t v_skipConstInApp_1746_, uint8_t v_skipInstances_1747_, size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_bs_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_usize_dec_lt(v_i_1749_, v_sz_1748_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_dec_ref(v_post_1744_);
lean_dec_ref(v_pre_1743_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_bs_1750_);
return v___x_1758_;
}
else
{
lean_object* v_v_1759_; lean_object* v___x_1760_; lean_object* v_bs_x27_1761_; lean_object* v___x_1762_; 
v_v_1759_ = lean_array_uget(v_bs_1750_, v_i_1749_);
v___x_1760_ = lean_unsigned_to_nat(0u);
v_bs_x27_1761_ = lean_array_uset(v_bs_1750_, v_i_1749_, v___x_1760_);
lean_inc_ref(v_post_1744_);
lean_inc_ref(v_pre_1743_);
v___x_1762_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1743_, v_post_1744_, v_usedLetOnly_1745_, v_skipConstInApp_1746_, v_skipInstances_1747_, v_v_1759_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; size_t v___x_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1749_, v___x_1764_);
v___x_1766_ = lean_array_uset(v_bs_x27_1761_, v_i_1749_, v_a_1763_);
v_i_1749_ = v___x_1765_;
v_bs_1750_ = v___x_1766_;
goto _start;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_bs_x27_1761_);
lean_dec_ref(v_post_1744_);
lean_dec_ref(v_pre_1743_);
v_a_1768_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1762_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1762_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1776_, lean_object* v_post_1777_, uint8_t v_usedLetOnly_1778_, uint8_t v_skipConstInApp_1779_, uint8_t v_skipInstances_1780_, lean_object* v___x_1781_, lean_object* v___y_1782_, lean_object* v_b_1783_, lean_object* v_a_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1776_, v_post_1777_, v_usedLetOnly_1778_, v_skipConstInApp_1779_, v_skipInstances_1780_, v___x_1781_, v___y_1782_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1800_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1800_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1800_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1795_ = lean_array_fset(v_b_1783_, v_a_1784_, v_a_1791_);
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1796_);
v___x_1798_ = v___x_1793_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref(v_b_1783_);
v_a_1801_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1790_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1790_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1809_, lean_object* v_post_1810_, lean_object* v_usedLetOnly_1811_, lean_object* v_skipConstInApp_1812_, lean_object* v_skipInstances_1813_, lean_object* v___x_1814_, lean_object* v___y_1815_, lean_object* v_b_1816_, lean_object* v_a_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v_usedLetOnly_boxed_1823_; uint8_t v_skipConstInApp_boxed_1824_; uint8_t v_skipInstances_boxed_1825_; lean_object* v_res_1826_; 
v_usedLetOnly_boxed_1823_ = lean_unbox(v_usedLetOnly_1811_);
v_skipConstInApp_boxed_1824_ = lean_unbox(v_skipConstInApp_1812_);
v_skipInstances_boxed_1825_ = lean_unbox(v_skipInstances_1813_);
v_res_1826_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1809_, v_post_1810_, v_usedLetOnly_boxed_1823_, v_skipConstInApp_boxed_1824_, v_skipInstances_boxed_1825_, v___x_1814_, v___y_1815_, v_b_1816_, v_a_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v_a_1817_);
lean_dec(v___y_1815_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1827_, lean_object* v___x_1828_, lean_object* v_pre_1829_, lean_object* v_post_1830_, uint8_t v_usedLetOnly_1831_, uint8_t v_skipConstInApp_1832_, uint8_t v_skipInstances_1833_, lean_object* v_a_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___y_1843_; uint8_t v___x_1866_; 
v___x_1866_ = lean_nat_dec_lt(v_a_1834_, v_upperBound_1827_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec(v_a_1834_);
lean_dec_ref(v_post_1830_);
lean_dec_ref(v_pre_1829_);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_b_1835_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1868_ = lean_array_fget_borrowed(v_b_1835_, v_a_1834_);
v___x_1869_ = lean_array_get_size(v___x_1828_);
v___x_1870_ = lean_nat_dec_lt(v_a_1834_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___f_1874_; 
lean_inc(v___x_1868_);
v___x_1871_ = lean_box(v_usedLetOnly_1831_);
v___x_1872_ = lean_box(v_skipConstInApp_1832_);
v___x_1873_ = lean_box(v_skipInstances_1833_);
lean_inc(v_a_1834_);
lean_inc(v___y_1836_);
lean_inc_ref(v_post_1830_);
lean_inc_ref(v_pre_1829_);
v___f_1874_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1874_, 0, v_pre_1829_);
lean_closure_set(v___f_1874_, 1, v_post_1830_);
lean_closure_set(v___f_1874_, 2, v___x_1871_);
lean_closure_set(v___f_1874_, 3, v___x_1872_);
lean_closure_set(v___f_1874_, 4, v___x_1873_);
lean_closure_set(v___f_1874_, 5, v___x_1868_);
lean_closure_set(v___f_1874_, 6, v___y_1836_);
lean_closure_set(v___f_1874_, 7, v_b_1835_);
lean_closure_set(v___f_1874_, 8, v_a_1834_);
v___y_1843_ = v___f_1874_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1875_; uint8_t v_isInstance_1876_; 
v___x_1875_ = lean_array_fget_borrowed(v___x_1828_, v_a_1834_);
v_isInstance_1876_ = lean_ctor_get_uint8(v___x_1875_, sizeof(void*)*1 + 4);
if (v_isInstance_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___f_1880_; 
lean_inc(v___x_1868_);
v___x_1877_ = lean_box(v_usedLetOnly_1831_);
v___x_1878_ = lean_box(v_skipConstInApp_1832_);
v___x_1879_ = lean_box(v_skipInstances_1833_);
lean_inc(v_a_1834_);
lean_inc(v___y_1836_);
lean_inc_ref(v_post_1830_);
lean_inc_ref(v_pre_1829_);
v___f_1880_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1880_, 0, v_pre_1829_);
lean_closure_set(v___f_1880_, 1, v_post_1830_);
lean_closure_set(v___f_1880_, 2, v___x_1877_);
lean_closure_set(v___f_1880_, 3, v___x_1878_);
lean_closure_set(v___f_1880_, 4, v___x_1879_);
lean_closure_set(v___f_1880_, 5, v___x_1868_);
lean_closure_set(v___f_1880_, 6, v___y_1836_);
lean_closure_set(v___f_1880_, 7, v_b_1835_);
lean_closure_set(v___f_1880_, 8, v_a_1834_);
v___y_1843_ = v___f_1880_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1881_; lean_object* v___f_1882_; 
v___x_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_b_1835_);
v___f_1882_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1882_, 0, v___x_1881_);
v___y_1843_ = v___f_1882_;
goto v___jp_1842_;
}
}
}
v___jp_1842_:
{
lean_object* v___x_1844_; 
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
v___x_1844_ = lean_apply_5(v___y_1843_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, lean_box(0));
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1857_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1857_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1857_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
if (lean_obj_tag(v_a_1845_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; 
lean_dec(v_a_1834_);
lean_dec_ref(v_post_1830_);
lean_dec_ref(v_pre_1829_);
v_a_1849_ = lean_ctor_get(v_a_1845_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v_a_1845_, 1);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v_a_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_del_object(v___x_1847_);
v_a_1853_ = lean_ctor_get(v_a_1845_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v_a_1845_, 1);
v___x_1854_ = lean_unsigned_to_nat(1u);
v___x_1855_ = lean_nat_add(v_a_1834_, v___x_1854_);
lean_dec(v_a_1834_);
v_a_1834_ = v___x_1855_;
v_b_1835_ = v_a_1853_;
goto _start;
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_a_1834_);
lean_dec_ref(v_post_1830_);
lean_dec_ref(v_pre_1829_);
v_a_1858_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1844_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1844_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1883_, lean_object* v_pre_1884_, lean_object* v_post_1885_, uint8_t v_usedLetOnly_1886_, uint8_t v_skipConstInApp_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_f_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; 
if (lean_obj_tag(v_x_1888_) == 5)
{
lean_object* v_fn_1946_; lean_object* v_arg_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_fn_1946_ = lean_ctor_get(v_x_1888_, 0);
lean_inc_ref(v_fn_1946_);
v_arg_1947_ = lean_ctor_get(v_x_1888_, 1);
lean_inc_ref(v_arg_1947_);
lean_dec_ref_known(v_x_1888_, 2);
v___x_1948_ = lean_array_set(v_x_1889_, v_x_1890_, v_arg_1947_);
v___x_1949_ = lean_unsigned_to_nat(1u);
v___x_1950_ = lean_nat_sub(v_x_1890_, v___x_1949_);
lean_dec(v_x_1890_);
v_x_1888_ = v_fn_1946_;
v_x_1889_ = v___x_1948_;
v_x_1890_ = v___x_1950_;
goto _start;
}
else
{
lean_dec(v_x_1890_);
if (v_skipConstInApp_1887_ == 0)
{
goto v___jp_1943_;
}
else
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Lean_Expr_isConst(v_x_1888_);
if (v___x_1952_ == 0)
{
goto v___jp_1943_;
}
else
{
v_f_1898_ = v_x_1888_;
v___y_1899_ = v___y_1891_;
v___y_1900_ = v___y_1892_;
v___y_1901_ = v___y_1893_;
v___y_1902_ = v___y_1894_;
v___y_1903_ = v___y_1895_;
goto v___jp_1897_;
}
}
}
v___jp_1897_:
{
if (v_skipInstances_1883_ == 0)
{
size_t v_sz_1904_; size_t v___x_1905_; lean_object* v___x_1906_; 
v_sz_1904_ = lean_array_size(v_x_1889_);
v___x_1905_ = ((size_t)0ULL);
lean_inc_ref(v_post_1885_);
lean_inc_ref(v_pre_1884_);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1884_, v_post_1885_, v_usedLetOnly_1886_, v_skipConstInApp_1887_, v_skipInstances_1883_, v_sz_1904_, v___x_1905_, v_x_1889_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = l_Lean_mkAppN(v_f_1898_, v_a_1907_);
lean_dec(v_a_1907_);
v___x_1909_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1884_, v_post_1885_, v_usedLetOnly_1886_, v_skipConstInApp_1887_, v_skipInstances_1883_, v___x_1908_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1909_;
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref(v_f_1898_);
lean_dec_ref(v_post_1885_);
lean_dec_ref(v_pre_1884_);
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
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_array_get_size(v_x_1889_);
lean_inc_ref(v_f_1898_);
v___x_1919_ = l_Lean_Meta_getFunInfoNArgs(v_f_1898_, v___x_1918_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v_paramInfo_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_paramInfo_1921_ = lean_ctor_get(v_a_1920_, 0);
lean_inc_ref(v_paramInfo_1921_);
lean_dec(v_a_1920_);
v___x_1922_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1885_);
lean_inc_ref(v_pre_1884_);
v___x_1923_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1918_, v_paramInfo_1921_, v_pre_1884_, v_post_1885_, v_usedLetOnly_1886_, v_skipConstInApp_1887_, v_skipInstances_1883_, v___x_1922_, v_x_1889_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec_ref(v_paramInfo_1921_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = l_Lean_mkAppN(v_f_1898_, v_a_1924_);
lean_dec(v_a_1924_);
v___x_1926_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1884_, v_post_1885_, v_usedLetOnly_1886_, v_skipConstInApp_1887_, v_skipInstances_1883_, v___x_1925_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
return v___x_1926_;
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_f_1898_);
lean_dec_ref(v_post_1885_);
lean_dec_ref(v_pre_1884_);
v_a_1927_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1923_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1923_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref(v_f_1898_);
lean_dec_ref(v_x_1889_);
lean_dec_ref(v_post_1885_);
lean_dec_ref(v_pre_1884_);
v_a_1935_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1919_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1919_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
v___jp_1943_:
{
lean_object* v___x_1944_; 
lean_inc_ref(v_post_1885_);
lean_inc_ref(v_pre_1884_);
v___x_1944_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1884_, v_post_1885_, v_usedLetOnly_1886_, v_skipConstInApp_1887_, v_skipInstances_1883_, v_x_1888_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1944_, 1);
v_f_1898_ = v_a_1945_;
v___y_1899_ = v___y_1891_;
v___y_1900_ = v___y_1892_;
v___y_1901_ = v___y_1893_;
v___y_1902_ = v___y_1894_;
v___y_1903_ = v___y_1895_;
goto v___jp_1897_;
}
else
{
lean_dec_ref(v_x_1889_);
lean_dec_ref(v_post_1885_);
lean_dec_ref(v_pre_1884_);
return v___x_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1953_, lean_object* v_pre_1954_, lean_object* v_e_1955_, lean_object* v_post_1956_, uint8_t v_usedLetOnly_1957_, uint8_t v_skipConstInApp_1958_, uint8_t v_skipInstances_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_Core_checkSystem(v___x_1953_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v___x_1967_; 
lean_dec_ref_known(v___x_1966_, 1);
lean_inc_ref(v_pre_1954_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
lean_inc_ref(v_e_1955_);
v___x_1967_ = lean_apply_6(v_pre_1954_, v_e_1955_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, lean_box(0));
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2016_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_2016_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2016_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___y_1973_; 
switch(lean_obj_tag(v_a_1968_))
{
case 0:
{
lean_object* v_e_2008_; lean_object* v___x_2010_; 
lean_dec_ref(v_post_1956_);
lean_dec_ref(v_e_1955_);
lean_dec_ref(v_pre_1954_);
v_e_2008_ = lean_ctor_get(v_a_1968_, 0);
lean_inc_ref(v_e_2008_);
lean_dec_ref_known(v_a_1968_, 1);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_e_2008_);
v___x_2010_ = v___x_1970_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_e_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
case 1:
{
lean_object* v_e_2012_; lean_object* v___x_2013_; 
lean_del_object(v___x_1970_);
lean_dec_ref(v_e_1955_);
v_e_2012_ = lean_ctor_get(v_a_1968_, 0);
lean_inc_ref(v_e_2012_);
lean_dec_ref_known(v_a_1968_, 1);
v___x_2013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v_e_2012_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_2013_;
}
default: 
{
lean_object* v_e_x3f_2014_; 
lean_del_object(v___x_1970_);
v_e_x3f_2014_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_e_x3f_2014_);
lean_dec_ref_known(v_a_1968_, 1);
if (lean_obj_tag(v_e_x3f_2014_) == 0)
{
v___y_1973_ = v_e_1955_;
goto v___jp_1972_;
}
else
{
lean_object* v_val_2015_; 
lean_dec_ref(v_e_1955_);
v_val_2015_ = lean_ctor_get(v_e_x3f_2014_, 0);
lean_inc(v_val_2015_);
lean_dec_ref_known(v_e_x3f_2014_, 1);
v___y_1973_ = v_val_2015_;
goto v___jp_1972_;
}
}
}
v___jp_1972_:
{
switch(lean_obj_tag(v___y_1973_))
{
case 7:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1975_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v___x_1974_, v___y_1973_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1975_;
}
case 6:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v___x_1976_, v___y_1973_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1977_;
}
case 8:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v___x_1978_, v___y_1973_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1979_;
}
case 5:
{
lean_object* v_dummy_1980_; lean_object* v_nargs_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_dummy_1980_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1981_ = l_Lean_Expr_getAppNumArgs(v___y_1973_);
lean_inc(v_nargs_1981_);
v___x_1982_ = lean_mk_array(v_nargs_1981_, v_dummy_1980_);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_sub(v_nargs_1981_, v___x_1983_);
lean_dec(v_nargs_1981_);
v___x_1985_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1959_, v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v___y_1973_, v___x_1982_, v___x_1984_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1985_;
}
case 10:
{
lean_object* v_data_1986_; lean_object* v_expr_1987_; lean_object* v___x_1988_; 
v_data_1986_ = lean_ctor_get(v___y_1973_, 0);
v_expr_1987_ = lean_ctor_get(v___y_1973_, 1);
lean_inc_ref(v_expr_1987_);
lean_inc_ref(v_post_1956_);
lean_inc_ref(v_pre_1954_);
v___x_1988_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v_expr_1987_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; size_t v___x_1990_; size_t v___x_1991_; uint8_t v___x_1992_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = lean_ptr_addr(v_expr_1987_);
v___x_1991_ = lean_ptr_addr(v_a_1989_);
v___x_1992_ = lean_usize_dec_eq(v___x_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_inc(v_data_1986_);
lean_dec_ref_known(v___y_1973_, 2);
v___x_1993_ = l_Lean_Expr_mdata___override(v_data_1986_, v_a_1989_);
v___x_1994_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v___x_1993_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1994_;
}
else
{
lean_object* v___x_1995_; 
lean_dec(v_a_1989_);
v___x_1995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v___y_1973_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_1995_;
}
}
else
{
lean_dec_ref_known(v___y_1973_, 2);
lean_dec_ref(v_post_1956_);
lean_dec_ref(v_pre_1954_);
return v___x_1988_;
}
}
case 11:
{
lean_object* v_typeName_1996_; lean_object* v_idx_1997_; lean_object* v_struct_1998_; lean_object* v___x_1999_; 
v_typeName_1996_ = lean_ctor_get(v___y_1973_, 0);
v_idx_1997_ = lean_ctor_get(v___y_1973_, 1);
v_struct_1998_ = lean_ctor_get(v___y_1973_, 2);
lean_inc_ref(v_struct_1998_);
lean_inc_ref(v_post_1956_);
lean_inc_ref(v_pre_1954_);
v___x_1999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v_struct_1998_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; size_t v___x_2001_; size_t v___x_2002_; uint8_t v___x_2003_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = lean_ptr_addr(v_struct_1998_);
v___x_2002_ = lean_ptr_addr(v_a_2000_);
v___x_2003_ = lean_usize_dec_eq(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_inc(v_idx_1997_);
lean_inc(v_typeName_1996_);
lean_dec_ref_known(v___y_1973_, 3);
v___x_2004_ = l_Lean_Expr_proj___override(v_typeName_1996_, v_idx_1997_, v_a_2000_);
v___x_2005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v___x_2004_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_2005_;
}
else
{
lean_object* v___x_2006_; 
lean_dec(v_a_2000_);
v___x_2006_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v___y_1973_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_2006_;
}
}
else
{
lean_dec_ref_known(v___y_1973_, 3);
lean_dec_ref(v_post_1956_);
lean_dec_ref(v_pre_1954_);
return v___x_1999_;
}
}
default: 
{
lean_object* v___x_2007_; 
v___x_2007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1954_, v_post_1956_, v_usedLetOnly_1957_, v_skipConstInApp_1958_, v_skipInstances_1959_, v___y_1973_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
return v___x_2007_;
}
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v_post_1956_);
lean_dec_ref(v_e_1955_);
lean_dec_ref(v_pre_1954_);
v_a_2017_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1967_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1967_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v_post_1956_);
lean_dec_ref(v_e_1955_);
lean_dec_ref(v_pre_1954_);
v_a_2025_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1966_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1966_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2033_, lean_object* v_pre_2034_, lean_object* v_e_2035_, lean_object* v_post_2036_, lean_object* v_usedLetOnly_2037_, lean_object* v_skipConstInApp_2038_, lean_object* v_skipInstances_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v_usedLetOnly_boxed_2046_; uint8_t v_skipConstInApp_boxed_2047_; uint8_t v_skipInstances_boxed_2048_; lean_object* v_res_2049_; 
v_usedLetOnly_boxed_2046_ = lean_unbox(v_usedLetOnly_2037_);
v_skipConstInApp_boxed_2047_ = lean_unbox(v_skipConstInApp_2038_);
v_skipInstances_boxed_2048_ = lean_unbox(v_skipInstances_2039_);
v_res_2049_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2033_, v_pre_2034_, v_e_2035_, v_post_2036_, v_usedLetOnly_boxed_2046_, v_skipConstInApp_boxed_2047_, v_skipInstances_boxed_2048_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2050_, lean_object* v_post_2051_, uint8_t v_usedLetOnly_2052_, uint8_t v_skipConstInApp_2053_, uint8_t v_skipInstances_2054_, lean_object* v_e_2055_, lean_object* v_a_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_inc(v_a_2056_);
v___x_2062_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2062_, 0, lean_box(0));
lean_closure_set(v___x_2062_, 1, lean_box(0));
lean_closure_set(v___x_2062_, 2, v_a_2056_);
v___x_2063_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2062_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2098_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2066_ = v___x_2063_;
v_isShared_2067_ = v_isSharedCheck_2098_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2063_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2098_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2064_, v_e_2055_);
lean_dec(v_a_2064_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; 
lean_del_object(v___x_2066_);
v___x_2069_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2070_ = lean_box(v_usedLetOnly_2052_);
v___x_2071_ = lean_box(v_skipConstInApp_2053_);
v___x_2072_ = lean_box(v_skipInstances_2054_);
lean_inc_ref(v_e_2055_);
v___f_2073_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2073_, 0, v___x_2069_);
lean_closure_set(v___f_2073_, 1, v_pre_2050_);
lean_closure_set(v___f_2073_, 2, v_e_2055_);
lean_closure_set(v___f_2073_, 3, v_post_2051_);
lean_closure_set(v___f_2073_, 4, v___x_2070_);
lean_closure_set(v___f_2073_, 5, v___x_2071_);
lean_closure_set(v___f_2073_, 6, v___x_2072_);
v___x_2074_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2073_, v_a_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___f_2076_; lean_object* v___x_2077_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc_n(v_a_2075_, 2);
lean_dec_ref_known(v___x_2074_, 1);
lean_inc(v_a_2056_);
v___f_2076_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2076_, 0, v_a_2056_);
lean_closure_set(v___f_2076_, 1, v_e_2055_);
lean_closure_set(v___f_2076_, 2, v_a_2075_);
v___x_2077_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2076_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v___x_2077_, 0);
lean_dec(v_unused_2085_);
v___x_2079_ = v___x_2077_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_dec(v___x_2077_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v_a_2075_);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2075_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_a_2075_);
v_a_2086_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2077_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2077_);
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
else
{
lean_dec_ref(v_e_2055_);
return v___x_2074_;
}
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; 
lean_dec_ref(v_e_2055_);
lean_dec_ref(v_post_2051_);
lean_dec_ref(v_pre_2050_);
v_val_2094_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2094_);
lean_dec_ref_known(v___x_2068_, 1);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v_val_2094_);
v___x_2096_ = v___x_2066_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_val_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_e_2055_);
lean_dec_ref(v_post_2051_);
lean_dec_ref(v_pre_2050_);
v_a_2099_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2063_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2063_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2107_, lean_object* v_post_2108_, uint8_t v_usedLetOnly_2109_, uint8_t v_skipConstInApp_2110_, uint8_t v_skipInstances_2111_, lean_object* v_fvars_2112_, lean_object* v_e_2113_, lean_object* v_a_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
if (lean_obj_tag(v_e_2113_) == 7)
{
lean_object* v_binderName_2120_; lean_object* v_binderType_2121_; lean_object* v_body_2122_; uint8_t v_binderInfo_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_binderName_2120_ = lean_ctor_get(v_e_2113_, 0);
lean_inc(v_binderName_2120_);
v_binderType_2121_ = lean_ctor_get(v_e_2113_, 1);
lean_inc_ref(v_binderType_2121_);
v_body_2122_ = lean_ctor_get(v_e_2113_, 2);
lean_inc_ref(v_body_2122_);
v_binderInfo_2123_ = lean_ctor_get_uint8(v_e_2113_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2113_, 3);
v___x_2124_ = lean_box(v_usedLetOnly_2109_);
v___x_2125_ = lean_box(v_skipConstInApp_2110_);
v___x_2126_ = lean_box(v_skipInstances_2111_);
lean_inc_ref(v_post_2108_);
lean_inc_ref(v_pre_2107_);
lean_inc_ref(v_fvars_2112_);
v___f_2127_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2127_, 0, v_fvars_2112_);
lean_closure_set(v___f_2127_, 1, v_pre_2107_);
lean_closure_set(v___f_2127_, 2, v_post_2108_);
lean_closure_set(v___f_2127_, 3, v___x_2124_);
lean_closure_set(v___f_2127_, 4, v___x_2125_);
lean_closure_set(v___f_2127_, 5, v___x_2126_);
lean_closure_set(v___f_2127_, 6, v_body_2122_);
v___x_2128_ = lean_expr_instantiate_rev(v_binderType_2121_, v_fvars_2112_);
lean_dec_ref(v_fvars_2112_);
lean_dec_ref(v_binderType_2121_);
v___x_2129_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2107_, v_post_2108_, v_usedLetOnly_2109_, v_skipConstInApp_2110_, v_skipInstances_2111_, v___x_2128_, v_a_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = 0;
v___x_2132_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2120_, v_binderInfo_2123_, v_a_2130_, v___f_2127_, v___x_2131_, v_a_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2132_;
}
else
{
lean_dec_ref(v___f_2127_);
lean_dec(v_binderName_2120_);
return v___x_2129_;
}
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = lean_expr_instantiate_rev(v_e_2113_, v_fvars_2112_);
lean_dec_ref(v_e_2113_);
lean_inc_ref(v_post_2108_);
lean_inc_ref(v_pre_2107_);
v___x_2134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2107_, v_post_2108_, v_usedLetOnly_2109_, v_skipConstInApp_2110_, v_skipInstances_2111_, v___x_2133_, v_a_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = 0;
v___x_2137_ = 1;
v___x_2138_ = 1;
v___x_2139_ = l_Lean_Meta_mkForallFVars(v_fvars_2112_, v_a_2135_, v___x_2136_, v_usedLetOnly_2109_, v___x_2137_, v___x_2138_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec_ref(v_fvars_2112_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2107_, v_post_2108_, v_usedLetOnly_2109_, v_skipConstInApp_2110_, v_skipInstances_2111_, v_a_2140_, v_a_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2141_;
}
else
{
lean_dec_ref(v_post_2108_);
lean_dec_ref(v_pre_2107_);
return v___x_2139_;
}
}
else
{
lean_dec_ref(v_fvars_2112_);
lean_dec_ref(v_post_2108_);
lean_dec_ref(v_pre_2107_);
return v___x_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2142_, lean_object* v_pre_2143_, lean_object* v_post_2144_, uint8_t v_usedLetOnly_2145_, uint8_t v_skipConstInApp_2146_, uint8_t v_skipInstances_2147_, lean_object* v_body_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_array_push(v_fvars_2142_, v_x_2149_);
v___x_2157_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2143_, v_post_2144_, v_usedLetOnly_2145_, v_skipConstInApp_2146_, v_skipInstances_2147_, v___x_2156_, v_body_2148_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2158_, lean_object* v_post_2159_, lean_object* v_usedLetOnly_2160_, lean_object* v_skipConstInApp_2161_, lean_object* v_skipInstances_2162_, lean_object* v_e_2163_, lean_object* v_a_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v_usedLetOnly_boxed_2170_; uint8_t v_skipConstInApp_boxed_2171_; uint8_t v_skipInstances_boxed_2172_; lean_object* v_res_2173_; 
v_usedLetOnly_boxed_2170_ = lean_unbox(v_usedLetOnly_2160_);
v_skipConstInApp_boxed_2171_ = lean_unbox(v_skipConstInApp_2161_);
v_skipInstances_boxed_2172_ = lean_unbox(v_skipInstances_2162_);
v_res_2173_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2158_, v_post_2159_, v_usedLetOnly_boxed_2170_, v_skipConstInApp_boxed_2171_, v_skipInstances_boxed_2172_, v_e_2163_, v_a_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v_a_2164_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2174_, lean_object* v_post_2175_, lean_object* v_usedLetOnly_2176_, lean_object* v_skipConstInApp_2177_, lean_object* v_skipInstances_2178_, lean_object* v_sz_2179_, lean_object* v_i_2180_, lean_object* v_bs_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v_usedLetOnly_boxed_2188_; uint8_t v_skipConstInApp_boxed_2189_; uint8_t v_skipInstances_boxed_2190_; size_t v_sz_boxed_2191_; size_t v_i_boxed_2192_; lean_object* v_res_2193_; 
v_usedLetOnly_boxed_2188_ = lean_unbox(v_usedLetOnly_2176_);
v_skipConstInApp_boxed_2189_ = lean_unbox(v_skipConstInApp_2177_);
v_skipInstances_boxed_2190_ = lean_unbox(v_skipInstances_2178_);
v_sz_boxed_2191_ = lean_unbox_usize(v_sz_2179_);
lean_dec(v_sz_2179_);
v_i_boxed_2192_ = lean_unbox_usize(v_i_2180_);
lean_dec(v_i_2180_);
v_res_2193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2174_, v_post_2175_, v_usedLetOnly_boxed_2188_, v_skipConstInApp_boxed_2189_, v_skipInstances_boxed_2190_, v_sz_boxed_2191_, v_i_boxed_2192_, v_bs_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2194_, lean_object* v_post_2195_, lean_object* v_usedLetOnly_2196_, lean_object* v_skipConstInApp_2197_, lean_object* v_skipInstances_2198_, lean_object* v_e_2199_, lean_object* v_a_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v_usedLetOnly_boxed_2206_; uint8_t v_skipConstInApp_boxed_2207_; uint8_t v_skipInstances_boxed_2208_; lean_object* v_res_2209_; 
v_usedLetOnly_boxed_2206_ = lean_unbox(v_usedLetOnly_2196_);
v_skipConstInApp_boxed_2207_ = lean_unbox(v_skipConstInApp_2197_);
v_skipInstances_boxed_2208_ = lean_unbox(v_skipInstances_2198_);
v_res_2209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2194_, v_post_2195_, v_usedLetOnly_boxed_2206_, v_skipConstInApp_boxed_2207_, v_skipInstances_boxed_2208_, v_e_2199_, v_a_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v_a_2200_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2210_, lean_object* v_post_2211_, lean_object* v_usedLetOnly_2212_, lean_object* v_skipConstInApp_2213_, lean_object* v_skipInstances_2214_, lean_object* v_fvars_2215_, lean_object* v_e_2216_, lean_object* v_a_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
uint8_t v_usedLetOnly_boxed_2223_; uint8_t v_skipConstInApp_boxed_2224_; uint8_t v_skipInstances_boxed_2225_; lean_object* v_res_2226_; 
v_usedLetOnly_boxed_2223_ = lean_unbox(v_usedLetOnly_2212_);
v_skipConstInApp_boxed_2224_ = lean_unbox(v_skipConstInApp_2213_);
v_skipInstances_boxed_2225_ = lean_unbox(v_skipInstances_2214_);
v_res_2226_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2210_, v_post_2211_, v_usedLetOnly_boxed_2223_, v_skipConstInApp_boxed_2224_, v_skipInstances_boxed_2225_, v_fvars_2215_, v_e_2216_, v_a_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v_a_2217_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2227_, lean_object* v_post_2228_, lean_object* v_usedLetOnly_2229_, lean_object* v_skipConstInApp_2230_, lean_object* v_skipInstances_2231_, lean_object* v_fvars_2232_, lean_object* v_e_2233_, lean_object* v_a_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
uint8_t v_usedLetOnly_boxed_2240_; uint8_t v_skipConstInApp_boxed_2241_; uint8_t v_skipInstances_boxed_2242_; lean_object* v_res_2243_; 
v_usedLetOnly_boxed_2240_ = lean_unbox(v_usedLetOnly_2229_);
v_skipConstInApp_boxed_2241_ = lean_unbox(v_skipConstInApp_2230_);
v_skipInstances_boxed_2242_ = lean_unbox(v_skipInstances_2231_);
v_res_2243_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2227_, v_post_2228_, v_usedLetOnly_boxed_2240_, v_skipConstInApp_boxed_2241_, v_skipInstances_boxed_2242_, v_fvars_2232_, v_e_2233_, v_a_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v_a_2234_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2244_, lean_object* v_post_2245_, lean_object* v_usedLetOnly_2246_, lean_object* v_skipConstInApp_2247_, lean_object* v_skipInstances_2248_, lean_object* v_fvars_2249_, lean_object* v_e_2250_, lean_object* v_a_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
uint8_t v_usedLetOnly_boxed_2257_; uint8_t v_skipConstInApp_boxed_2258_; uint8_t v_skipInstances_boxed_2259_; lean_object* v_res_2260_; 
v_usedLetOnly_boxed_2257_ = lean_unbox(v_usedLetOnly_2246_);
v_skipConstInApp_boxed_2258_ = lean_unbox(v_skipConstInApp_2247_);
v_skipInstances_boxed_2259_ = lean_unbox(v_skipInstances_2248_);
v_res_2260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2244_, v_post_2245_, v_usedLetOnly_boxed_2257_, v_skipConstInApp_boxed_2258_, v_skipInstances_boxed_2259_, v_fvars_2249_, v_e_2250_, v_a_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v_a_2251_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2261_, lean_object* v___x_2262_, lean_object* v_pre_2263_, lean_object* v_post_2264_, lean_object* v_usedLetOnly_2265_, lean_object* v_skipConstInApp_2266_, lean_object* v_skipInstances_2267_, lean_object* v_a_2268_, lean_object* v_b_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
uint8_t v_usedLetOnly_boxed_2276_; uint8_t v_skipConstInApp_boxed_2277_; uint8_t v_skipInstances_boxed_2278_; lean_object* v_res_2279_; 
v_usedLetOnly_boxed_2276_ = lean_unbox(v_usedLetOnly_2265_);
v_skipConstInApp_boxed_2277_ = lean_unbox(v_skipConstInApp_2266_);
v_skipInstances_boxed_2278_ = lean_unbox(v_skipInstances_2267_);
v_res_2279_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2261_, v___x_2262_, v_pre_2263_, v_post_2264_, v_usedLetOnly_boxed_2276_, v_skipConstInApp_boxed_2277_, v_skipInstances_boxed_2278_, v_a_2268_, v_b_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___x_2262_);
lean_dec(v_upperBound_2261_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2280_, lean_object* v_pre_2281_, lean_object* v_post_2282_, lean_object* v_usedLetOnly_2283_, lean_object* v_skipConstInApp_2284_, lean_object* v_x_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
uint8_t v_skipInstances_boxed_2294_; uint8_t v_usedLetOnly_boxed_2295_; uint8_t v_skipConstInApp_boxed_2296_; lean_object* v_res_2297_; 
v_skipInstances_boxed_2294_ = lean_unbox(v_skipInstances_2280_);
v_usedLetOnly_boxed_2295_ = lean_unbox(v_usedLetOnly_2283_);
v_skipConstInApp_boxed_2296_ = lean_unbox(v_skipConstInApp_2284_);
v_res_2297_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2294_, v_pre_2281_, v_post_2282_, v_usedLetOnly_boxed_2295_, v_skipConstInApp_boxed_2296_, v_x_2285_, v_x_2286_, v_x_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
return v_res_2297_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2299_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2299_, 0, lean_box(0));
lean_closure_set(v___x_2299_, 1, lean_box(0));
lean_closure_set(v___x_2299_, 2, v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2300_, lean_object* v_pre_2301_, lean_object* v_post_2302_, uint8_t v_usedLetOnly_2303_, uint8_t v_skipConstInApp_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2314_; 
v___x_2310_ = 0;
v___x_2311_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2312_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2311_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref(v___x_2312_);
v___x_2314_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2301_, v_post_2302_, v_usedLetOnly_2303_, v_skipConstInApp_2304_, v___x_2310_, v_input_2300_, v_a_2313_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2316_, 0, lean_box(0));
lean_closure_set(v___x_2316_, 1, lean_box(0));
lean_closure_set(v___x_2316_, 2, v_a_2313_);
v___x_2317_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2316_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2324_ == 0)
{
lean_object* v_unused_2325_; 
v_unused_2325_ = lean_ctor_get(v___x_2317_, 0);
lean_dec(v_unused_2325_);
v___x_2319_ = v___x_2317_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_dec(v___x_2317_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_a_2315_);
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2315_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
else
{
lean_dec(v_a_2313_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2326_, lean_object* v_pre_2327_, lean_object* v_post_2328_, lean_object* v_usedLetOnly_2329_, lean_object* v_skipConstInApp_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
uint8_t v_usedLetOnly_boxed_2336_; uint8_t v_skipConstInApp_boxed_2337_; lean_object* v_res_2338_; 
v_usedLetOnly_boxed_2336_ = lean_unbox(v_usedLetOnly_2329_);
v_skipConstInApp_boxed_2337_ = lean_unbox(v_skipConstInApp_2330_);
v_res_2338_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2326_, v_pre_2327_, v_post_2328_, v_usedLetOnly_boxed_2336_, v_skipConstInApp_boxed_2337_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2339_, lean_object* v_as_2340_, lean_object* v_j_2341_){
_start:
{
lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2342_ = lean_array_get_size(v_as_2340_);
v___x_2343_ = lean_nat_dec_lt(v_j_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
lean_dec(v_j_2341_);
v___x_2344_ = lean_box(0);
return v___x_2344_;
}
else
{
lean_object* v___x_2345_; lean_object* v_declName_2346_; uint8_t v___x_2347_; 
v___x_2345_ = lean_array_fget_borrowed(v_as_2340_, v_j_2341_);
v_declName_2346_ = lean_ctor_get(v___x_2345_, 3);
v___x_2347_ = lean_name_eq(v_declName_2346_, v___x_2339_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_unsigned_to_nat(1u);
v___x_2349_ = lean_nat_add(v_j_2341_, v___x_2348_);
lean_dec(v_j_2341_);
v_j_2341_ = v___x_2349_;
goto _start;
}
else
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_j_2341_);
return v___x_2351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2352_, lean_object* v_as_2353_, lean_object* v_j_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2352_, v_as_2353_, v_j_2354_);
lean_dec_ref(v_as_2353_);
lean_dec(v___x_2352_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_st_ref_get(v_val_2356_);
v___x_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v_val_2364_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2371_, lean_object* v_val_2372_, lean_object* v_a_2373_, lean_object* v___x_2374_, lean_object* v_____r_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2381_ = lean_st_ref_take(v_val_2371_);
v___x_2382_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2372_, v_a_2373_, v___x_2381_);
v___x_2383_ = lean_st_ref_put(v_val_2371_, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2374_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2386_, lean_object* v_val_2387_, lean_object* v_a_2388_, lean_object* v___x_2389_, lean_object* v_____r_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2386_, v_val_2387_, v_a_2388_, v___x_2389_, v_____r_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_val_2387_);
lean_dec(v_val_2386_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2397_, lean_object* v_val_2398_, lean_object* v_next_2399_, lean_object* v_next_2400_, lean_object* v___x_2401_, lean_object* v___x_2402_, lean_object* v_upperBound_2403_, lean_object* v_params_2404_, lean_object* v___x_2405_, lean_object* v_a_2406_, uint8_t v_b_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
uint8_t v_a_2414_; uint8_t v___x_2418_; 
v___x_2418_ = lean_nat_dec_lt(v_a_2406_, v_upperBound_2403_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
lean_dec(v_a_2406_);
lean_dec_ref(v___x_2405_);
lean_dec(v_next_2399_);
v___x_2419_ = lean_box(v_b_2407_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
else
{
uint8_t v___x_2421_; lean_object* v___y_2423_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2421_ = lean_nat_dec_eq(v___x_2401_, v___x_2402_);
v___x_2437_ = lean_st_ref_get(v_val_2397_);
v___x_2438_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2400_, v_a_2406_, v___x_2437_);
lean_dec(v___x_2437_);
if (v___x_2438_ == 0)
{
v_a_2414_ = v_b_2407_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2439_; uint8_t v_foApprox_2440_; uint8_t v_ctxApprox_2441_; uint8_t v_quasiPatternApprox_2442_; uint8_t v_constApprox_2443_; uint8_t v_isDefEqStuckEx_2444_; uint8_t v_unificationHints_2445_; uint8_t v_assignSyntheticOpaque_2446_; uint8_t v_offsetCnstrs_2447_; uint8_t v_transparency_2448_; uint8_t v_etaStruct_2449_; uint8_t v_univApprox_2450_; uint8_t v_iota_2451_; uint8_t v_beta_2452_; uint8_t v_proj_2453_; uint8_t v_zeta_2454_; uint8_t v_zetaDelta_2455_; uint8_t v_zetaUnused_2456_; uint8_t v_zetaHave_2457_; uint8_t v_canUnfoldPredicateConfig_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2488_; 
v___x_2439_ = l_Lean_Meta_Context_config(v___y_2408_);
v_foApprox_2440_ = lean_ctor_get_uint8(v___x_2439_, 0);
v_ctxApprox_2441_ = lean_ctor_get_uint8(v___x_2439_, 1);
v_quasiPatternApprox_2442_ = lean_ctor_get_uint8(v___x_2439_, 2);
v_constApprox_2443_ = lean_ctor_get_uint8(v___x_2439_, 3);
v_isDefEqStuckEx_2444_ = lean_ctor_get_uint8(v___x_2439_, 4);
v_unificationHints_2445_ = lean_ctor_get_uint8(v___x_2439_, 5);
v_assignSyntheticOpaque_2446_ = lean_ctor_get_uint8(v___x_2439_, 7);
v_offsetCnstrs_2447_ = lean_ctor_get_uint8(v___x_2439_, 8);
v_transparency_2448_ = lean_ctor_get_uint8(v___x_2439_, 9);
v_etaStruct_2449_ = lean_ctor_get_uint8(v___x_2439_, 10);
v_univApprox_2450_ = lean_ctor_get_uint8(v___x_2439_, 11);
v_iota_2451_ = lean_ctor_get_uint8(v___x_2439_, 12);
v_beta_2452_ = lean_ctor_get_uint8(v___x_2439_, 13);
v_proj_2453_ = lean_ctor_get_uint8(v___x_2439_, 14);
v_zeta_2454_ = lean_ctor_get_uint8(v___x_2439_, 15);
v_zetaDelta_2455_ = lean_ctor_get_uint8(v___x_2439_, 16);
v_zetaUnused_2456_ = lean_ctor_get_uint8(v___x_2439_, 17);
v_zetaHave_2457_ = lean_ctor_get_uint8(v___x_2439_, 18);
v_canUnfoldPredicateConfig_2458_ = lean_ctor_get_uint8(v___x_2439_, 19);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2460_ = v___x_2439_;
v_isShared_2461_ = v_isSharedCheck_2488_;
goto v_resetjp_2459_;
}
else
{
lean_dec(v___x_2439_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2488_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
uint8_t v_trackZetaDelta_2462_; lean_object* v_zetaDeltaSet_2463_; lean_object* v_lctx_2464_; lean_object* v_localInstances_2465_; lean_object* v_defEqCtx_x3f_2466_; lean_object* v_synthPendingDepth_2467_; lean_object* v_customCanUnfoldPredicate_x3f_2468_; uint8_t v_univApprox_2469_; uint8_t v_inTypeClassResolution_2470_; uint8_t v_cacheInferType_2471_; uint8_t v___x_2472_; lean_object* v___x_2474_; 
v_trackZetaDelta_2462_ = lean_ctor_get_uint8(v___y_2408_, sizeof(void*)*7);
v_zetaDeltaSet_2463_ = lean_ctor_get(v___y_2408_, 1);
v_lctx_2464_ = lean_ctor_get(v___y_2408_, 2);
v_localInstances_2465_ = lean_ctor_get(v___y_2408_, 3);
v_defEqCtx_x3f_2466_ = lean_ctor_get(v___y_2408_, 4);
v_synthPendingDepth_2467_ = lean_ctor_get(v___y_2408_, 5);
v_customCanUnfoldPredicate_x3f_2468_ = lean_ctor_get(v___y_2408_, 6);
v_univApprox_2469_ = lean_ctor_get_uint8(v___y_2408_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2470_ = lean_ctor_get_uint8(v___y_2408_, sizeof(void*)*7 + 2);
v_cacheInferType_2471_ = lean_ctor_get_uint8(v___y_2408_, sizeof(void*)*7 + 3);
v___x_2472_ = 0;
if (v_isShared_2461_ == 0)
{
v___x_2474_ = v___x_2460_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 0, v_foApprox_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 1, v_ctxApprox_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 2, v_quasiPatternApprox_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 3, v_constApprox_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 4, v_isDefEqStuckEx_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 5, v_unificationHints_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 7, v_assignSyntheticOpaque_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 8, v_offsetCnstrs_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 9, v_transparency_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 10, v_etaStruct_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 11, v_univApprox_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 12, v_iota_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 13, v_beta_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 14, v_proj_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 15, v_zeta_2454_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 16, v_zetaDelta_2455_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 17, v_zetaUnused_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 18, v_zetaHave_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2487_, 19, v_canUnfoldPredicateConfig_2458_);
v___x_2474_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
uint64_t v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v_transparency_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; uint8_t v___x_2482_; 
lean_ctor_set_uint8(v___x_2474_, 6, v___x_2472_);
v___x_2475_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set_uint64(v___x_2476_, sizeof(void*)*1, v___x_2475_);
lean_inc(v_customCanUnfoldPredicate_x3f_2468_);
lean_inc(v_synthPendingDepth_2467_);
lean_inc(v_defEqCtx_x3f_2466_);
lean_inc_ref(v_localInstances_2465_);
lean_inc_ref(v_lctx_2464_);
lean_inc(v_zetaDeltaSet_2463_);
lean_inc_ref(v___x_2476_);
v___x_2477_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
lean_ctor_set(v___x_2477_, 1, v_zetaDeltaSet_2463_);
lean_ctor_set(v___x_2477_, 2, v_lctx_2464_);
lean_ctor_set(v___x_2477_, 3, v_localInstances_2465_);
lean_ctor_set(v___x_2477_, 4, v_defEqCtx_x3f_2466_);
lean_ctor_set(v___x_2477_, 5, v_synthPendingDepth_2467_);
lean_ctor_set(v___x_2477_, 6, v_customCanUnfoldPredicate_x3f_2468_);
lean_ctor_set_uint8(v___x_2477_, sizeof(void*)*7, v_trackZetaDelta_2462_);
lean_ctor_set_uint8(v___x_2477_, sizeof(void*)*7 + 1, v_univApprox_2469_);
lean_ctor_set_uint8(v___x_2477_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2470_);
lean_ctor_set_uint8(v___x_2477_, sizeof(void*)*7 + 3, v_cacheInferType_2471_);
v___x_2478_ = l_Lean_Meta_Context_config(v___x_2477_);
v_transparency_2479_ = lean_ctor_get_uint8(v___x_2478_, 9);
lean_dec_ref(v___x_2478_);
v___x_2480_ = lean_array_fget_borrowed(v_params_2404_, v_a_2406_);
v___x_2481_ = 2;
v___x_2482_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2479_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec_ref_known(v___x_2477_, 7);
v___x_2483_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2481_, v___x_2476_);
lean_inc(v_customCanUnfoldPredicate_x3f_2468_);
lean_inc(v_synthPendingDepth_2467_);
lean_inc(v_defEqCtx_x3f_2466_);
lean_inc_ref(v_localInstances_2465_);
lean_inc_ref(v_lctx_2464_);
lean_inc(v_zetaDeltaSet_2463_);
v___x_2484_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v_zetaDeltaSet_2463_);
lean_ctor_set(v___x_2484_, 2, v_lctx_2464_);
lean_ctor_set(v___x_2484_, 3, v_localInstances_2465_);
lean_ctor_set(v___x_2484_, 4, v_defEqCtx_x3f_2466_);
lean_ctor_set(v___x_2484_, 5, v_synthPendingDepth_2467_);
lean_ctor_set(v___x_2484_, 6, v_customCanUnfoldPredicate_x3f_2468_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*7, v_trackZetaDelta_2462_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*7 + 1, v_univApprox_2469_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2470_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*7 + 3, v_cacheInferType_2471_);
lean_inc_ref(v___x_2405_);
lean_inc(v___x_2480_);
v___x_2485_ = l_Lean_Meta_isExprDefEq(v___x_2480_, v___x_2405_, v___x_2484_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec_ref_known(v___x_2484_, 7);
v___y_2423_ = v___x_2485_;
goto v___jp_2422_;
}
else
{
lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2476_, 1);
lean_inc_ref(v___x_2405_);
lean_inc(v___x_2480_);
v___x_2486_ = l_Lean_Meta_isExprDefEq(v___x_2480_, v___x_2405_, v___x_2477_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec_ref_known(v___x_2477_, 7);
v___y_2423_ = v___x_2486_;
goto v___jp_2422_;
}
}
}
}
v___jp_2422_:
{
if (lean_obj_tag(v___y_2423_) == 0)
{
lean_object* v_a_2424_; uint8_t v___x_2425_; 
v_a_2424_ = lean_ctor_get(v___y_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___y_2423_, 1);
v___x_2425_ = lean_unbox(v_a_2424_);
lean_dec(v_a_2424_);
if (v___x_2425_ == 0)
{
v_a_2414_ = v_b_2407_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = lean_st_ref_take(v_val_2397_);
lean_inc(v_a_2406_);
lean_inc(v_next_2399_);
v___x_2427_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2398_, v_next_2399_, v_next_2400_, v_a_2406_, v___x_2426_);
v___x_2428_ = lean_st_ref_put(v_val_2397_, v___x_2427_);
v_a_2414_ = v___x_2421_;
goto v___jp_2413_;
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_a_2406_);
lean_dec_ref(v___x_2405_);
lean_dec(v_next_2399_);
v_a_2429_ = lean_ctor_get(v___y_2423_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___y_2423_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___y_2423_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___y_2423_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
v___jp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_nat_add(v_a_2406_, v___x_2415_);
lean_dec(v_a_2406_);
v_a_2406_ = v___x_2416_;
v_b_2407_ = v_a_2414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2489_, lean_object* v_val_2490_, lean_object* v_next_2491_, lean_object* v_next_2492_, lean_object* v___x_2493_, lean_object* v___x_2494_, lean_object* v_upperBound_2495_, lean_object* v_params_2496_, lean_object* v___x_2497_, lean_object* v_a_2498_, lean_object* v_b_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v_b_boxed_2505_; lean_object* v_res_2506_; 
v_b_boxed_2505_ = lean_unbox(v_b_2499_);
v_res_2506_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2489_, v_val_2490_, v_next_2491_, v_next_2492_, v___x_2493_, v___x_2494_, v_upperBound_2495_, v_params_2496_, v___x_2497_, v_a_2498_, v_b_boxed_2505_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v_params_2496_);
lean_dec(v_upperBound_2495_);
lean_dec(v___x_2494_);
lean_dec(v___x_2493_);
lean_dec(v_next_2492_);
lean_dec(v_val_2490_);
lean_dec(v_val_2489_);
return v_res_2506_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2518_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2519_ = l_Lean_Name_append(v___x_2518_, v___x_2517_);
return v___x_2519_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2527_ = l_Lean_stringToMessageData(v___x_2526_);
return v___x_2527_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2530_ = l_Lean_stringToMessageData(v___x_2529_);
return v___x_2530_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2533_ = l_Lean_stringToMessageData(v___x_2532_);
return v___x_2533_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2536_ = l_Lean_stringToMessageData(v___x_2535_);
return v___x_2536_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2539_ = l_Lean_stringToMessageData(v___x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2540_, lean_object* v_val_2541_, lean_object* v_upperBound_2542_, lean_object* v_args_2543_, lean_object* v_e_2544_, lean_object* v_next_2545_, lean_object* v_params_2546_, lean_object* v___x_2547_, lean_object* v___x_2548_, lean_object* v_a_2549_, lean_object* v_b_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_a_2557_; lean_object* v___y_2562_; uint8_t v___x_2581_; 
v___x_2581_ = lean_nat_dec_lt(v_a_2549_, v_upperBound_2542_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_b_2550_);
return v___x_2582_;
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2583_ = lean_box(0);
v___x_2590_ = l_Lean_instInhabitedExpr;
v___x_2591_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2540_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; uint8_t v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2541_, v_a_2549_, v_a_2592_);
lean_dec(v_a_2592_);
if (v___x_2593_ == 0)
{
v_a_2557_ = v___x_2583_;
goto v___jp_2556_;
}
else
{
lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2594_ = lean_array_get_size(v_args_2543_);
v___x_2595_ = lean_nat_dec_lt(v_a_2549_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v_toCold_2596_; lean_object* v_options_2597_; uint8_t v_hasTrace_2598_; 
v_toCold_2596_ = lean_ctor_get(v___y_2553_, 0);
v_options_2597_ = lean_ctor_get(v_toCold_2596_, 2);
v_hasTrace_2598_ = lean_ctor_get_uint8(v_options_2597_, sizeof(void*)*1);
if (v_hasTrace_2598_ == 0)
{
goto v___jp_2586_;
}
else
{
lean_object* v_inheritedTraceOptions_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_inheritedTraceOptions_2599_ = lean_ctor_get(v_toCold_2596_, 11);
v___x_2600_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2601_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2602_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2599_, v_options_2597_, v___x_2601_);
if (v___x_2602_ == 0)
{
goto v___jp_2586_;
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2603_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2541_);
v___x_2604_ = l_Nat_reprFast(v_val_2541_);
v___x_2605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
v___x_2606_ = l_Lean_MessageData_ofFormat(v___x_2605_);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2603_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
lean_inc(v_a_2549_);
v___x_2610_ = l_Nat_reprFast(v_a_2549_);
v___x_2611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
v___x_2612_ = l_Lean_MessageData_ofFormat(v___x_2611_);
lean_inc_ref(v___x_2612_);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2609_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
lean_inc_ref(v_e_2544_);
v___x_2616_ = l_Lean_MessageData_ofExpr(v_e_2544_);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2612_);
v___x_2621_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2600_, v___x_2620_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2623_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
lean_inc(v_a_2549_);
v___x_2623_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2540_, v_val_2541_, v_a_2549_, v___x_2583_, v_a_2622_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
v___y_2562_ = v___x_2623_;
goto v___jp_2561_;
}
else
{
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
return v___x_2621_;
}
}
}
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_array_fget_borrowed(v_args_2543_, v_a_2549_);
v___x_2625_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2540_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2541_, v_a_2549_, v_next_2545_, v_a_2626_);
lean_dec(v_a_2626_);
if (lean_obj_tag(v___x_2627_) == 1)
{
lean_object* v_val_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2729_; 
v_val_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2729_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_val_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2729_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; uint8_t v_foApprox_2633_; uint8_t v_ctxApprox_2634_; uint8_t v_quasiPatternApprox_2635_; uint8_t v_constApprox_2636_; uint8_t v_isDefEqStuckEx_2637_; uint8_t v_unificationHints_2638_; uint8_t v_assignSyntheticOpaque_2639_; uint8_t v_offsetCnstrs_2640_; uint8_t v_transparency_2641_; uint8_t v_etaStruct_2642_; uint8_t v_univApprox_2643_; uint8_t v_iota_2644_; uint8_t v_beta_2645_; uint8_t v_proj_2646_; uint8_t v_zeta_2647_; uint8_t v_zetaDelta_2648_; uint8_t v_zetaUnused_2649_; uint8_t v_zetaHave_2650_; uint8_t v_canUnfoldPredicateConfig_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2728_; 
v___x_2632_ = l_Lean_Meta_Context_config(v___y_2551_);
v_foApprox_2633_ = lean_ctor_get_uint8(v___x_2632_, 0);
v_ctxApprox_2634_ = lean_ctor_get_uint8(v___x_2632_, 1);
v_quasiPatternApprox_2635_ = lean_ctor_get_uint8(v___x_2632_, 2);
v_constApprox_2636_ = lean_ctor_get_uint8(v___x_2632_, 3);
v_isDefEqStuckEx_2637_ = lean_ctor_get_uint8(v___x_2632_, 4);
v_unificationHints_2638_ = lean_ctor_get_uint8(v___x_2632_, 5);
v_assignSyntheticOpaque_2639_ = lean_ctor_get_uint8(v___x_2632_, 7);
v_offsetCnstrs_2640_ = lean_ctor_get_uint8(v___x_2632_, 8);
v_transparency_2641_ = lean_ctor_get_uint8(v___x_2632_, 9);
v_etaStruct_2642_ = lean_ctor_get_uint8(v___x_2632_, 10);
v_univApprox_2643_ = lean_ctor_get_uint8(v___x_2632_, 11);
v_iota_2644_ = lean_ctor_get_uint8(v___x_2632_, 12);
v_beta_2645_ = lean_ctor_get_uint8(v___x_2632_, 13);
v_proj_2646_ = lean_ctor_get_uint8(v___x_2632_, 14);
v_zeta_2647_ = lean_ctor_get_uint8(v___x_2632_, 15);
v_zetaDelta_2648_ = lean_ctor_get_uint8(v___x_2632_, 16);
v_zetaUnused_2649_ = lean_ctor_get_uint8(v___x_2632_, 17);
v_zetaHave_2650_ = lean_ctor_get_uint8(v___x_2632_, 18);
v_canUnfoldPredicateConfig_2651_ = lean_ctor_get_uint8(v___x_2632_, 19);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2653_ = v___x_2632_;
v_isShared_2654_ = v_isSharedCheck_2728_;
goto v_resetjp_2652_;
}
else
{
lean_dec(v___x_2632_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2728_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
uint8_t v_trackZetaDelta_2655_; lean_object* v_zetaDeltaSet_2656_; lean_object* v_lctx_2657_; lean_object* v_localInstances_2658_; lean_object* v_defEqCtx_x3f_2659_; lean_object* v_synthPendingDepth_2660_; lean_object* v_customCanUnfoldPredicate_x3f_2661_; uint8_t v_univApprox_2662_; uint8_t v_inTypeClassResolution_2663_; uint8_t v_cacheInferType_2664_; uint8_t v___x_2665_; lean_object* v___x_2667_; 
v_trackZetaDelta_2655_ = lean_ctor_get_uint8(v___y_2551_, sizeof(void*)*7);
v_zetaDeltaSet_2656_ = lean_ctor_get(v___y_2551_, 1);
v_lctx_2657_ = lean_ctor_get(v___y_2551_, 2);
v_localInstances_2658_ = lean_ctor_get(v___y_2551_, 3);
v_defEqCtx_x3f_2659_ = lean_ctor_get(v___y_2551_, 4);
v_synthPendingDepth_2660_ = lean_ctor_get(v___y_2551_, 5);
v_customCanUnfoldPredicate_x3f_2661_ = lean_ctor_get(v___y_2551_, 6);
v_univApprox_2662_ = lean_ctor_get_uint8(v___y_2551_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2663_ = lean_ctor_get_uint8(v___y_2551_, sizeof(void*)*7 + 2);
v_cacheInferType_2664_ = lean_ctor_get_uint8(v___y_2551_, sizeof(void*)*7 + 3);
v___x_2665_ = 0;
if (v_isShared_2654_ == 0)
{
v___x_2667_ = v___x_2653_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 0, v_foApprox_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 1, v_ctxApprox_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 2, v_quasiPatternApprox_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 3, v_constApprox_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 4, v_isDefEqStuckEx_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 5, v_unificationHints_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 7, v_assignSyntheticOpaque_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 8, v_offsetCnstrs_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 9, v_transparency_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 10, v_etaStruct_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 11, v_univApprox_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 12, v_iota_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 13, v_beta_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 14, v_proj_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 15, v_zeta_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 16, v_zetaDelta_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 17, v_zetaUnused_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 18, v_zetaHave_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2727_, 19, v_canUnfoldPredicateConfig_2651_);
v___x_2667_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
uint64_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v_transparency_2672_; lean_object* v___x_2673_; lean_object* v___y_2675_; uint8_t v___x_2721_; uint8_t v___x_2722_; 
lean_ctor_set_uint8(v___x_2667_, 6, v___x_2665_);
v___x_2668_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set_uint64(v___x_2669_, sizeof(void*)*1, v___x_2668_);
lean_inc(v_customCanUnfoldPredicate_x3f_2661_);
lean_inc(v_synthPendingDepth_2660_);
lean_inc(v_defEqCtx_x3f_2659_);
lean_inc_ref(v_localInstances_2658_);
lean_inc_ref(v_lctx_2657_);
lean_inc(v_zetaDeltaSet_2656_);
lean_inc_ref(v___x_2669_);
v___x_2670_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v_zetaDeltaSet_2656_);
lean_ctor_set(v___x_2670_, 2, v_lctx_2657_);
lean_ctor_set(v___x_2670_, 3, v_localInstances_2658_);
lean_ctor_set(v___x_2670_, 4, v_defEqCtx_x3f_2659_);
lean_ctor_set(v___x_2670_, 5, v_synthPendingDepth_2660_);
lean_ctor_set(v___x_2670_, 6, v_customCanUnfoldPredicate_x3f_2661_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7, v_trackZetaDelta_2655_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 1, v_univApprox_2662_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2663_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 3, v_cacheInferType_2664_);
v___x_2671_ = l_Lean_Meta_Context_config(v___x_2670_);
v_transparency_2672_ = lean_ctor_get_uint8(v___x_2671_, 9);
lean_dec_ref(v___x_2671_);
v___x_2673_ = lean_array_get_borrowed(v___x_2590_, v_params_2546_, v_val_2628_);
lean_dec(v_val_2628_);
v___x_2721_ = 2;
v___x_2722_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2672_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref_known(v___x_2670_, 7);
v___x_2723_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2721_, v___x_2669_);
lean_inc(v_customCanUnfoldPredicate_x3f_2661_);
lean_inc(v_synthPendingDepth_2660_);
lean_inc(v_defEqCtx_x3f_2659_);
lean_inc_ref(v_localInstances_2658_);
lean_inc_ref(v_lctx_2657_);
lean_inc(v_zetaDeltaSet_2656_);
v___x_2724_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v_zetaDeltaSet_2656_);
lean_ctor_set(v___x_2724_, 2, v_lctx_2657_);
lean_ctor_set(v___x_2724_, 3, v_localInstances_2658_);
lean_ctor_set(v___x_2724_, 4, v_defEqCtx_x3f_2659_);
lean_ctor_set(v___x_2724_, 5, v_synthPendingDepth_2660_);
lean_ctor_set(v___x_2724_, 6, v_customCanUnfoldPredicate_x3f_2661_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7, v_trackZetaDelta_2655_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 1, v_univApprox_2662_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2663_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*7 + 3, v_cacheInferType_2664_);
lean_inc(v___x_2624_);
lean_inc(v___x_2673_);
v___x_2725_ = l_Lean_Meta_isExprDefEq(v___x_2673_, v___x_2624_, v___x_2724_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec_ref_known(v___x_2724_, 7);
v___y_2675_ = v___x_2725_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2726_; 
lean_dec_ref_known(v___x_2669_, 1);
lean_inc(v___x_2624_);
lean_inc(v___x_2673_);
v___x_2726_ = l_Lean_Meta_isExprDefEq(v___x_2673_, v___x_2624_, v___x_2670_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec_ref_known(v___x_2670_, 7);
v___y_2675_ = v___x_2726_;
goto v___jp_2674_;
}
v___jp_2674_:
{
if (lean_obj_tag(v___y_2675_) == 0)
{
lean_object* v_a_2676_; uint8_t v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___y_2675_, 1);
v___x_2677_ = lean_unbox(v_a_2676_);
lean_dec(v_a_2676_);
if (v___x_2677_ == 0)
{
lean_object* v_toCold_2678_; lean_object* v_options_2679_; uint8_t v_hasTrace_2680_; 
v_toCold_2678_ = lean_ctor_get(v___y_2553_, 0);
v_options_2679_ = lean_ctor_get(v_toCold_2678_, 2);
v_hasTrace_2680_ = lean_ctor_get_uint8(v_options_2679_, sizeof(void*)*1);
if (v_hasTrace_2680_ == 0)
{
lean_del_object(v___x_2630_);
goto v___jp_2588_;
}
else
{
lean_object* v_inheritedTraceOptions_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v_inheritedTraceOptions_2681_ = lean_ctor_get(v_toCold_2678_, 11);
v___x_2682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2683_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2684_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2681_, v_options_2679_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_del_object(v___x_2630_);
goto v___jp_2588_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2541_);
v___x_2686_ = l_Nat_reprFast(v_val_2541_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 3);
lean_ctor_set(v___x_2630_, 0, v___x_2686_);
v___x_2688_ = v___x_2630_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2689_ = l_Lean_MessageData_ofFormat(v___x_2688_);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2685_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
lean_inc(v_a_2549_);
v___x_2693_ = l_Nat_reprFast(v_a_2549_);
v___x_2694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
v___x_2695_ = l_Lean_MessageData_ofFormat(v___x_2694_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2692_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
lean_inc_ref(v_e_2544_);
v___x_2699_ = l_Lean_MessageData_ofExpr(v_e_2544_);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_inc(v___x_2673_);
v___x_2703_ = l_Lean_MessageData_ofExpr(v___x_2673_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_inc(v___x_2624_);
v___x_2707_ = l_Lean_MessageData_ofExpr(v___x_2624_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2682_, v___x_2708_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
lean_inc(v_a_2549_);
v___x_2711_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2540_, v_val_2541_, v_a_2549_, v___x_2583_, v_a_2710_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
v___y_2562_ = v___x_2711_;
goto v___jp_2561_;
}
else
{
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
return v___x_2709_;
}
}
}
}
}
else
{
lean_del_object(v___x_2630_);
v_a_2557_ = v___x_2583_;
goto v___jp_2556_;
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_del_object(v___x_2630_);
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
v_a_2713_ = lean_ctor_get(v___y_2675_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___y_2675_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___y_2675_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___y_2675_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
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
lean_object* v___x_2730_; uint8_t v___x_2731_; lean_object* v___x_2732_; 
lean_dec(v___x_2627_);
v___x_2730_ = lean_unsigned_to_nat(0u);
v___x_2731_ = 0;
lean_inc(v___x_2624_);
lean_inc(v_a_2549_);
v___x_2732_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2540_, v_val_2541_, v_a_2549_, v_next_2545_, v___x_2547_, v___x_2548_, v___x_2547_, v_params_2546_, v___x_2624_, v___x_2730_, v___x_2731_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; uint8_t v___x_2734_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = lean_unbox(v_a_2733_);
lean_dec(v_a_2733_);
if (v___x_2734_ == 0)
{
lean_object* v_toCold_2735_; lean_object* v_options_2736_; uint8_t v_hasTrace_2737_; 
v_toCold_2735_ = lean_ctor_get(v___y_2553_, 0);
v_options_2736_ = lean_ctor_get(v_toCold_2735_, 2);
v_hasTrace_2737_ = lean_ctor_get_uint8(v_options_2736_, sizeof(void*)*1);
if (v_hasTrace_2737_ == 0)
{
goto v___jp_2584_;
}
else
{
lean_object* v_inheritedTraceOptions_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; 
v_inheritedTraceOptions_2738_ = lean_ctor_get(v_toCold_2735_, 11);
v___x_2739_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2740_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2741_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2738_, v_options_2736_, v___x_2740_);
if (v___x_2741_ == 0)
{
goto v___jp_2584_;
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2742_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2541_);
v___x_2743_ = l_Nat_reprFast(v_val_2541_);
v___x_2744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
v___x_2745_ = l_Lean_MessageData_ofFormat(v___x_2744_);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2742_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
lean_inc(v_a_2549_);
v___x_2749_ = l_Nat_reprFast(v_a_2549_);
v___x_2750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
v___x_2751_ = l_Lean_MessageData_ofFormat(v___x_2750_);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2748_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
lean_inc_ref(v_e_2544_);
v___x_2755_ = l_Lean_MessageData_ofExpr(v_e_2544_);
v___x_2756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_inc(v___x_2624_);
v___x_2759_ = l_Lean_MessageData_ofExpr(v___x_2624_);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2739_, v___x_2762_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
lean_inc(v_a_2549_);
v___x_2765_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2540_, v_val_2541_, v_a_2549_, v___x_2583_, v_a_2764_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
v___y_2562_ = v___x_2765_;
goto v___jp_2561_;
}
else
{
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
return v___x_2763_;
}
}
}
}
else
{
v_a_2557_ = v___x_2583_;
goto v___jp_2556_;
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
v_a_2766_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2732_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2732_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
v_a_2774_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2625_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2625_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
v_a_2782_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2591_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2591_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
v___jp_2584_:
{
lean_object* v___x_2585_; 
lean_inc(v_a_2549_);
v___x_2585_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2540_, v_val_2541_, v_a_2549_, v___x_2583_, v___x_2583_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
v___y_2562_ = v___x_2585_;
goto v___jp_2561_;
}
v___jp_2586_:
{
lean_object* v___x_2587_; 
lean_inc(v_a_2549_);
v___x_2587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2540_, v_val_2541_, v_a_2549_, v___x_2583_, v___x_2583_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
v___y_2562_ = v___x_2587_;
goto v___jp_2561_;
}
v___jp_2588_:
{
lean_object* v___x_2589_; 
lean_inc(v_a_2549_);
v___x_2589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2540_, v_val_2541_, v_a_2549_, v___x_2583_, v___x_2583_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
v___y_2562_ = v___x_2589_;
goto v___jp_2561_;
}
}
v___jp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_unsigned_to_nat(1u);
v___x_2559_ = lean_nat_add(v_a_2549_, v___x_2558_);
lean_dec(v_a_2549_);
v_a_2549_ = v___x_2559_;
v_b_2550_ = v_a_2557_;
goto _start;
}
v___jp_2561_:
{
if (lean_obj_tag(v___y_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2572_; 
v_a_2563_ = lean_ctor_get(v___y_2562_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___y_2562_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2565_ = v___y_2562_;
v_isShared_2566_ = v_isSharedCheck_2572_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___y_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2572_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
if (lean_obj_tag(v_a_2563_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
v_a_2567_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v_a_2563_, 1);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v_a_2567_);
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
else
{
lean_object* v_a_2571_; 
lean_del_object(v___x_2565_);
v_a_2571_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v_a_2563_, 1);
v_a_2557_ = v_a_2571_;
goto v___jp_2556_;
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_a_2549_);
lean_dec_ref(v_e_2544_);
lean_dec(v_val_2541_);
v_a_2573_ = lean_ctor_get(v___y_2562_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___y_2562_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___y_2562_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___y_2562_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2790_, lean_object* v_val_2791_, lean_object* v_upperBound_2792_, lean_object* v_args_2793_, lean_object* v_e_2794_, lean_object* v_next_2795_, lean_object* v_params_2796_, lean_object* v___x_2797_, lean_object* v___x_2798_, lean_object* v_a_2799_, lean_object* v_b_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2790_, v_val_2791_, v_upperBound_2792_, v_args_2793_, v_e_2794_, v_next_2795_, v_params_2796_, v___x_2797_, v___x_2798_, v_a_2799_, v_b_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___x_2798_);
lean_dec(v___x_2797_);
lean_dec_ref(v_params_2796_);
lean_dec(v_next_2795_);
lean_dec_ref(v_args_2793_);
lean_dec(v_upperBound_2792_);
lean_dec(v_val_2790_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2809_, lean_object* v___x_2810_, lean_object* v_val_2811_, lean_object* v_e_2812_, lean_object* v_next_2813_, lean_object* v_params_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 5)
{
lean_object* v_fn_2825_; lean_object* v_arg_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_fn_2825_ = lean_ctor_get(v_x_2817_, 0);
lean_inc_ref(v_fn_2825_);
v_arg_2826_ = lean_ctor_get(v_x_2817_, 1);
lean_inc_ref(v_arg_2826_);
lean_dec_ref_known(v_x_2817_, 2);
v___x_2827_ = lean_array_set(v_x_2818_, v_x_2819_, v_arg_2826_);
v___x_2828_ = lean_unsigned_to_nat(1u);
v___x_2829_ = lean_nat_sub(v_x_2819_, v___x_2828_);
lean_dec(v_x_2819_);
v_x_2817_ = v_fn_2825_;
v_x_2818_ = v___x_2827_;
v_x_2819_ = v___x_2829_;
goto _start;
}
else
{
uint8_t v___x_2831_; 
lean_dec(v_x_2819_);
v___x_2831_ = l_Lean_Expr_isConst(v_x_2817_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
lean_dec_ref(v_x_2818_);
lean_dec_ref(v_x_2817_);
lean_dec_ref(v_e_2812_);
v___x_2832_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2834_ = l_Lean_Expr_constName_x21(v_x_2817_);
lean_dec_ref(v_x_2817_);
v___x_2835_ = lean_unsigned_to_nat(0u);
v___x_2836_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2834_, v_preDefs_2809_, v___x_2835_);
lean_dec(v___x_2834_);
if (lean_obj_tag(v___x_2836_) == 1)
{
lean_object* v_val_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v_val_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_array_get_borrowed(v___x_2835_, v___x_2810_, v_val_2837_);
v___x_2840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2811_, v_val_2837_, v___x_2839_, v_x_2818_, v_e_2812_, v_next_2813_, v_params_2814_, v___x_2815_, v___x_2816_, v___x_2835_, v___x_2838_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec_ref(v_x_2818_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2848_; 
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; 
v_unused_2849_ = lean_ctor_get(v___x_2840_, 0);
lean_dec(v_unused_2849_);
v___x_2842_ = v___x_2840_;
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
else
{
lean_dec(v___x_2840_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2848_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2844_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2844_);
v___x_2846_ = v___x_2842_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
v_a_2850_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2840_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2840_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec(v___x_2836_);
lean_dec_ref(v_x_2818_);
lean_dec_ref(v_e_2812_);
v___x_2858_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
return v___x_2859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2860_, lean_object* v___x_2861_, lean_object* v_val_2862_, lean_object* v_e_2863_, lean_object* v_next_2864_, lean_object* v_params_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v_x_2868_, lean_object* v_x_2869_, lean_object* v_x_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2860_, v___x_2861_, v_val_2862_, v_e_2863_, v_next_2864_, v_params_2865_, v___x_2866_, v___x_2867_, v_x_2868_, v_x_2869_, v_x_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec_ref(v_params_2865_);
lean_dec(v_next_2864_);
lean_dec(v_val_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v_preDefs_2860_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2877_, lean_object* v___x_2878_, lean_object* v_val_2879_, lean_object* v_a_2880_, lean_object* v_params_2881_, lean_object* v___x_2882_, lean_object* v___x_2883_, lean_object* v_e_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_dummy_2890_; lean_object* v_nargs_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_dummy_2890_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2891_ = l_Lean_Expr_getAppNumArgs(v_e_2884_);
lean_inc(v_nargs_2891_);
v___x_2892_ = lean_mk_array(v_nargs_2891_, v_dummy_2890_);
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = lean_nat_sub(v_nargs_2891_, v___x_2893_);
lean_dec(v_nargs_2891_);
lean_inc_ref(v_e_2884_);
v___x_2895_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2877_, v___x_2878_, v_val_2879_, v_e_2884_, v_a_2880_, v_params_2881_, v___x_2882_, v___x_2883_, v_e_2884_, v___x_2892_, v___x_2894_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2896_, lean_object* v___x_2897_, lean_object* v_val_2898_, lean_object* v_a_2899_, lean_object* v_params_2900_, lean_object* v___x_2901_, lean_object* v___x_2902_, lean_object* v_e_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2896_, v___x_2897_, v_val_2898_, v_a_2899_, v_params_2900_, v___x_2901_, v___x_2902_, v_e_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___x_2902_);
lean_dec(v___x_2901_);
lean_dec_ref(v_params_2900_);
lean_dec(v_a_2899_);
lean_dec(v_val_2898_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v_preDefs_2896_);
return v_res_2909_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2913_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2914_ = lean_unsigned_to_nat(6u);
v___x_2915_ = lean_unsigned_to_nat(201u);
v___x_2916_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2917_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2918_ = l_mkPanicMessageWithDecl(v___x_2917_, v___x_2916_, v___x_2915_, v___x_2914_, v___x_2913_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2919_, lean_object* v___x_2920_, lean_object* v_a_2921_, lean_object* v_preDefs_2922_, lean_object* v_val_2923_, lean_object* v___f_2924_, lean_object* v___x_2925_, lean_object* v_params_2926_, lean_object* v_body_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
v___x_2933_ = lean_array_get_size(v_params_2926_);
v___x_2934_ = lean_array_get(v___x_2919_, v___x_2920_, v_a_2921_);
v___x_2935_ = lean_nat_dec_eq(v___x_2933_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
lean_dec(v___x_2934_);
lean_dec_ref(v_body_2927_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v___f_2924_);
lean_dec(v_val_2923_);
lean_dec_ref(v_preDefs_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v___x_2920_);
v___x_2936_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2937_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2936_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
return v___x_2937_;
}
else
{
lean_object* v___f_2938_; uint8_t v___x_2939_; lean_object* v___x_2940_; 
v___f_2938_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2938_, 0, v_preDefs_2922_);
lean_closure_set(v___f_2938_, 1, v___x_2920_);
lean_closure_set(v___f_2938_, 2, v_val_2923_);
lean_closure_set(v___f_2938_, 3, v_a_2921_);
lean_closure_set(v___f_2938_, 4, v_params_2926_);
lean_closure_set(v___f_2938_, 5, v___x_2933_);
lean_closure_set(v___f_2938_, 6, v___x_2934_);
v___x_2939_ = 0;
v___x_2940_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2927_, v___f_2938_, v___f_2924_, v___x_2939_, v___x_2935_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2947_ == 0)
{
lean_object* v_unused_2948_; 
v_unused_2948_ = lean_ctor_get(v___x_2940_, 0);
lean_dec(v_unused_2948_);
v___x_2942_ = v___x_2940_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_dec(v___x_2940_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2925_);
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2925_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_a_2949_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2940_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2940_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2957_, lean_object* v___x_2958_, lean_object* v_a_2959_, lean_object* v_preDefs_2960_, lean_object* v_val_2961_, lean_object* v___f_2962_, lean_object* v___x_2963_, lean_object* v_params_2964_, lean_object* v_body_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2957_, v___x_2958_, v_a_2959_, v_preDefs_2960_, v_val_2961_, v___f_2962_, v___x_2963_, v_params_2964_, v_body_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___x_2957_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_e_2972_);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v___x_2988_, lean_object* v_preDefs_2989_, lean_object* v_val_2990_, lean_object* v_upperBound_2991_, lean_object* v_a_2992_, lean_object* v_b_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v___x_2999_; 
v___x_2999_ = lean_nat_dec_lt(v_a_2992_, v_upperBound_2991_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; 
lean_dec(v_a_2992_);
lean_dec(v_val_2990_);
lean_dec_ref(v_preDefs_2989_);
lean_dec_ref(v___x_2988_);
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v_b_2993_);
return v___x_3000_;
}
else
{
lean_object* v___x_3001_; lean_object* v_value_3002_; lean_object* v___f_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___f_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; 
v___x_3001_ = lean_array_fget_borrowed(v_preDefs_2989_, v_a_2992_);
v_value_3002_ = lean_ctor_get(v___x_3001_, 7);
v___f_3003_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = lean_box(0);
lean_inc(v_val_2990_);
lean_inc_ref(v_preDefs_2989_);
lean_inc(v_a_2992_);
lean_inc_ref(v___x_2988_);
v___f_3006_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3006_, 0, v___x_3004_);
lean_closure_set(v___f_3006_, 1, v___x_2988_);
lean_closure_set(v___f_3006_, 2, v_a_2992_);
lean_closure_set(v___f_3006_, 3, v_preDefs_2989_);
lean_closure_set(v___f_3006_, 4, v_val_2990_);
lean_closure_set(v___f_3006_, 5, v___f_3003_);
lean_closure_set(v___f_3006_, 6, v___x_3005_);
v___x_3007_ = 0;
lean_inc_ref(v_value_3002_);
v___x_3008_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3002_, v___f_3006_, v___x_3007_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec_ref_known(v___x_3008_, 1);
v___x_3009_ = lean_unsigned_to_nat(1u);
v___x_3010_ = lean_nat_add(v_a_2992_, v___x_3009_);
lean_dec(v_a_2992_);
v_a_2992_ = v___x_3010_;
v_b_2993_ = v___x_3005_;
goto _start;
}
else
{
lean_dec(v_a_2992_);
lean_dec(v_val_2990_);
lean_dec_ref(v_preDefs_2989_);
lean_dec_ref(v___x_2988_);
return v___x_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v___x_3012_, lean_object* v_preDefs_3013_, lean_object* v_val_3014_, lean_object* v_upperBound_3015_, lean_object* v_a_3016_, lean_object* v_b_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3012_, v_preDefs_3013_, v_val_3014_, v_upperBound_3015_, v_a_3016_, v_b_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v_upperBound_3015_);
return v_res_3023_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3026_ = l_Lean_stringToMessageData(v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
size_t v_sz_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v_sz_3033_ = lean_array_size(v_preDefs_3027_);
v___x_3034_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3027_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3033_, v___x_3034_, v_preDefs_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; size_t v_sz_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc_n(v_a_3036_, 2);
lean_dec_ref_known(v___x_3035_, 1);
v_sz_3037_ = lean_array_size(v_a_3036_);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3037_, v___x_3034_, v_a_3036_);
v___x_3039_ = l_Lean_Elab_FixedParams_Info_init(v_a_3036_);
v___x_3040_ = lean_st_mk_ref(v___x_3039_);
v___x_3041_ = lean_st_ref_take(v___x_3040_);
v___x_3042_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3041_);
v___x_3043_ = lean_st_ref_put(v___x_3040_, v___x_3042_);
v___x_3044_ = lean_array_get_size(v_preDefs_3027_);
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = lean_box(0);
lean_inc(v___x_3040_);
v___x_3047_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3038_, v_preDefs_3027_, v___x_3040_, v___x_3044_, v___x_3045_, v___x_3046_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3087_; 
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3047_, 0);
lean_dec(v_unused_3088_);
v___x_3049_ = v___x_3047_;
v_isShared_3050_ = v_isSharedCheck_3087_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v___x_3047_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3087_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3051_; lean_object* v_toCold_3052_; lean_object* v_options_3053_; uint8_t v_hasTrace_3054_; 
v___x_3051_ = lean_st_ref_get(v___x_3040_);
lean_dec(v___x_3040_);
v_toCold_3052_ = lean_ctor_get(v_a_3030_, 0);
v_options_3053_ = lean_ctor_get(v_toCold_3052_, 2);
v_hasTrace_3054_ = lean_ctor_get_uint8(v_options_3053_, sizeof(void*)*1);
if (v_hasTrace_3054_ == 0)
{
lean_object* v___x_3056_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3051_);
v___x_3056_ = v___x_3049_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3051_);
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
lean_object* v_inheritedTraceOptions_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v_inheritedTraceOptions_3058_ = lean_ctor_get(v_toCold_3052_, 11);
v___x_3059_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3060_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3061_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3058_, v_options_3053_, v___x_3060_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3063_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 0, v___x_3051_);
v___x_3063_ = v___x_3049_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3051_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_del_object(v___x_3049_);
v___x_3065_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3051_);
v___x_3066_ = l_Lean_Elab_FixedParams_Info_format(v___x_3051_);
v___x_3067_ = l_Std_Format_indentD(v___x_3066_);
v___x_3068_ = l_Lean_MessageData_ofFormat(v___x_3067_);
v___x_3069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3065_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v___x_3070_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3059_, v___x_3069_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3070_, 0);
lean_dec(v_unused_3078_);
v___x_3072_ = v___x_3070_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_dec(v___x_3070_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3051_);
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3051_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v___x_3051_);
v_a_3079_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3070_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3070_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v___x_3040_);
v_a_3089_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3047_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3047_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v_preDefs_3027_);
v_a_3097_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3035_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3035_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3112_, lean_object* v_val_3113_, lean_object* v_next_3114_, lean_object* v_next_3115_, lean_object* v___x_3116_, lean_object* v___x_3117_, lean_object* v_upperBound_3118_, lean_object* v_params_3119_, lean_object* v___x_3120_, lean_object* v_inst_3121_, lean_object* v_R_3122_, lean_object* v_a_3123_, uint8_t v_b_3124_, lean_object* v_c_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3112_, v_val_3113_, v_next_3114_, v_next_3115_, v___x_3116_, v___x_3117_, v_upperBound_3118_, v_params_3119_, v___x_3120_, v_a_3123_, v_b_3124_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3132_ = _args[0];
lean_object* v_val_3133_ = _args[1];
lean_object* v_next_3134_ = _args[2];
lean_object* v_next_3135_ = _args[3];
lean_object* v___x_3136_ = _args[4];
lean_object* v___x_3137_ = _args[5];
lean_object* v_upperBound_3138_ = _args[6];
lean_object* v_params_3139_ = _args[7];
lean_object* v___x_3140_ = _args[8];
lean_object* v_inst_3141_ = _args[9];
lean_object* v_R_3142_ = _args[10];
lean_object* v_a_3143_ = _args[11];
lean_object* v_b_3144_ = _args[12];
lean_object* v_c_3145_ = _args[13];
lean_object* v___y_3146_ = _args[14];
lean_object* v___y_3147_ = _args[15];
lean_object* v___y_3148_ = _args[16];
lean_object* v___y_3149_ = _args[17];
lean_object* v___y_3150_ = _args[18];
_start:
{
uint8_t v_b_boxed_3151_; lean_object* v_res_3152_; 
v_b_boxed_3151_ = lean_unbox(v_b_3144_);
v_res_3152_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3132_, v_val_3133_, v_next_3134_, v_next_3135_, v___x_3136_, v___x_3137_, v_upperBound_3138_, v_params_3139_, v___x_3140_, v_inst_3141_, v_R_3142_, v_a_3143_, v_b_boxed_3151_, v_c_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_params_3139_);
lean_dec(v_upperBound_3138_);
lean_dec(v___x_3137_);
lean_dec(v___x_3136_);
lean_dec(v_next_3135_);
lean_dec(v_val_3133_);
lean_dec(v_val_3132_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3153_, lean_object* v_val_3154_, lean_object* v_upperBound_3155_, lean_object* v_args_3156_, lean_object* v_e_3157_, lean_object* v_next_3158_, lean_object* v_params_3159_, lean_object* v___x_3160_, lean_object* v___x_3161_, lean_object* v_inst_3162_, lean_object* v_R_3163_, lean_object* v_a_3164_, lean_object* v_b_3165_, lean_object* v_c_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3153_, v_val_3154_, v_upperBound_3155_, v_args_3156_, v_e_3157_, v_next_3158_, v_params_3159_, v___x_3160_, v___x_3161_, v_a_3164_, v_b_3165_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3173_ = _args[0];
lean_object* v_val_3174_ = _args[1];
lean_object* v_upperBound_3175_ = _args[2];
lean_object* v_args_3176_ = _args[3];
lean_object* v_e_3177_ = _args[4];
lean_object* v_next_3178_ = _args[5];
lean_object* v_params_3179_ = _args[6];
lean_object* v___x_3180_ = _args[7];
lean_object* v___x_3181_ = _args[8];
lean_object* v_inst_3182_ = _args[9];
lean_object* v_R_3183_ = _args[10];
lean_object* v_a_3184_ = _args[11];
lean_object* v_b_3185_ = _args[12];
lean_object* v_c_3186_ = _args[13];
lean_object* v___y_3187_ = _args[14];
lean_object* v___y_3188_ = _args[15];
lean_object* v___y_3189_ = _args[16];
lean_object* v___y_3190_ = _args[17];
lean_object* v___y_3191_ = _args[18];
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3173_, v_val_3174_, v_upperBound_3175_, v_args_3176_, v_e_3177_, v_next_3178_, v_params_3179_, v___x_3180_, v___x_3181_, v_inst_3182_, v_R_3183_, v_a_3184_, v_b_3185_, v_c_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___x_3181_);
lean_dec(v___x_3180_);
lean_dec_ref(v_params_3179_);
lean_dec(v_next_3178_);
lean_dec_ref(v_args_3176_);
lean_dec(v_upperBound_3175_);
lean_dec(v_val_3173_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v___x_3193_, lean_object* v_preDefs_3194_, lean_object* v_val_3195_, lean_object* v_upperBound_3196_, lean_object* v_inst_3197_, lean_object* v_R_3198_, lean_object* v_a_3199_, lean_object* v_b_3200_, lean_object* v_c_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3193_, v_preDefs_3194_, v_val_3195_, v_upperBound_3196_, v_a_3199_, v_b_3200_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v___x_3208_, lean_object* v_preDefs_3209_, lean_object* v_val_3210_, lean_object* v_upperBound_3211_, lean_object* v_inst_3212_, lean_object* v_R_3213_, lean_object* v_a_3214_, lean_object* v_b_3215_, lean_object* v_c_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3208_, v_preDefs_3209_, v_val_3210_, v_upperBound_3211_, v_inst_3212_, v_R_3213_, v_a_3214_, v_b_3215_, v_c_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v_upperBound_3211_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3223_, lean_object* v___x_3224_, lean_object* v_pre_3225_, lean_object* v_post_3226_, uint8_t v_usedLetOnly_3227_, uint8_t v_skipConstInApp_3228_, uint8_t v_skipInstances_3229_, lean_object* v___x_3230_, lean_object* v_inst_3231_, lean_object* v_R_3232_, lean_object* v_a_3233_, lean_object* v_b_3234_, lean_object* v_c_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3223_, v___x_3224_, v_pre_3225_, v_post_3226_, v_usedLetOnly_3227_, v_skipConstInApp_3228_, v_skipInstances_3229_, v_a_3233_, v_b_3234_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3243_ = _args[0];
lean_object* v___x_3244_ = _args[1];
lean_object* v_pre_3245_ = _args[2];
lean_object* v_post_3246_ = _args[3];
lean_object* v_usedLetOnly_3247_ = _args[4];
lean_object* v_skipConstInApp_3248_ = _args[5];
lean_object* v_skipInstances_3249_ = _args[6];
lean_object* v___x_3250_ = _args[7];
lean_object* v_inst_3251_ = _args[8];
lean_object* v_R_3252_ = _args[9];
lean_object* v_a_3253_ = _args[10];
lean_object* v_b_3254_ = _args[11];
lean_object* v_c_3255_ = _args[12];
lean_object* v___y_3256_ = _args[13];
lean_object* v___y_3257_ = _args[14];
lean_object* v___y_3258_ = _args[15];
lean_object* v___y_3259_ = _args[16];
lean_object* v___y_3260_ = _args[17];
lean_object* v___y_3261_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3262_; uint8_t v_skipConstInApp_boxed_3263_; uint8_t v_skipInstances_boxed_3264_; lean_object* v_res_3265_; 
v_usedLetOnly_boxed_3262_ = lean_unbox(v_usedLetOnly_3247_);
v_skipConstInApp_boxed_3263_ = lean_unbox(v_skipConstInApp_3248_);
v_skipInstances_boxed_3264_ = lean_unbox(v_skipInstances_3249_);
v_res_3265_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3243_, v___x_3244_, v_pre_3245_, v_post_3246_, v_usedLetOnly_boxed_3262_, v_skipConstInApp_boxed_3263_, v_skipInstances_boxed_3264_, v___x_3250_, v_inst_3251_, v_R_3252_, v_a_3253_, v_b_3254_, v_c_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec(v___x_3250_);
lean_dec_ref(v___x_3244_);
lean_dec(v_upperBound_3243_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3266_, lean_object* v_m_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3267_, v_a_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3270_, lean_object* v_m_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3270_, v_m_3271_, v_a_3272_);
lean_dec_ref(v_a_3272_);
lean_dec_ref(v_m_3271_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3274_, lean_object* v_name_3275_, uint8_t v_bi_3276_, lean_object* v_type_3277_, lean_object* v_k_3278_, uint8_t v_kind_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3275_, v_bi_3276_, v_type_3277_, v_k_3278_, v_kind_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3287_, lean_object* v_name_3288_, lean_object* v_bi_3289_, lean_object* v_type_3290_, lean_object* v_k_3291_, lean_object* v_kind_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
uint8_t v_bi_boxed_3299_; uint8_t v_kind_boxed_3300_; lean_object* v_res_3301_; 
v_bi_boxed_3299_ = lean_unbox(v_bi_3289_);
v_kind_boxed_3300_ = lean_unbox(v_kind_3292_);
v_res_3301_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3287_, v_name_3288_, v_bi_boxed_3299_, v_type_3290_, v_k_3291_, v_kind_boxed_3300_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3302_, lean_object* v_name_3303_, lean_object* v_type_3304_, lean_object* v_val_3305_, lean_object* v_k_3306_, uint8_t v_nondep_3307_, uint8_t v_kind_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3303_, v_type_3304_, v_val_3305_, v_k_3306_, v_nondep_3307_, v_kind_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3316_, lean_object* v_name_3317_, lean_object* v_type_3318_, lean_object* v_val_3319_, lean_object* v_k_3320_, lean_object* v_nondep_3321_, lean_object* v_kind_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v_nondep_boxed_3329_; uint8_t v_kind_boxed_3330_; lean_object* v_res_3331_; 
v_nondep_boxed_3329_ = lean_unbox(v_nondep_3321_);
v_kind_boxed_3330_ = lean_unbox(v_kind_3322_);
v_res_3331_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3316_, v_name_3317_, v_type_3318_, v_val_3319_, v_k_3320_, v_nondep_boxed_3329_, v_kind_boxed_3330_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3332_, lean_object* v_ref_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3333_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3340_, lean_object* v_ref_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3340_, v_ref_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3348_, lean_object* v_x_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3357_, lean_object* v_x_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3357_, v_x_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3366_, lean_object* v_m_3367_, lean_object* v_a_3368_, lean_object* v_b_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3367_, v_a_3368_, v_b_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3371_, lean_object* v_a_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3372_, v_x_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3375_, lean_object* v_a_3376_, lean_object* v_x_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3375_, v_a_3376_, v_x_3377_);
lean_dec(v_x_3377_);
lean_dec_ref(v_a_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3379_, lean_object* v_a_3380_, lean_object* v_x_3381_){
_start:
{
uint8_t v___x_3382_; 
v___x_3382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3380_, v_x_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3383_, lean_object* v_a_3384_, lean_object* v_x_3385_){
_start:
{
uint8_t v_res_3386_; lean_object* v_r_3387_; 
v_res_3386_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3383_, v_a_3384_, v_x_3385_);
lean_dec(v_x_3385_);
lean_dec_ref(v_a_3384_);
v_r_3387_ = lean_box(v_res_3386_);
return v_r_3387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3388_, lean_object* v_data_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3391_, lean_object* v_a_3392_, lean_object* v_b_3393_, lean_object* v_x_3394_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3392_, v_b_3393_, v_x_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3396_, lean_object* v_i_3397_, lean_object* v_source_3398_, lean_object* v_target_3399_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3397_, v_source_3398_, v_target_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3401_, lean_object* v_x_3402_, lean_object* v_x_3403_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3402_, v_x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3418_, lean_object* v_x_3419_){
_start:
{
if (lean_obj_tag(v_x_3418_) == 0)
{
lean_object* v___x_3420_; 
v___x_3420_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3420_;
}
else
{
lean_object* v_val_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3432_; 
v_val_3421_ = lean_ctor_get(v_x_3418_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_x_3418_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3423_ = v_x_3418_;
v_isShared_3424_ = v_isSharedCheck_3432_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_val_3421_);
lean_dec(v_x_3418_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3432_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3428_; 
v___x_3425_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3426_ = l_Nat_reprFast(v_val_3421_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set_tag(v___x_3423_, 3);
lean_ctor_set(v___x_3423_, 0, v___x_3426_);
v___x_3428_ = v___x_3423_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3425_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = l_Repr_addAppParen(v___x_3429_, v_x_3419_);
return v___x_3430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3433_, lean_object* v_x_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3433_, v_x_3434_);
lean_dec(v_x_3434_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3436_, lean_object* v_x_3437_, lean_object* v_x_3438_){
_start:
{
if (lean_obj_tag(v_x_3438_) == 0)
{
lean_dec(v_x_3436_);
return v_x_3437_;
}
else
{
lean_object* v_head_3439_; lean_object* v_tail_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3451_; 
v_head_3439_ = lean_ctor_get(v_x_3438_, 0);
v_tail_3440_ = lean_ctor_get(v_x_3438_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_x_3438_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3442_ = v_x_3438_;
v_isShared_3443_ = v_isSharedCheck_3451_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_tail_3440_);
lean_inc(v_head_3439_);
lean_dec(v_x_3438_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3451_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
lean_inc(v_x_3436_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set_tag(v___x_3442_, 5);
lean_ctor_set(v___x_3442_, 1, v_x_3436_);
lean_ctor_set(v___x_3442_, 0, v_x_3437_);
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_x_3437_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_x_3436_);
v___x_3445_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3439_, v___x_3446_);
v___x_3448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3445_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v_x_3437_ = v___x_3448_;
v_x_3438_ = v_tail_3440_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3452_, lean_object* v_x_3453_, lean_object* v_x_3454_){
_start:
{
if (lean_obj_tag(v_x_3454_) == 0)
{
lean_dec(v_x_3452_);
return v_x_3453_;
}
else
{
lean_object* v_head_3455_; lean_object* v_tail_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3467_; 
v_head_3455_ = lean_ctor_get(v_x_3454_, 0);
v_tail_3456_ = lean_ctor_get(v_x_3454_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_x_3454_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3458_ = v_x_3454_;
v_isShared_3459_ = v_isSharedCheck_3467_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_tail_3456_);
lean_inc(v_head_3455_);
lean_dec(v_x_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3467_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
lean_inc(v_x_3452_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 5);
lean_ctor_set(v___x_3458_, 1, v_x_3452_);
lean_ctor_set(v___x_3458_, 0, v_x_3453_);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_x_3453_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_x_3452_);
v___x_3461_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3462_ = lean_unsigned_to_nat(0u);
v___x_3463_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3455_, v___x_3462_);
v___x_3464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3461_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3452_, v___x_3464_, v_tail_3456_);
return v___x_3465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3468_){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3469_ = lean_unsigned_to_nat(0u);
v___x_3470_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3468_, v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3471_, lean_object* v_x_3472_){
_start:
{
if (lean_obj_tag(v_x_3471_) == 0)
{
lean_object* v___x_3473_; 
lean_dec(v_x_3472_);
v___x_3473_ = lean_box(0);
return v___x_3473_;
}
else
{
lean_object* v_tail_3474_; 
v_tail_3474_ = lean_ctor_get(v_x_3471_, 1);
if (lean_obj_tag(v_tail_3474_) == 0)
{
lean_object* v_head_3475_; lean_object* v___x_3476_; 
lean_dec(v_x_3472_);
v_head_3475_ = lean_ctor_get(v_x_3471_, 0);
lean_inc(v_head_3475_);
lean_dec_ref_known(v_x_3471_, 2);
v___x_3476_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3475_);
return v___x_3476_;
}
else
{
lean_object* v_head_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_inc(v_tail_3474_);
v_head_3477_ = lean_ctor_get(v_x_3471_, 0);
lean_inc(v_head_3477_);
lean_dec_ref_known(v_x_3471_, 2);
v___x_3478_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3477_);
v___x_3479_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3472_, v___x_3478_, v_tail_3474_);
return v___x_3479_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3488_ = lean_string_length(v___x_3487_);
return v___x_3488_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3490_ = lean_nat_to_int(v___x_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3496_){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; 
v___x_3497_ = lean_array_get_size(v_xs_3496_);
v___x_3498_ = lean_unsigned_to_nat(0u);
v___x_3499_ = lean_nat_dec_eq(v___x_3497_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3500_ = lean_array_to_list(v_xs_3496_);
v___x_3501_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3502_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3500_, v___x_3501_);
v___x_3503_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3504_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v___x_3502_);
v___x_3506_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3503_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
v___x_3509_ = l_Std_Format_fill(v___x_3508_);
return v___x_3509_;
}
else
{
lean_object* v___x_3510_; 
lean_dec_ref(v_xs_3496_);
v___x_3510_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3510_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3511_, lean_object* v_x_3512_, lean_object* v_x_3513_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 0)
{
lean_dec(v_x_3511_);
return v_x_3512_;
}
else
{
lean_object* v_head_3514_; lean_object* v_tail_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3525_; 
v_head_3514_ = lean_ctor_get(v_x_3513_, 0);
v_tail_3515_ = lean_ctor_get(v_x_3513_, 1);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_x_3513_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3517_ = v_x_3513_;
v_isShared_3518_ = v_isSharedCheck_3525_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_tail_3515_);
lean_inc(v_head_3514_);
lean_dec(v_x_3513_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3525_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
lean_inc(v_x_3511_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set_tag(v___x_3517_, 5);
lean_ctor_set(v___x_3517_, 1, v_x_3511_);
lean_ctor_set(v___x_3517_, 0, v_x_3512_);
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_x_3512_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_x_3511_);
v___x_3520_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3514_);
v___x_3522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v_x_3512_ = v___x_3522_;
v_x_3513_ = v_tail_3515_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3526_, lean_object* v_x_3527_){
_start:
{
if (lean_obj_tag(v_x_3526_) == 0)
{
lean_object* v___x_3528_; 
lean_dec(v_x_3527_);
v___x_3528_ = lean_box(0);
return v___x_3528_;
}
else
{
lean_object* v_tail_3529_; 
v_tail_3529_ = lean_ctor_get(v_x_3526_, 1);
if (lean_obj_tag(v_tail_3529_) == 0)
{
lean_object* v_head_3530_; lean_object* v___x_3531_; 
lean_dec(v_x_3527_);
v_head_3530_ = lean_ctor_get(v_x_3526_, 0);
lean_inc(v_head_3530_);
lean_dec_ref_known(v_x_3526_, 2);
v___x_3531_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3530_);
return v___x_3531_;
}
else
{
lean_object* v_head_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_inc(v_tail_3529_);
v_head_3532_ = lean_ctor_get(v_x_3526_, 0);
lean_inc(v_head_3532_);
lean_dec_ref_known(v_x_3526_, 2);
v___x_3533_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3532_);
v___x_3534_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3527_, v___x_3533_, v_tail_3529_);
return v___x_3534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3535_){
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
v___x_3541_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3539_, v___x_3540_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_){
_start:
{
if (lean_obj_tag(v_x_3552_) == 0)
{
lean_dec(v_x_3550_);
return v_x_3551_;
}
else
{
lean_object* v_head_3553_; lean_object* v_tail_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3565_; 
v_head_3553_ = lean_ctor_get(v_x_3552_, 0);
v_tail_3554_ = lean_ctor_get(v_x_3552_, 1);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_x_3552_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3556_ = v_x_3552_;
v_isShared_3557_ = v_isSharedCheck_3565_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_tail_3554_);
lean_inc(v_head_3553_);
lean_dec(v_x_3552_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3565_;
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
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_x_3551_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_x_3550_);
v___x_3559_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = l_Nat_reprFast(v_head_3553_);
v___x_3561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
v___x_3562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3559_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v_x_3551_ = v___x_3562_;
v_x_3552_ = v_tail_3554_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3566_, lean_object* v_x_3567_, lean_object* v_x_3568_){
_start:
{
if (lean_obj_tag(v_x_3568_) == 0)
{
lean_dec(v_x_3566_);
return v_x_3567_;
}
else
{
lean_object* v_head_3569_; lean_object* v_tail_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3581_; 
v_head_3569_ = lean_ctor_get(v_x_3568_, 0);
v_tail_3570_ = lean_ctor_get(v_x_3568_, 1);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_x_3568_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3572_ = v_x_3568_;
v_isShared_3573_ = v_isSharedCheck_3581_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_tail_3570_);
lean_inc(v_head_3569_);
lean_dec(v_x_3568_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3581_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
lean_inc(v_x_3566_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set_tag(v___x_3572_, 5);
lean_ctor_set(v___x_3572_, 1, v_x_3566_);
lean_ctor_set(v___x_3572_, 0, v_x_3567_);
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_x_3567_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_x_3566_);
v___x_3575_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3576_ = l_Nat_reprFast(v_head_3569_);
v___x_3577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
v___x_3578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3575_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3566_, v___x_3578_, v_tail_3570_);
return v___x_3579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3582_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = l_Nat_reprFast(v___y_3582_);
v___x_3584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3585_, lean_object* v_x_3586_){
_start:
{
if (lean_obj_tag(v_x_3585_) == 0)
{
lean_object* v___x_3587_; 
lean_dec(v_x_3586_);
v___x_3587_ = lean_box(0);
return v___x_3587_;
}
else
{
lean_object* v_tail_3588_; 
v_tail_3588_ = lean_ctor_get(v_x_3585_, 1);
if (lean_obj_tag(v_tail_3588_) == 0)
{
lean_object* v_head_3589_; lean_object* v___x_3590_; 
lean_dec(v_x_3586_);
v_head_3589_ = lean_ctor_get(v_x_3585_, 0);
lean_inc(v_head_3589_);
lean_dec_ref_known(v_x_3585_, 2);
v___x_3590_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3589_);
return v___x_3590_;
}
else
{
lean_object* v_head_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_inc(v_tail_3588_);
v_head_3591_ = lean_ctor_get(v_x_3585_, 0);
lean_inc(v_head_3591_);
lean_dec_ref_known(v_x_3585_, 2);
v___x_3592_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3591_);
v___x_3593_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3586_, v___x_3592_, v_tail_3588_);
return v___x_3593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3594_){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3595_ = lean_array_get_size(v_xs_3594_);
v___x_3596_ = lean_unsigned_to_nat(0u);
v___x_3597_ = lean_nat_dec_eq(v___x_3595_, v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3598_ = lean_array_to_list(v_xs_3594_);
v___x_3599_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3600_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3598_, v___x_3599_);
v___x_3601_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3602_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v___x_3600_);
v___x_3604_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3601_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l_Std_Format_fill(v___x_3606_);
return v___x_3607_;
}
else
{
lean_object* v___x_3608_; 
lean_dec_ref(v_xs_3594_);
v___x_3608_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3608_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3609_, lean_object* v_x_3610_, lean_object* v_x_3611_){
_start:
{
if (lean_obj_tag(v_x_3611_) == 0)
{
lean_dec(v_x_3609_);
return v_x_3610_;
}
else
{
lean_object* v_head_3612_; lean_object* v_tail_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3623_; 
v_head_3612_ = lean_ctor_get(v_x_3611_, 0);
v_tail_3613_ = lean_ctor_get(v_x_3611_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_x_3611_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3615_ = v_x_3611_;
v_isShared_3616_ = v_isSharedCheck_3623_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_tail_3613_);
lean_inc(v_head_3612_);
lean_dec(v_x_3611_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3623_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
lean_inc(v_x_3609_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 5);
lean_ctor_set(v___x_3615_, 1, v_x_3609_);
lean_ctor_set(v___x_3615_, 0, v_x_3610_);
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_x_3610_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_x_3609_);
v___x_3618_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3612_);
v___x_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v_x_3610_ = v___x_3620_;
v_x_3611_ = v_tail_3613_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3624_, lean_object* v_x_3625_){
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
lean_dec_ref_known(v_x_3624_, 2);
v___x_3629_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3628_);
return v___x_3629_;
}
else
{
lean_object* v_head_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_inc(v_tail_3627_);
v_head_3630_ = lean_ctor_get(v_x_3624_, 0);
lean_inc(v_head_3630_);
lean_dec_ref_known(v_x_3624_, 2);
v___x_3631_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3630_);
v___x_3632_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3625_, v___x_3631_, v_tail_3627_);
return v___x_3632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3633_){
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
v___x_3639_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3637_, v___x_3638_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3648_, lean_object* v_x_3649_, lean_object* v_x_3650_){
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
v___x_3658_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3651_);
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
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3663_, lean_object* v_x_3664_){
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
lean_dec_ref_known(v_x_3663_, 2);
v___x_3668_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3667_);
return v___x_3668_;
}
else
{
lean_object* v_head_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_inc(v_tail_3666_);
v_head_3669_ = lean_ctor_get(v_x_3663_, 0);
lean_inc(v_head_3669_);
lean_dec_ref_known(v_x_3663_, 2);
v___x_3670_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3669_);
v___x_3671_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3664_, v___x_3670_, v_tail_3666_);
return v___x_3671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3672_){
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
v___x_3678_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3676_, v___x_3677_);
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
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_unsigned_to_nat(12u);
v___x_3701_ = lean_nat_to_int(v___x_3700_);
return v___x_3701_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = lean_unsigned_to_nat(9u);
v___x_3706_ = lean_nat_to_int(v___x_3705_);
return v___x_3706_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = lean_unsigned_to_nat(11u);
v___x_3711_ = lean_nat_to_int(v___x_3710_);
return v___x_3711_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3714_ = lean_string_length(v___x_3713_);
return v___x_3714_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3716_ = lean_nat_to_int(v___x_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3721_){
_start:
{
lean_object* v_numFixed_3722_; lean_object* v_perms_3723_; lean_object* v_revDeps_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v_numFixed_3722_ = lean_ctor_get(v_x_3721_, 0);
lean_inc(v_numFixed_3722_);
v_perms_3723_ = lean_ctor_get(v_x_3721_, 1);
lean_inc_ref(v_perms_3723_);
v_revDeps_3724_ = lean_ctor_get(v_x_3721_, 2);
lean_inc_ref(v_revDeps_3724_);
lean_dec_ref(v_x_3721_);
v___x_3725_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3726_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3727_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3728_ = l_Nat_reprFast(v_numFixed_3722_);
v___x_3729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3727_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = 0;
v___x_3732_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set_uint8(v___x_3732_, sizeof(void*)*1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3726_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_box(1);
v___x_3737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
lean_ctor_set(v___x_3740_, 1, v___x_3725_);
v___x_3741_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3742_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3723_);
v___x_3743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3741_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set_uint8(v___x_3744_, sizeof(void*)*1, v___x_3731_);
v___x_3745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3740_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v___x_3734_);
v___x_3747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set(v___x_3747_, 1, v___x_3736_);
v___x_3748_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3749_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
lean_ctor_set(v___x_3750_, 1, v___x_3725_);
v___x_3751_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3752_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3724_);
v___x_3753_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
lean_ctor_set_uint8(v___x_3754_, sizeof(void*)*1, v___x_3731_);
v___x_3755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3750_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3757_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
lean_ctor_set(v___x_3758_, 1, v___x_3755_);
v___x_3759_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3756_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set_uint8(v___x_3762_, sizeof(void*)*1, v___x_3731_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3763_, lean_object* v_prec_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3763_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3766_, lean_object* v_prec_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3766_, v_prec_3767_);
lean_dec(v_prec_3767_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___f_3777_; lean_object* v___x_5728__overap_3778_; lean_object* v___x_3779_; 
v___f_3777_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5728__overap_3778_ = lean_panic_fn_borrowed(v___f_3777_, v_msg_3771_);
lean_inc(v___y_3775_);
lean_inc_ref(v___y_3774_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
v___x_3779_ = lean_apply_5(v___x_5728__overap_3778_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, lean_box(0));
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___f_3793_; lean_object* v___x_5738__overap_3794_; lean_object* v___x_3795_; 
v___f_3793_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5738__overap_3794_ = lean_panic_fn_borrowed(v___f_3793_, v_msg_3787_);
lean_inc(v___y_3791_);
lean_inc_ref(v___y_3790_);
lean_inc(v___y_3789_);
lean_inc_ref(v___y_3788_);
v___x_3795_ = lean_apply_5(v___x_5738__overap_3794_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, lean_box(0));
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v___f_3809_; lean_object* v___x_5748__overap_3810_; lean_object* v___x_3811_; 
v___f_3809_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5748__overap_3810_ = lean_panic_fn_borrowed(v___f_3809_, v_msg_3803_);
lean_inc(v___y_3807_);
lean_inc_ref(v___y_3806_);
lean_inc(v___y_3805_);
lean_inc_ref(v___y_3804_);
v___x_3811_ = lean_apply_5(v___x_5748__overap_3810_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, lean_box(0));
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
return v_res_3818_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3822_ = lean_unsigned_to_nat(12u);
v___x_3823_ = lean_unsigned_to_nat(294u);
v___x_3824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3825_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3826_ = l_mkPanicMessageWithDecl(v___x_3825_, v___x_3824_, v___x_3823_, v___x_3822_, v___x_3821_);
return v___x_3826_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3829_ = lean_unsigned_to_nat(12u);
v___x_3830_ = lean_unsigned_to_nat(297u);
v___x_3831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3832_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3833_ = l_mkPanicMessageWithDecl(v___x_3832_, v___x_3831_, v___x_3830_, v___x_3829_, v___x_3828_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3834_, lean_object* v_as_3835_, size_t v_sz_3836_, size_t v_i_3837_, lean_object* v_b_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_a_3845_; uint8_t v___x_3849_; 
v___x_3849_ = lean_usize_dec_lt(v_i_3837_, v_sz_3836_);
if (v___x_3849_ == 0)
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3850_, 0, v_b_3838_);
return v___x_3850_;
}
else
{
lean_object* v_a_3851_; 
v_a_3851_ = lean_array_uget_borrowed(v_as_3835_, v_i_3837_);
if (lean_obj_tag(v_a_3851_) == 1)
{
lean_object* v_val_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_val_3852_ = lean_ctor_get(v_a_3851_, 0);
v___x_3853_ = lean_box(0);
v___x_3854_ = lean_unsigned_to_nat(0u);
v___x_3855_ = lean_array_get_borrowed(v___x_3853_, v_val_3852_, v___x_3854_);
if (lean_obj_tag(v___x_3855_) == 1)
{
lean_object* v_val_3856_; lean_object* v___x_3857_; 
v_val_3856_ = lean_ctor_get(v___x_3855_, 0);
v___x_3857_ = lean_array_get_borrowed(v___x_3853_, v___x_3834_, v_val_3856_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec_ref(v_b_3838_);
v___x_3858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3859_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3858_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3869_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3862_ = v___x_3859_;
v_isShared_3863_ = v_isSharedCheck_3869_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3869_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
if (lean_obj_tag(v_a_3860_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; 
v_a_3864_ = lean_ctor_get(v_a_3860_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v_a_3860_, 1);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 0, v_a_3864_);
v___x_3866_ = v___x_3862_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
else
{
lean_object* v_a_3868_; 
lean_del_object(v___x_3862_);
v_a_3868_ = lean_ctor_get(v_a_3860_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v_a_3860_, 1);
v_a_3845_ = v_a_3868_;
goto v___jp_3844_;
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
v_a_3870_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3859_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3859_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v___x_3878_; 
lean_inc_ref(v___x_3857_);
v___x_3878_ = lean_array_push(v_b_3838_, v___x_3857_);
v_a_3845_ = v___x_3878_;
goto v___jp_3844_;
}
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3880_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3879_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_dec_ref_known(v___x_3880_, 1);
v_a_3845_ = v_b_3838_;
goto v___jp_3844_;
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec_ref(v_b_3838_);
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3880_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3880_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_box(0);
v___x_3890_ = lean_array_push(v_b_3838_, v___x_3889_);
v_a_3845_ = v___x_3890_;
goto v___jp_3844_;
}
}
v___jp_3844_:
{
size_t v___x_3846_; size_t v___x_3847_; 
v___x_3846_ = ((size_t)1ULL);
v___x_3847_ = lean_usize_add(v_i_3837_, v___x_3846_);
v_i_3837_ = v___x_3847_;
v_b_3838_ = v_a_3845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3891_, lean_object* v_as_3892_, lean_object* v_sz_3893_, lean_object* v_i_3894_, lean_object* v_b_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
size_t v_sz_boxed_3901_; size_t v_i_boxed_3902_; lean_object* v_res_3903_; 
v_sz_boxed_3901_ = lean_unbox_usize(v_sz_3893_);
lean_dec(v_sz_3893_);
v_i_boxed_3902_ = lean_unbox_usize(v_i_3894_);
lean_dec(v_i_3894_);
v_res_3903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3891_, v_as_3892_, v_sz_boxed_3901_, v_i_boxed_3902_, v_b_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec_ref(v_as_3892_);
lean_dec_ref(v___x_3891_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3906_, lean_object* v___x_3907_, lean_object* v___x_3908_, lean_object* v_a_3909_, lean_object* v_b_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_nat_dec_lt(v_a_3909_, v_upperBound_3906_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; 
lean_dec(v_a_3909_);
v___x_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3917_, 0, v_b_3910_);
return v___x_3917_;
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; size_t v_sz_3920_; size_t v___x_3921_; lean_object* v___x_3922_; 
v___x_3918_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3919_ = lean_array_fget_borrowed(v___x_3907_, v_a_3909_);
v_sz_3920_ = lean_array_size(v___x_3919_);
v___x_3921_ = ((size_t)0ULL);
v___x_3922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3908_, v___x_3919_, v_sz_3920_, v___x_3921_, v___x_3918_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v___x_3922_, 1);
v___x_3924_ = lean_array_push(v_b_3910_, v_a_3923_);
v___x_3925_ = lean_unsigned_to_nat(1u);
v___x_3926_ = lean_nat_add(v_a_3909_, v___x_3925_);
lean_dec(v_a_3909_);
v_a_3909_ = v___x_3926_;
v_b_3910_ = v___x_3924_;
goto _start;
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec_ref(v_b_3910_);
lean_dec(v_a_3909_);
v_a_3928_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3922_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3922_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3936_, lean_object* v___x_3937_, lean_object* v___x_3938_, lean_object* v_a_3939_, lean_object* v_b_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3936_, v___x_3937_, v___x_3938_, v_a_3939_, v_b_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec_ref(v___x_3938_);
lean_dec_ref(v___x_3937_);
lean_dec(v_upperBound_3936_);
return v_res_3946_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3949_ = lean_unsigned_to_nat(8u);
v___x_3950_ = lean_unsigned_to_nat(281u);
v___x_3951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3952_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3953_ = l_mkPanicMessageWithDecl(v___x_3952_, v___x_3951_, v___x_3950_, v___x_3949_, v___x_3948_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3954_, lean_object* v_a_3955_, lean_object* v_b_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_a_3963_; uint8_t v___x_3967_; 
v___x_3967_ = lean_nat_dec_lt(v_a_3955_, v_upperBound_3954_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
lean_dec(v_a_3955_);
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v_b_3956_);
return v___x_3968_;
}
else
{
lean_object* v_snd_3969_; lean_object* v_snd_3970_; lean_object* v_snd_3971_; lean_object* v_fst_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4096_; 
v_snd_3969_ = lean_ctor_get(v_b_3956_, 1);
lean_inc(v_snd_3969_);
v_snd_3970_ = lean_ctor_get(v_snd_3969_, 1);
lean_inc(v_snd_3970_);
v_snd_3971_ = lean_ctor_get(v_snd_3970_, 1);
lean_inc(v_snd_3971_);
v_fst_3972_ = lean_ctor_get(v_b_3956_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_b_3956_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; 
v_unused_4097_ = lean_ctor_get(v_b_3956_, 1);
lean_dec(v_unused_4097_);
v___x_3974_ = v_b_3956_;
v_isShared_3975_ = v_isSharedCheck_4096_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_fst_3972_);
lean_dec(v_b_3956_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4096_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v_fst_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_4094_; 
v_fst_3976_ = lean_ctor_get(v_snd_3969_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_snd_3969_);
if (v_isSharedCheck_4094_ == 0)
{
lean_object* v_unused_4095_; 
v_unused_4095_ = lean_ctor_get(v_snd_3969_, 1);
lean_dec(v_unused_4095_);
v___x_3978_ = v_snd_3969_;
v_isShared_3979_ = v_isSharedCheck_4094_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_fst_3976_);
lean_dec(v_snd_3969_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_4094_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v_fst_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4092_; 
v_fst_3980_ = lean_ctor_get(v_snd_3970_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_snd_3970_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v_snd_3970_, 1);
lean_dec(v_unused_4093_);
v___x_3982_ = v_snd_3970_;
v_isShared_3983_ = v_isSharedCheck_4092_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_fst_3980_);
lean_dec(v_snd_3970_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4092_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v_array_3984_; lean_object* v_start_3985_; lean_object* v_stop_3986_; uint8_t v___x_3987_; 
v_array_3984_ = lean_ctor_get(v_snd_3971_, 0);
v_start_3985_ = lean_ctor_get(v_snd_3971_, 1);
v_stop_3986_ = lean_ctor_get(v_snd_3971_, 2);
v___x_3987_ = lean_nat_dec_lt(v_start_3985_, v_stop_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3989_; 
lean_dec(v_a_3955_);
if (v_isShared_3983_ == 0)
{
v___x_3989_ = v___x_3982_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_fst_3980_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_snd_3971_);
v___x_3989_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3991_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_3989_);
v___x_3991_ = v___x_3978_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_fst_3976_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3993_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_3991_);
v___x_3993_ = v___x_3974_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_fst_3972_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
}
}
}
else
{
lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4088_; 
lean_inc(v_stop_3986_);
lean_inc(v_start_3985_);
lean_inc_ref(v_array_3984_);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_snd_3971_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; lean_object* v_unused_4090_; lean_object* v_unused_4091_; 
v_unused_4089_ = lean_ctor_get(v_snd_3971_, 2);
lean_dec(v_unused_4089_);
v_unused_4090_ = lean_ctor_get(v_snd_3971_, 1);
lean_dec(v_unused_4090_);
v_unused_4091_ = lean_ctor_get(v_snd_3971_, 0);
lean_dec(v_unused_4091_);
v___x_3999_ = v_snd_3971_;
v_isShared_4000_ = v_isSharedCheck_4088_;
goto v_resetjp_3998_;
}
else
{
lean_dec(v_snd_3971_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4088_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v_array_4001_; lean_object* v_start_4002_; lean_object* v_stop_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4008_; 
v_array_4001_ = lean_ctor_get(v_fst_3980_, 0);
v_start_4002_ = lean_ctor_get(v_fst_3980_, 1);
v_stop_4003_ = lean_ctor_get(v_fst_3980_, 2);
v___x_4004_ = lean_array_fget(v_array_3984_, v_start_3985_);
v___x_4005_ = lean_unsigned_to_nat(1u);
v___x_4006_ = lean_nat_add(v_start_3985_, v___x_4005_);
lean_dec(v_start_3985_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 1, v___x_4006_);
v___x_4008_ = v___x_3999_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_array_3984_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4087_, 2, v_stop_3986_);
v___x_4008_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_nat_dec_lt(v_start_4002_, v_stop_4003_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4011_; 
lean_dec(v___x_4004_);
lean_dec(v_a_3955_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 1, v___x_4008_);
v___x_4011_ = v___x_3982_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_fst_3980_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v___x_4008_);
v___x_4011_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4013_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_4011_);
v___x_4013_ = v___x_3978_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_fst_3976_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4015_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_4013_);
v___x_4015_ = v___x_3974_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_fst_3972_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v___x_4013_);
v___x_4015_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
}
}
}
else
{
lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4083_; 
lean_inc(v_stop_4003_);
lean_inc(v_start_4002_);
lean_inc_ref(v_array_4001_);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_fst_3980_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; lean_object* v_unused_4085_; lean_object* v_unused_4086_; 
v_unused_4084_ = lean_ctor_get(v_fst_3980_, 2);
lean_dec(v_unused_4084_);
v_unused_4085_ = lean_ctor_get(v_fst_3980_, 1);
lean_dec(v_unused_4085_);
v_unused_4086_ = lean_ctor_get(v_fst_3980_, 0);
lean_dec(v_unused_4086_);
v___x_4021_ = v_fst_3980_;
v_isShared_4022_ = v_isSharedCheck_4083_;
goto v_resetjp_4020_;
}
else
{
lean_dec(v_fst_3980_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4083_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4023_; lean_object* v___x_4025_; 
v___x_4023_ = lean_nat_add(v_start_4002_, v___x_4005_);
lean_dec(v_start_4002_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 1, v___x_4023_);
v___x_4025_ = v___x_4021_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_array_4001_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4023_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_stop_4003_);
v___x_4025_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
if (lean_obj_tag(v___x_4004_) == 1)
{
lean_object* v_val_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4070_; 
v_val_4026_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4028_ = v___x_4004_;
v_isShared_4029_ = v_isSharedCheck_4070_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_val_4026_);
lean_dec(v___x_4004_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4070_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4035_; 
v___x_4030_ = lean_box(0);
v___x_4031_ = lean_unsigned_to_nat(0u);
v___x_4032_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4033_ = lean_array_get(v___x_4030_, v_val_4026_, v___x_4031_);
lean_dec(v_val_4026_);
lean_inc(v_a_3955_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v_a_3955_);
v___x_4035_ = v___x_4028_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_3955_);
v___x_4035_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
uint8_t v___x_4036_; 
v___x_4036_ = l_Option_instDecidableEq___redArg(v___x_4032_, v___x_4033_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
lean_dec_ref(v___x_4025_);
lean_dec_ref(v___x_4008_);
lean_del_object(v___x_3982_);
lean_del_object(v___x_3978_);
lean_dec(v_fst_3976_);
lean_del_object(v___x_3974_);
lean_dec(v_fst_3972_);
v___x_4037_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4038_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4037_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4048_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4041_ = v___x_4038_;
v_isShared_4042_ = v_isSharedCheck_4048_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4038_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4048_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
if (lean_obj_tag(v_a_4039_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; 
lean_dec(v_a_3955_);
v_a_4043_ = lean_ctor_get(v_a_4039_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v_a_4039_, 1);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v_a_4043_);
v___x_4045_ = v___x_4041_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4043_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
else
{
lean_object* v_a_4047_; 
lean_del_object(v___x_4041_);
v_a_4047_ = lean_ctor_get(v_a_4039_, 0);
lean_inc(v_a_4047_);
lean_dec_ref_known(v_a_4039_, 1);
v_a_3963_ = v_a_4047_;
goto v___jp_3962_;
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec(v_a_3955_);
v_a_4049_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4038_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4038_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
lean_inc(v_fst_3976_);
v___x_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4057_, 0, v_fst_3976_);
v___x_4058_ = lean_array_push(v_fst_3972_, v___x_4057_);
v___x_4059_ = lean_nat_add(v_fst_3976_, v___x_4005_);
lean_dec(v_fst_3976_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 1, v___x_4008_);
lean_ctor_set(v___x_3982_, 0, v___x_4025_);
v___x_4061_ = v___x_3982_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v___x_4008_);
v___x_4061_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4063_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_4061_);
lean_ctor_set(v___x_3978_, 0, v___x_4059_);
v___x_4063_ = v___x_3978_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4059_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4065_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_4063_);
lean_ctor_set(v___x_3974_, 0, v___x_4058_);
v___x_4065_ = v___x_3974_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
v_a_3963_ = v___x_4065_;
goto v___jp_3962_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
lean_dec(v___x_4004_);
v___x_4071_ = lean_box(0);
v___x_4072_ = lean_array_push(v_fst_3972_, v___x_4071_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 1, v___x_4008_);
lean_ctor_set(v___x_3982_, 0, v___x_4025_);
v___x_4074_ = v___x_3982_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4008_);
v___x_4074_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4076_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 1, v___x_4074_);
v___x_4076_ = v___x_3978_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_fst_3976_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v___x_4074_);
v___x_4076_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4078_; 
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 1, v___x_4076_);
lean_ctor_set(v___x_3974_, 0, v___x_4072_);
v___x_4078_ = v___x_3974_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4072_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
v_a_3963_ = v___x_4078_;
goto v___jp_3962_;
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
v___jp_3962_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = lean_unsigned_to_nat(1u);
v___x_3965_ = lean_nat_add(v_a_3955_, v___x_3964_);
lean_dec(v_a_3955_);
v_a_3955_ = v___x_3965_;
v_b_3956_ = v_a_3963_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4098_, lean_object* v_a_4099_, lean_object* v_b_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4098_, v_a_4099_, v_b_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v_upperBound_4098_);
return v_res_4106_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4108_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4109_ = lean_unsigned_to_nat(4u);
v___x_4110_ = lean_unsigned_to_nat(275u);
v___x_4111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4112_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4113_ = l_mkPanicMessageWithDecl(v___x_4112_, v___x_4111_, v___x_4110_, v___x_4109_, v___x_4108_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4114_, lean_object* v___x_4115_, lean_object* v___x_4116_, lean_object* v_xs_4117_, lean_object* v_x_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_graph_4124_; lean_object* v_revDeps_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4178_; 
v_graph_4124_ = lean_ctor_get(v_a_4114_, 0);
v_revDeps_4125_ = lean_ctor_get(v_a_4114_, 1);
v_isSharedCheck_4178_ = !lean_is_exclusive(v_a_4114_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4127_ = v_a_4114_;
v_isShared_4128_ = v_isSharedCheck_4178_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_revDeps_4125_);
lean_inc(v_graph_4124_);
lean_dec(v_a_4114_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4178_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v___x_4129_ = lean_array_get_borrowed(v___x_4115_, v_graph_4124_, v___x_4116_);
v___x_4130_ = lean_array_get_size(v_xs_4117_);
v___x_4131_ = lean_array_get_size(v___x_4129_);
v___x_4132_ = lean_nat_dec_eq(v___x_4130_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_del_object(v___x_4127_);
lean_dec_ref(v_revDeps_4125_);
lean_dec_ref(v_graph_4124_);
lean_dec_ref(v_xs_4117_);
lean_dec(v___x_4116_);
v___x_4133_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4134_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4133_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
return v___x_4134_;
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___x_4135_ = lean_mk_empty_array_with_capacity(v___x_4116_);
lean_inc_n(v___x_4116_, 2);
v___x_4136_ = l_Array_toSubarray___redArg(v_xs_4117_, v___x_4116_, v___x_4130_);
lean_inc(v___x_4129_);
v___x_4137_ = l_Array_toSubarray___redArg(v___x_4129_, v___x_4116_, v___x_4131_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 1, v___x_4137_);
lean_ctor_set(v___x_4127_, 0, v___x_4136_);
v___x_4139_ = v___x_4127_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4177_, 1, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_inc(v___x_4116_);
v___x_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4116_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4135_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4130_, v___x_4116_, v___x_4141_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v_snd_4144_; lean_object* v_fst_4145_; lean_object* v_fst_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v_snd_4144_ = lean_ctor_get(v_a_4143_, 1);
lean_inc(v_snd_4144_);
v_fst_4145_ = lean_ctor_get(v_a_4143_, 0);
lean_inc_n(v_fst_4145_, 2);
lean_dec(v_a_4143_);
v_fst_4146_ = lean_ctor_get(v_snd_4144_, 0);
lean_inc(v_fst_4146_);
lean_dec(v_snd_4144_);
v___x_4147_ = lean_unsigned_to_nat(1u);
v___x_4148_ = lean_array_get_size(v_graph_4124_);
v___x_4149_ = lean_mk_empty_array_with_capacity(v___x_4147_);
v___x_4150_ = lean_array_push(v___x_4149_, v_fst_4145_);
v___x_4151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4148_, v_graph_4124_, v_fst_4145_, v___x_4147_, v___x_4150_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v_fst_4145_);
lean_dec_ref(v_graph_4124_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4160_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4160_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4160_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4156_; lean_object* v___x_4158_; 
v___x_4156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4156_, 0, v_fst_4146_);
lean_ctor_set(v___x_4156_, 1, v_a_4152_);
lean_ctor_set(v___x_4156_, 2, v_revDeps_4125_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4156_);
v___x_4158_ = v___x_4154_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_dec(v_fst_4146_);
lean_dec_ref(v_revDeps_4125_);
v_a_4161_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4151_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4151_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec_ref(v_revDeps_4125_);
lean_dec_ref(v_graph_4124_);
v_a_4169_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4142_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4142_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4179_, lean_object* v___x_4180_, lean_object* v___x_4181_, lean_object* v_xs_4182_, lean_object* v_x_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4179_, v___x_4180_, v___x_4181_, v_xs_4182_, v_x_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec_ref(v_x_4183_);
lean_dec_ref(v___x_4180_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4196_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4197_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
lean_inc_ref(v_preDefs_4190_);
v___x_4198_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v_value_4202_; lean_object* v___f_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v___x_4200_ = lean_unsigned_to_nat(0u);
v___x_4201_ = lean_array_get(v___x_4196_, v_preDefs_4190_, v___x_4200_);
lean_dec_ref(v_preDefs_4190_);
v_value_4202_ = lean_ctor_get(v___x_4201_, 7);
lean_inc_ref(v_value_4202_);
lean_dec(v___x_4201_);
v___f_4203_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4203_, 0, v_a_4199_);
lean_closure_set(v___f_4203_, 1, v___x_4197_);
lean_closure_set(v___f_4203_, 2, v___x_4200_);
v___x_4204_ = 0;
v___x_4205_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4202_, v___f_4203_, v___x_4204_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
return v___x_4205_;
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v_preDefs_4190_);
v_a_4206_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4198_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4198_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4221_, lean_object* v___x_4222_, lean_object* v___x_4223_, lean_object* v_inst_4224_, lean_object* v_R_4225_, lean_object* v_a_4226_, lean_object* v_b_4227_, lean_object* v_c_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4221_, v___x_4222_, v___x_4223_, v_a_4226_, v_b_4227_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4235_, lean_object* v___x_4236_, lean_object* v___x_4237_, lean_object* v_inst_4238_, lean_object* v_R_4239_, lean_object* v_a_4240_, lean_object* v_b_4241_, lean_object* v_c_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4235_, v___x_4236_, v___x_4237_, v_inst_4238_, v_R_4239_, v_a_4240_, v_b_4241_, v_c_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec_ref(v___x_4237_);
lean_dec_ref(v___x_4236_);
lean_dec(v_upperBound_4235_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4249_, lean_object* v_inst_4250_, lean_object* v_R_4251_, lean_object* v_a_4252_, lean_object* v_b_4253_, lean_object* v_c_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4249_, v_a_4252_, v_b_4253_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4261_, lean_object* v_inst_4262_, lean_object* v_R_4263_, lean_object* v_a_4264_, lean_object* v_b_4265_, lean_object* v_c_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4261_, v_inst_4262_, v_R_4263_, v_a_4264_, v_b_4265_, v_c_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v_upperBound_4261_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4273_, size_t v_i_4274_, size_t v_stop_4275_, lean_object* v_b_4276_){
_start:
{
uint8_t v___x_4277_; 
v___x_4277_ = lean_usize_dec_eq(v_i_4274_, v_stop_4275_);
if (v___x_4277_ == 0)
{
size_t v___x_4278_; size_t v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = ((size_t)1ULL);
v___x_4279_ = lean_usize_sub(v_i_4274_, v___x_4278_);
v___x_4280_ = lean_array_uget_borrowed(v_as_4273_, v___x_4279_);
if (lean_obj_tag(v___x_4280_) == 0)
{
v_i_4274_ = v___x_4279_;
goto _start;
}
else
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4282_ = lean_unsigned_to_nat(1u);
v___x_4283_ = lean_nat_add(v_b_4276_, v___x_4282_);
lean_dec(v_b_4276_);
v_i_4274_ = v___x_4279_;
v_b_4276_ = v___x_4283_;
goto _start;
}
}
else
{
return v_b_4276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4285_, lean_object* v_i_4286_, lean_object* v_stop_4287_, lean_object* v_b_4288_){
_start:
{
size_t v_i_boxed_4289_; size_t v_stop_boxed_4290_; lean_object* v_res_4291_; 
v_i_boxed_4289_ = lean_unbox_usize(v_i_4286_);
lean_dec(v_i_4286_);
v_stop_boxed_4290_ = lean_unbox_usize(v_stop_4287_);
lean_dec(v_stop_4287_);
v_res_4291_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4285_, v_i_boxed_4289_, v_stop_boxed_4290_, v_b_4288_);
lean_dec_ref(v_as_4285_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4292_){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4293_ = lean_unsigned_to_nat(0u);
v___x_4294_ = lean_array_get_size(v_perm_4292_);
v___x_4295_ = lean_nat_dec_lt(v___x_4293_, v___x_4294_);
if (v___x_4295_ == 0)
{
return v___x_4293_;
}
else
{
size_t v___x_4296_; size_t v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = lean_usize_of_nat(v___x_4294_);
v___x_4297_ = ((size_t)0ULL);
v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4292_, v___x_4296_, v___x_4297_, v___x_4293_);
return v___x_4298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4299_);
lean_dec_ref(v_perm_4299_);
return v_res_4300_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4301_, lean_object* v_i_4302_){
_start:
{
lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4303_ = lean_array_get_size(v_perm_4301_);
v___x_4304_ = lean_nat_dec_lt(v_i_4302_, v___x_4303_);
if (v___x_4304_ == 0)
{
return v___x_4304_;
}
else
{
lean_object* v___x_4305_; 
v___x_4305_ = lean_array_fget_borrowed(v_perm_4301_, v_i_4302_);
if (lean_obj_tag(v___x_4305_) == 0)
{
uint8_t v___x_4306_; 
v___x_4306_ = 0;
return v___x_4306_;
}
else
{
return v___x_4304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4307_, lean_object* v_i_4308_){
_start:
{
uint8_t v_res_4309_; lean_object* v_r_4310_; 
v_res_4309_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4307_, v_i_4308_);
lean_dec(v_i_4308_);
lean_dec_ref(v_perm_4307_);
v_r_4310_ = lean_box(v_res_4309_);
return v_r_4310_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v___f_4317_; lean_object* v___x_757__overap_4318_; lean_object* v___x_4319_; 
v___f_4317_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_757__overap_4318_ = lean_panic_fn_borrowed(v___f_4317_, v_msg_4311_);
lean_inc(v___y_4315_);
lean_inc_ref(v___y_4314_);
lean_inc(v___y_4313_);
lean_inc_ref(v___y_4312_);
v___x_4319_ = lean_apply_5(v___x_757__overap_4318_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, lean_box(0));
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4327_, lean_object* v_msg_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4335_, lean_object* v_msg_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4335_, v_msg_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4343_, lean_object* v_maxFVars_x3f_4344_, lean_object* v_k_4345_, uint8_t v_cleanupAnnotations_4346_, uint8_t v_whnfType_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v___f_4353_; lean_object* v___x_4354_; 
v___f_4353_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4353_, 0, v_k_4345_);
v___x_4354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4343_, v_maxFVars_x3f_4344_, v___f_4353_, v_cleanupAnnotations_4346_, v_whnfType_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4354_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4354_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
v_a_4363_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4354_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4354_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4371_, lean_object* v_maxFVars_x3f_4372_, lean_object* v_k_4373_, lean_object* v_cleanupAnnotations_4374_, lean_object* v_whnfType_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4381_; uint8_t v_whnfType_boxed_4382_; lean_object* v_res_4383_; 
v_cleanupAnnotations_boxed_4381_ = lean_unbox(v_cleanupAnnotations_4374_);
v_whnfType_boxed_4382_ = lean_unbox(v_whnfType_4375_);
v_res_4383_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4371_, v_maxFVars_x3f_4372_, v_k_4373_, v_cleanupAnnotations_boxed_4381_, v_whnfType_boxed_4382_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4384_, lean_object* v_type_4385_, lean_object* v_maxFVars_x3f_4386_, lean_object* v_k_4387_, uint8_t v_cleanupAnnotations_4388_, uint8_t v_whnfType_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4385_, v_maxFVars_x3f_4386_, v_k_4387_, v_cleanupAnnotations_4388_, v_whnfType_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4396_, lean_object* v_type_4397_, lean_object* v_maxFVars_x3f_4398_, lean_object* v_k_4399_, lean_object* v_cleanupAnnotations_4400_, lean_object* v_whnfType_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4407_; uint8_t v_whnfType_boxed_4408_; lean_object* v_res_4409_; 
v_cleanupAnnotations_boxed_4407_ = lean_unbox(v_cleanupAnnotations_4400_);
v_whnfType_boxed_4408_ = lean_unbox(v_whnfType_4401_);
v_res_4409_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4396_, v_type_4397_, v_maxFVars_x3f_4398_, v_k_4399_, v_cleanupAnnotations_boxed_4407_, v_whnfType_boxed_4408_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
return v_res_4409_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4412_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4413_ = lean_unsigned_to_nat(6u);
v___x_4414_ = lean_unsigned_to_nat(329u);
v___x_4415_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4416_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4417_ = l_mkPanicMessageWithDecl(v___x_4416_, v___x_4415_, v___x_4414_, v___x_4413_, v___x_4412_);
return v___x_4417_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4421_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4422_ = lean_unsigned_to_nat(8u);
v___x_4423_ = lean_unsigned_to_nat(322u);
v___x_4424_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4425_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4426_ = l_mkPanicMessageWithDecl(v___x_4425_, v___x_4424_, v___x_4423_, v___x_4422_, v___x_4421_);
return v___x_4426_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4428_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4429_ = lean_unsigned_to_nat(8u);
v___x_4430_ = lean_unsigned_to_nat(325u);
v___x_4431_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4432_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4433_ = l_mkPanicMessageWithDecl(v___x_4432_, v___x_4431_, v___x_4430_, v___x_4429_, v___x_4428_);
return v___x_4433_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4435_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4436_ = lean_unsigned_to_nat(8u);
v___x_4437_ = lean_unsigned_to_nat(324u);
v___x_4438_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4439_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4440_ = l_mkPanicMessageWithDecl(v___x_4439_, v___x_4438_, v___x_4437_, v___x_4436_, v___x_4435_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4441_, lean_object* v___x_4442_, lean_object* v_xs_4443_, lean_object* v_val_4444_, lean_object* v_i_4445_, lean_object* v_perm_4446_, lean_object* v_k_4447_, lean_object* v_xs_x27_4448_, lean_object* v_type_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v___x_4455_; uint8_t v___x_4456_; 
v___x_4455_ = lean_array_get_size(v_xs_x27_4448_);
v___x_4456_ = lean_nat_dec_eq(v___x_4455_, v___x_4441_);
if (v___x_4456_ == 0)
{
lean_object* v___x_4457_; lean_object* v___x_4458_; 
lean_dec_ref(v_type_4449_);
lean_dec_ref(v_k_4447_);
lean_dec_ref(v_perm_4446_);
lean_dec_ref(v_xs_4443_);
v___x_4457_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4458_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4457_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
return v___x_4458_;
}
else
{
lean_object* v___x_4459_; lean_object* v_x_4460_; lean_object* v___x_4461_; 
v___x_4459_ = lean_unsigned_to_nat(0u);
v_x_4460_ = lean_array_get_borrowed(v___x_4442_, v_xs_x27_4448_, v___x_4459_);
lean_inc(v___y_4453_);
lean_inc_ref(v___y_4452_);
lean_inc(v___y_4451_);
lean_inc_ref(v___y_4450_);
lean_inc(v_x_4460_);
v___x_4461_ = lean_infer_type(v_x_4460_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_object* v_a_4462_; uint8_t v___x_4463_; 
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref_known(v___x_4461_, 1);
v___x_4463_ = l_Lean_Expr_hasLooseBVars(v_a_4462_);
lean_dec(v_a_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; uint8_t v___x_4465_; 
v___x_4464_ = lean_array_get_size(v_xs_4443_);
v___x_4465_ = lean_nat_dec_lt(v_val_4444_, v___x_4464_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4467_; 
lean_dec_ref(v_type_4449_);
lean_dec_ref(v_k_4447_);
lean_dec_ref(v_perm_4446_);
lean_dec_ref(v_xs_4443_);
v___x_4466_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4467_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4466_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
return v___x_4467_;
}
else
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4468_ = lean_nat_add(v_i_4445_, v___x_4441_);
lean_inc(v_x_4460_);
v___x_4469_ = lean_array_set(v_xs_4443_, v_val_4444_, v_x_4460_);
v___x_4470_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4446_, v_k_4447_, v___x_4468_, v_type_4449_, v___x_4469_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
return v___x_4470_;
}
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_dec_ref(v_type_4449_);
lean_dec_ref(v_k_4447_);
lean_dec_ref(v_perm_4446_);
lean_dec_ref(v_xs_4443_);
v___x_4471_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4472_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4471_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
return v___x_4472_;
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec_ref(v_type_4449_);
lean_dec_ref(v_k_4447_);
lean_dec_ref(v_perm_4446_);
lean_dec_ref(v_xs_4443_);
v_a_4473_ = lean_ctor_get(v___x_4461_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4461_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4461_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4461_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4481_, lean_object* v___x_4482_, lean_object* v_xs_4483_, lean_object* v_val_4484_, lean_object* v_i_4485_, lean_object* v_perm_4486_, lean_object* v_k_4487_, lean_object* v_xs_x27_4488_, lean_object* v_type_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v_res_4495_; 
v_res_4495_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4481_, v___x_4482_, v_xs_4483_, v_val_4484_, v_i_4485_, v_perm_4486_, v_k_4487_, v_xs_x27_4488_, v_type_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec_ref(v_xs_x27_4488_);
lean_dec(v_i_4485_);
lean_dec(v_val_4484_);
lean_dec_ref(v___x_4482_);
lean_dec(v___x_4481_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4496_, lean_object* v_k_4497_, lean_object* v_i_4498_, lean_object* v_type_4499_, lean_object* v_xs_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v___x_4506_; uint8_t v___x_4507_; 
v___x_4506_ = lean_array_get_size(v_perm_4496_);
v___x_4507_ = lean_nat_dec_lt(v_i_4498_, v___x_4506_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; 
lean_dec_ref(v_type_4499_);
lean_dec(v_i_4498_);
lean_dec_ref(v_perm_4496_);
lean_inc(v_a_4504_);
lean_inc_ref(v_a_4503_);
lean_inc(v_a_4502_);
lean_inc_ref(v_a_4501_);
v___x_4508_ = lean_apply_6(v_k_4497_, v_xs_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, lean_box(0));
return v___x_4508_;
}
else
{
lean_object* v___x_4509_; 
v___x_4509_ = lean_array_fget_borrowed(v_perm_4496_, v_i_4498_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v___x_4510_; 
lean_inc(v_a_4504_);
lean_inc_ref(v_a_4503_);
lean_inc(v_a_4502_);
lean_inc_ref(v_a_4501_);
v___x_4510_ = lean_whnf(v_type_4499_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; uint8_t v___x_4512_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref_known(v___x_4510_, 1);
v___x_4512_ = l_Lean_Expr_isForall(v_a_4511_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
lean_dec(v_a_4511_);
lean_dec_ref(v_xs_4500_);
lean_dec(v_i_4498_);
lean_dec_ref(v_k_4497_);
lean_dec_ref(v_perm_4496_);
v___x_4513_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4514_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4513_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
return v___x_4514_;
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4515_ = lean_unsigned_to_nat(1u);
v___x_4516_ = lean_nat_add(v_i_4498_, v___x_4515_);
lean_dec(v_i_4498_);
v___x_4517_ = l_Lean_Expr_bindingBody_x21(v_a_4511_);
lean_dec(v_a_4511_);
v_i_4498_ = v___x_4516_;
v_type_4499_ = v___x_4517_;
goto _start;
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec_ref(v_xs_4500_);
lean_dec(v_i_4498_);
lean_dec_ref(v_k_4497_);
lean_dec_ref(v_perm_4496_);
v_a_4519_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4510_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4510_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v_val_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___f_4530_; lean_object* v___x_4531_; uint8_t v___x_4532_; lean_object* v___x_4533_; 
v_val_4527_ = lean_ctor_get(v___x_4509_, 0);
lean_inc(v_val_4527_);
v___x_4528_ = l_Lean_instInhabitedExpr;
v___x_4529_ = lean_unsigned_to_nat(1u);
v___f_4530_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4530_, 0, v___x_4529_);
lean_closure_set(v___f_4530_, 1, v___x_4528_);
lean_closure_set(v___f_4530_, 2, v_xs_4500_);
lean_closure_set(v___f_4530_, 3, v_val_4527_);
lean_closure_set(v___f_4530_, 4, v_i_4498_);
lean_closure_set(v___f_4530_, 5, v_perm_4496_);
lean_closure_set(v___f_4530_, 6, v_k_4497_);
v___x_4531_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4532_ = 0;
v___x_4533_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4499_, v___x_4531_, v___f_4530_, v___x_4507_, v___x_4532_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
return v___x_4533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4534_, lean_object* v_k_4535_, lean_object* v_i_4536_, lean_object* v_type_4537_, lean_object* v_xs_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4534_, v_k_4535_, v_i_4536_, v_type_4537_, v_xs_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4545_, lean_object* v_perm_4546_, lean_object* v_k_4547_, lean_object* v_i_4548_, lean_object* v_type_4549_, lean_object* v_xs_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4546_, v_k_4547_, v_i_4548_, v_type_4549_, v_xs_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4557_, lean_object* v_perm_4558_, lean_object* v_k_4559_, lean_object* v_i_4560_, lean_object* v_type_4561_, lean_object* v_xs_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4557_, v_perm_4558_, v_k_4559_, v_i_4560_, v_type_4561_, v_xs_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
return v_res_4568_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = lean_unsigned_to_nat(0u);
v___x_4570_ = l_Lean_Level_ofNat(v___x_4569_);
return v___x_4570_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4571_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4572_ = l_Lean_mkSort(v___x_4571_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4573_, lean_object* v_type_4574_, lean_object* v_k_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4581_ = lean_unsigned_to_nat(0u);
v___x_4582_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4573_);
v___x_4583_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4584_ = lean_mk_array(v___x_4582_, v___x_4583_);
v___x_4585_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4573_, v_k_4575_, v___x_4581_, v_type_4574_, v___x_4584_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4586_, lean_object* v_type_4587_, lean_object* v_k_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4586_, v_type_4587_, v_k_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4595_, lean_object* v_perm_4596_, lean_object* v_type_4597_, lean_object* v_k_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4596_, v_type_4597_, v_k_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4605_, lean_object* v_perm_4606_, lean_object* v_type_4607_, lean_object* v_k_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_){
_start:
{
lean_object* v_res_4614_; 
v_res_4614_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4605_, v_perm_4606_, v_type_4607_, v_k_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4615_, lean_object* v_runInBase_4616_, lean_object* v_b_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = lean_apply_1(v_k_4615_, v_b_4617_);
lean_inc(v___y_4621_);
lean_inc_ref(v___y_4620_);
lean_inc(v___y_4619_);
lean_inc_ref(v___y_4618_);
v___x_4624_ = lean_apply_7(v_runInBase_4616_, lean_box(0), v___x_4623_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, lean_box(0));
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4625_, lean_object* v_runInBase_4626_, lean_object* v_b_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4625_, v_runInBase_4626_, v_b_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4634_, lean_object* v_perm_4635_, lean_object* v_type_4636_, lean_object* v_runInBase_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
lean_object* v___f_4643_; lean_object* v___x_4644_; 
v___f_4643_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4643_, 0, v_k_4634_);
lean_closure_set(v___f_4643_, 1, v_runInBase_4637_);
v___x_4644_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4635_, v_type_4636_, v___f_4643_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4645_, lean_object* v_perm_4646_, lean_object* v_type_4647_, lean_object* v_runInBase_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4645_, v_perm_4646_, v_type_4647_, v_runInBase_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4655_, lean_object* v_inst_4656_, lean_object* v_perm_4657_, lean_object* v_type_4658_, lean_object* v_k_4659_){
_start:
{
lean_object* v_toBind_4660_; lean_object* v_liftWith_4661_; lean_object* v_restoreM_4662_; lean_object* v___f_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; 
v_toBind_4660_ = lean_ctor_get(v_inst_4656_, 1);
lean_inc(v_toBind_4660_);
lean_dec_ref(v_inst_4656_);
v_liftWith_4661_ = lean_ctor_get(v_inst_4655_, 0);
lean_inc(v_liftWith_4661_);
v_restoreM_4662_ = lean_ctor_get(v_inst_4655_, 1);
lean_inc(v_restoreM_4662_);
lean_dec_ref(v_inst_4655_);
v___f_4663_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4663_, 0, v_k_4659_);
lean_closure_set(v___f_4663_, 1, v_perm_4657_);
lean_closure_set(v___f_4663_, 2, v_type_4658_);
v___x_4664_ = lean_apply_2(v_liftWith_4661_, lean_box(0), v___f_4663_);
v___x_4665_ = lean_apply_1(v_restoreM_4662_, lean_box(0));
v___x_4666_ = lean_apply_4(v_toBind_4660_, lean_box(0), lean_box(0), v___x_4664_, v___x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4667_, lean_object* v_00_u03b1_4668_, lean_object* v_inst_4669_, lean_object* v_inst_4670_, lean_object* v_perm_4671_, lean_object* v_type_4672_, lean_object* v_k_4673_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4669_, v_inst_4670_, v_perm_4671_, v_type_4672_, v_k_4673_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v___f_4681_; lean_object* v___x_512__overap_4682_; lean_object* v___x_4683_; 
v___f_4681_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_512__overap_4682_ = lean_panic_fn_borrowed(v___f_4681_, v_msg_4675_);
lean_inc(v___y_4679_);
lean_inc_ref(v___y_4678_);
lean_inc(v___y_4677_);
lean_inc_ref(v___y_4676_);
v___x_4683_ = lean_apply_5(v___x_512__overap_4682_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, lean_box(0));
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
return v_res_4690_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4693_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4694_ = lean_unsigned_to_nat(10u);
v___x_4695_ = lean_unsigned_to_nat(353u);
v___x_4696_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4697_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4698_ = l_mkPanicMessageWithDecl(v___x_4697_, v___x_4696_, v___x_4695_, v___x_4694_, v___x_4693_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4699_, lean_object* v_xs_4700_, lean_object* v_tail_4701_, lean_object* v_ys_4702_, lean_object* v_type_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4699_, v_xs_4700_, v_tail_4701_, v_ys_4702_, v_type_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec_ref(v_ys_4702_);
lean_dec(v___x_4699_);
return v_res_4709_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4710_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4711_ = lean_unsigned_to_nat(8u);
v___x_4712_ = lean_unsigned_to_nat(349u);
v___x_4713_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4715_ = l_mkPanicMessageWithDecl(v___x_4714_, v___x_4713_, v___x_4712_, v___x_4711_, v___x_4710_);
return v___x_4715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4716_, lean_object* v_x_4717_, lean_object* v_x_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
if (lean_obj_tag(v_x_4717_) == 0)
{
lean_object* v___x_4724_; 
lean_dec_ref(v_xs_4716_);
v___x_4724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4724_, 0, v_x_4718_);
return v___x_4724_;
}
else
{
lean_object* v_head_4725_; 
v_head_4725_ = lean_ctor_get(v_x_4717_, 0);
if (lean_obj_tag(v_head_4725_) == 0)
{
lean_object* v_tail_4726_; lean_object* v___x_4727_; lean_object* v___f_4728_; lean_object* v___x_4729_; uint8_t v___x_4730_; lean_object* v___x_4731_; 
v_tail_4726_ = lean_ctor_get(v_x_4717_, 1);
lean_inc(v_tail_4726_);
lean_dec_ref_known(v_x_4717_, 2);
v___x_4727_ = lean_unsigned_to_nat(1u);
v___f_4728_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4728_, 0, v___x_4727_);
lean_closure_set(v___f_4728_, 1, v_xs_4716_);
lean_closure_set(v___f_4728_, 2, v_tail_4726_);
v___x_4729_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4730_ = 0;
v___x_4731_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4718_, v___x_4729_, v___f_4728_, v___x_4730_, v___x_4730_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
return v___x_4731_;
}
else
{
lean_object* v_tail_4732_; lean_object* v_val_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
lean_inc_ref(v_head_4725_);
v_tail_4732_ = lean_ctor_get(v_x_4717_, 1);
lean_inc(v_tail_4732_);
lean_dec_ref_known(v_x_4717_, 2);
v_val_4733_ = lean_ctor_get(v_head_4725_, 0);
lean_inc(v_val_4733_);
lean_dec_ref_known(v_head_4725_, 1);
v___x_4734_ = lean_array_get_size(v_xs_4716_);
v___x_4735_ = lean_nat_dec_lt(v_val_4733_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
lean_dec(v_val_4733_);
lean_dec(v_tail_4732_);
lean_dec_ref(v_x_4718_);
lean_dec_ref(v_xs_4716_);
v___x_4736_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4737_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4736_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
return v___x_4737_;
}
else
{
lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4738_ = l_Lean_instInhabitedExpr;
v___x_4739_ = lean_array_get_borrowed(v___x_4738_, v_xs_4716_, v_val_4733_);
lean_dec(v_val_4733_);
v___x_4740_ = lean_unsigned_to_nat(1u);
v___x_4741_ = lean_mk_empty_array_with_capacity(v___x_4740_);
lean_inc(v___x_4739_);
v___x_4742_ = lean_array_push(v___x_4741_, v___x_4739_);
v___x_4743_ = l_Lean_Meta_instantiateForall(v_x_4718_, v___x_4742_, v_a_4719_, v_a_4720_, v_a_4721_, v_a_4722_);
lean_dec_ref(v___x_4742_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
lean_inc(v_a_4744_);
lean_dec_ref_known(v___x_4743_, 1);
v_x_4717_ = v_tail_4732_;
v_x_4718_ = v_a_4744_;
goto _start;
}
else
{
lean_dec(v_tail_4732_);
lean_dec_ref(v_xs_4716_);
return v___x_4743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4746_, lean_object* v_xs_4747_, lean_object* v_tail_4748_, lean_object* v_ys_4749_, lean_object* v_type_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
lean_object* v___x_4756_; uint8_t v___x_4757_; 
v___x_4756_ = lean_array_get_size(v_ys_4749_);
v___x_4757_ = lean_nat_dec_eq(v___x_4756_, v___x_4746_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec_ref(v_type_4750_);
lean_dec(v_tail_4748_);
lean_dec_ref(v_xs_4747_);
v___x_4758_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4759_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4758_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
return v___x_4759_;
}
else
{
lean_object* v___x_4760_; 
v___x_4760_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4747_, v_tail_4748_, v_type_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; uint8_t v___x_4762_; uint8_t v___x_4763_; lean_object* v___x_4764_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v___x_4762_ = 0;
v___x_4763_ = 1;
v___x_4764_ = l_Lean_Meta_mkForallFVars(v_ys_4749_, v_a_4761_, v___x_4762_, v___x_4757_, v___x_4757_, v___x_4763_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
return v___x_4764_;
}
else
{
return v___x_4760_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4765_, lean_object* v_x_4766_, lean_object* v_x_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4765_, v_x_4766_, v_x_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
return v_res_4773_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4776_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4777_ = lean_unsigned_to_nat(2u);
v___x_4778_ = lean_unsigned_to_nat(343u);
v___x_4779_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4780_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4781_ = l_mkPanicMessageWithDecl(v___x_4780_, v___x_4779_, v___x_4778_, v___x_4777_, v___x_4776_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4782_, lean_object* v_type_u2080_4783_, lean_object* v_xs_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; uint8_t v___x_4792_; 
v___x_4790_ = lean_array_get_size(v_xs_4784_);
v___x_4791_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4782_);
v___x_4792_ = lean_nat_dec_eq(v___x_4790_, v___x_4791_);
lean_dec(v___x_4791_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_dec_ref(v_xs_4784_);
lean_dec_ref(v_type_u2080_4783_);
lean_dec_ref(v_perm_4782_);
v___x_4793_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4794_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4793_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_);
return v___x_4794_;
}
else
{
lean_object* v_mask_4795_; lean_object* v___x_4796_; 
v_mask_4795_ = lean_array_to_list(v_perm_4782_);
v___x_4796_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4784_, v_mask_4795_, v_type_u2080_4783_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_);
return v___x_4796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4797_, lean_object* v_type_u2080_4798_, lean_object* v_xs_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4797_, v_type_u2080_4798_, v_xs_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_);
lean_dec(v_a_4803_);
lean_dec_ref(v_a_4802_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
return v_res_4805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4806_, lean_object* v_maxFVars_4807_, lean_object* v_k_4808_, uint8_t v_cleanupAnnotations_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v___f_4815_; uint8_t v___x_4816_; uint8_t v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___f_4815_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4815_, 0, v_k_4808_);
v___x_4816_ = 1;
v___x_4817_ = 0;
v___x_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4818_, 0, v_maxFVars_4807_);
v___x_4819_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4806_, v___x_4816_, v___x_4817_, v___x_4816_, v___x_4817_, v___x_4818_, v___f_4815_, v_cleanupAnnotations_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
lean_dec_ref_known(v___x_4818_, 1);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
v_a_4820_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4822_ = v___x_4819_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4819_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
v_a_4828_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4819_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4819_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4836_, lean_object* v_maxFVars_4837_, lean_object* v_k_4838_, lean_object* v_cleanupAnnotations_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4845_; lean_object* v_res_4846_; 
v_cleanupAnnotations_boxed_4845_ = lean_unbox(v_cleanupAnnotations_4839_);
v_res_4846_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4836_, v_maxFVars_4837_, v_k_4838_, v_cleanupAnnotations_boxed_4845_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4847_, lean_object* v_e_4848_, lean_object* v_maxFVars_4849_, lean_object* v_k_4850_, uint8_t v_cleanupAnnotations_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4848_, v_maxFVars_4849_, v_k_4850_, v_cleanupAnnotations_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4858_, lean_object* v_e_4859_, lean_object* v_maxFVars_4860_, lean_object* v_k_4861_, lean_object* v_cleanupAnnotations_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4868_; lean_object* v_res_4869_; 
v_cleanupAnnotations_boxed_4868_ = lean_unbox(v_cleanupAnnotations_4862_);
v_res_4869_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4858_, v_e_4859_, v_maxFVars_4860_, v_k_4861_, v_cleanupAnnotations_boxed_4868_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_);
lean_dec(v___y_4866_);
lean_dec_ref(v___y_4865_);
lean_dec(v___y_4864_);
lean_dec_ref(v___y_4863_);
return v_res_4869_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4870_){
_start:
{
if (lean_obj_tag(v_x_4870_) == 0)
{
uint8_t v___x_4871_; 
v___x_4871_ = 1;
return v___x_4871_;
}
else
{
lean_object* v_head_4872_; 
v_head_4872_ = lean_ctor_get(v_x_4870_, 0);
if (lean_obj_tag(v_head_4872_) == 0)
{
lean_object* v_tail_4873_; 
v_tail_4873_ = lean_ctor_get(v_x_4870_, 1);
v_x_4870_ = v_tail_4873_;
goto _start;
}
else
{
uint8_t v___x_4875_; 
v___x_4875_ = 0;
return v___x_4875_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4876_){
_start:
{
uint8_t v_res_4877_; lean_object* v_r_4878_; 
v_res_4877_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4876_);
lean_dec(v_x_4876_);
v_r_4878_ = lean_box(v_res_4877_);
return v_r_4878_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4881_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4882_ = lean_unsigned_to_nat(12u);
v___x_4883_ = lean_unsigned_to_nat(376u);
v___x_4884_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4885_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4886_ = l_mkPanicMessageWithDecl(v___x_4885_, v___x_4884_, v___x_4883_, v___x_4882_, v___x_4881_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4887_, lean_object* v_xs_4888_, lean_object* v_tail_4889_, lean_object* v___x_4890_, lean_object* v___x_4891_, lean_object* v_ys_4892_, lean_object* v_value_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
uint8_t v___x_1127__boxed_4899_; uint8_t v___x_1128__boxed_4900_; lean_object* v_res_4901_; 
v___x_1127__boxed_4899_ = lean_unbox(v___x_4890_);
v___x_1128__boxed_4900_ = lean_unbox(v___x_4891_);
v_res_4901_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4887_, v_xs_4888_, v_tail_4889_, v___x_1127__boxed_4899_, v___x_1128__boxed_4900_, v_ys_4892_, v_value_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec_ref(v_ys_4892_);
lean_dec(v___x_4887_);
return v_res_4901_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; 
v___x_4902_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4903_ = lean_unsigned_to_nat(8u);
v___x_4904_ = lean_unsigned_to_nat(368u);
v___x_4905_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4906_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4907_ = l_mkPanicMessageWithDecl(v___x_4906_, v___x_4905_, v___x_4904_, v___x_4903_, v___x_4902_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4908_, lean_object* v_x_4909_, lean_object* v_x_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
if (lean_obj_tag(v_x_4909_) == 0)
{
lean_object* v___x_4916_; 
lean_dec_ref(v_xs_4908_);
v___x_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4916_, 0, v_x_4910_);
return v___x_4916_;
}
else
{
lean_object* v_head_4917_; 
v_head_4917_ = lean_ctor_get(v_x_4909_, 0);
if (lean_obj_tag(v_head_4917_) == 0)
{
lean_object* v_tail_4918_; uint8_t v___x_4919_; 
v_tail_4918_ = lean_ctor_get(v_x_4909_, 1);
lean_inc(v_tail_4918_);
lean_dec_ref_known(v_x_4909_, 2);
v___x_4919_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4918_);
if (v___x_4919_ == 0)
{
uint8_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___f_4924_; lean_object* v___x_4925_; 
v___x_4920_ = 1;
v___x_4921_ = lean_unsigned_to_nat(1u);
v___x_4922_ = lean_box(v___x_4919_);
v___x_4923_ = lean_box(v___x_4920_);
v___f_4924_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4924_, 0, v___x_4921_);
lean_closure_set(v___f_4924_, 1, v_xs_4908_);
lean_closure_set(v___f_4924_, 2, v_tail_4918_);
lean_closure_set(v___f_4924_, 3, v___x_4922_);
lean_closure_set(v___f_4924_, 4, v___x_4923_);
v___x_4925_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4910_, v___x_4921_, v___f_4924_, v___x_4919_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
return v___x_4925_;
}
else
{
lean_object* v___x_4926_; 
lean_dec(v_tail_4918_);
lean_dec_ref(v_xs_4908_);
v___x_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4926_, 0, v_x_4910_);
return v___x_4926_;
}
}
else
{
lean_object* v_tail_4927_; lean_object* v_val_4928_; lean_object* v___x_4929_; uint8_t v___x_4930_; 
lean_inc_ref(v_head_4917_);
v_tail_4927_ = lean_ctor_get(v_x_4909_, 1);
lean_inc(v_tail_4927_);
lean_dec_ref_known(v_x_4909_, 2);
v_val_4928_ = lean_ctor_get(v_head_4917_, 0);
lean_inc(v_val_4928_);
lean_dec_ref_known(v_head_4917_, 1);
v___x_4929_ = lean_array_get_size(v_xs_4908_);
v___x_4930_ = lean_nat_dec_lt(v_val_4928_, v___x_4929_);
if (v___x_4930_ == 0)
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
lean_dec(v_val_4928_);
lean_dec(v_tail_4927_);
lean_dec_ref(v_x_4910_);
lean_dec_ref(v_xs_4908_);
v___x_4931_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4932_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4931_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
return v___x_4932_;
}
else
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4933_ = l_Lean_instInhabitedExpr;
v___x_4934_ = lean_array_get_borrowed(v___x_4933_, v_xs_4908_, v_val_4928_);
lean_dec(v_val_4928_);
v___x_4935_ = lean_unsigned_to_nat(1u);
v___x_4936_ = lean_mk_empty_array_with_capacity(v___x_4935_);
lean_inc(v___x_4934_);
v___x_4937_ = lean_array_push(v___x_4936_, v___x_4934_);
v___x_4938_ = l_Lean_Meta_instantiateLambda(v_x_4910_, v___x_4937_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_);
lean_dec_ref(v___x_4937_);
if (lean_obj_tag(v___x_4938_) == 0)
{
lean_object* v_a_4939_; 
v_a_4939_ = lean_ctor_get(v___x_4938_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___x_4938_, 1);
v_x_4909_ = v_tail_4927_;
v_x_4910_ = v_a_4939_;
goto _start;
}
else
{
lean_dec(v_tail_4927_);
lean_dec_ref(v_xs_4908_);
return v___x_4938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4941_, lean_object* v_xs_4942_, lean_object* v_tail_4943_, uint8_t v___x_4944_, uint8_t v___x_4945_, lean_object* v_ys_4946_, lean_object* v_value_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
lean_object* v___x_4953_; uint8_t v___x_4954_; 
v___x_4953_ = lean_array_get_size(v_ys_4946_);
v___x_4954_ = lean_nat_dec_eq(v___x_4953_, v___x_4941_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_dec_ref(v_value_4947_);
lean_dec(v_tail_4943_);
lean_dec_ref(v_xs_4942_);
v___x_4955_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4956_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4955_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
return v___x_4956_;
}
else
{
lean_object* v___x_4957_; 
v___x_4957_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4942_, v_tail_4943_, v_value_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; uint8_t v___x_4959_; lean_object* v___x_4960_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref_known(v___x_4957_, 1);
v___x_4959_ = 1;
v___x_4960_ = l_Lean_Meta_mkLambdaFVars(v_ys_4946_, v_a_4958_, v___x_4944_, v___x_4945_, v___x_4944_, v___x_4945_, v___x_4959_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
return v___x_4960_;
}
else
{
return v___x_4957_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4961_, lean_object* v_x_4962_, lean_object* v_x_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4961_, v_x_4962_, v_x_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
lean_dec(v_a_4967_);
lean_dec_ref(v_a_4966_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
return v_res_4969_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4971_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4972_ = lean_unsigned_to_nat(2u);
v___x_4973_ = lean_unsigned_to_nat(362u);
v___x_4974_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_4975_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4976_ = l_mkPanicMessageWithDecl(v___x_4975_, v___x_4974_, v___x_4973_, v___x_4972_, v___x_4971_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_4977_, lean_object* v_value_u2080_4978_, lean_object* v_xs_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; uint8_t v___x_4987_; 
v___x_4985_ = lean_array_get_size(v_xs_4979_);
v___x_4986_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4977_);
v___x_4987_ = lean_nat_dec_eq(v___x_4985_, v___x_4986_);
lean_dec(v___x_4986_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
lean_dec_ref(v_xs_4979_);
lean_dec_ref(v_value_u2080_4978_);
lean_dec_ref(v_perm_4977_);
v___x_4988_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_4989_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4988_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_4989_;
}
else
{
lean_object* v_mask_4990_; lean_object* v___x_4991_; 
v_mask_4990_ = lean_array_to_list(v_perm_4977_);
v___x_4991_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4979_, v_mask_4990_, v_value_u2080_4978_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_);
return v___x_4991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_4992_, lean_object* v_value_u2080_4993_, lean_object* v_xs_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_4992_, v_value_u2080_4993_, v_xs_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
lean_dec(v_a_4996_);
lean_dec_ref(v_a_4995_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5008_){
_start:
{
lean_object* v___f_5009_; lean_object* v___f_5010_; lean_object* v___f_5011_; lean_object* v___f_5012_; lean_object* v___f_5013_; lean_object* v___f_5014_; lean_object* v___f_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___f_5009_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5010_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5011_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5012_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5013_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5014_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5015_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5016_, 0, v___f_5009_);
lean_ctor_set(v___x_5016_, 1, v___f_5010_);
v___x_5017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
lean_ctor_set(v___x_5017_, 1, v___f_5011_);
lean_ctor_set(v___x_5017_, 2, v___f_5012_);
lean_ctor_set(v___x_5017_, 3, v___f_5013_);
lean_ctor_set(v___x_5017_, 4, v___f_5014_);
v___x_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5017_);
lean_ctor_set(v___x_5018_, 1, v___f_5015_);
v___x_5019_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5020_ = l_instInhabitedOfMonad___redArg(v___x_5018_, v___x_5019_);
v___x_5021_ = lean_panic_fn_borrowed(v___x_5020_, v_msg_5008_);
lean_dec(v___x_5020_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5022_, lean_object* v_msg_5023_){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5023_);
return v___x_5024_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5027_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5028_ = lean_unsigned_to_nat(8u);
v___x_5029_ = lean_unsigned_to_nat(394u);
v___x_5030_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5031_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5032_ = l_mkPanicMessageWithDecl(v___x_5031_, v___x_5030_, v___x_5029_, v___x_5028_, v___x_5027_);
return v___x_5032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5033_, lean_object* v_x_5034_){
_start:
{
if (lean_obj_tag(v_x_5033_) == 0)
{
return v_x_5034_;
}
else
{
lean_object* v_head_5035_; lean_object* v_fst_5036_; 
v_head_5035_ = lean_ctor_get(v_x_5033_, 0);
v_fst_5036_ = lean_ctor_get(v_head_5035_, 0);
if (lean_obj_tag(v_fst_5036_) == 0)
{
lean_object* v_tail_5037_; 
v_tail_5037_ = lean_ctor_get(v_x_5033_, 1);
lean_inc(v_tail_5037_);
lean_dec_ref_known(v_x_5033_, 2);
v_x_5033_ = v_tail_5037_;
goto _start;
}
else
{
lean_object* v_tail_5039_; lean_object* v_snd_5040_; lean_object* v_val_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; 
lean_inc_ref(v_fst_5036_);
lean_inc(v_head_5035_);
v_tail_5039_ = lean_ctor_get(v_x_5033_, 1);
lean_inc(v_tail_5039_);
lean_dec_ref_known(v_x_5033_, 2);
v_snd_5040_ = lean_ctor_get(v_head_5035_, 1);
lean_inc(v_snd_5040_);
lean_dec(v_head_5035_);
v_val_5041_ = lean_ctor_get(v_fst_5036_, 0);
lean_inc(v_val_5041_);
lean_dec_ref_known(v_fst_5036_, 1);
v___x_5042_ = lean_array_get_size(v_x_5034_);
v___x_5043_ = lean_nat_dec_lt(v_val_5041_, v___x_5042_);
if (v___x_5043_ == 0)
{
lean_object* v___x_5044_; lean_object* v___x_5045_; 
lean_dec(v_val_5041_);
lean_dec(v_snd_5040_);
lean_dec(v_tail_5039_);
lean_dec_ref(v_x_5034_);
v___x_5044_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5045_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5044_);
return v___x_5045_;
}
else
{
lean_object* v___x_5046_; 
v___x_5046_ = lean_array_set(v_x_5034_, v_val_5041_, v_snd_5040_);
lean_dec(v_val_5041_);
v_x_5033_ = v_tail_5039_;
v_x_5034_ = v___x_5046_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5048_, lean_object* v_x_5049_, lean_object* v_x_5050_){
_start:
{
lean_object* v___x_5051_; 
v___x_5051_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5049_, v_x_5050_);
return v___x_5051_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5054_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5055_ = lean_unsigned_to_nat(2u);
v___x_5056_ = lean_unsigned_to_nat(384u);
v___x_5057_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5058_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5059_ = l_mkPanicMessageWithDecl(v___x_5058_, v___x_5057_, v___x_5056_, v___x_5055_, v___x_5054_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5062_, lean_object* v_xs_5063_){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; uint8_t v___x_5066_; 
v___x_5064_ = lean_array_get_size(v_xs_5063_);
v___x_5065_ = lean_array_get_size(v_perm_5062_);
v___x_5066_ = lean_nat_dec_eq(v___x_5064_, v___x_5065_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5068_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5067_);
return v___x_5068_;
}
else
{
lean_object* v___x_5069_; uint8_t v___x_5070_; 
v___x_5069_ = lean_unsigned_to_nat(0u);
v___x_5070_ = lean_nat_dec_eq(v___x_5064_, v___x_5069_);
if (v___x_5070_ == 0)
{
lean_object* v_dummy_5071_; lean_object* v___x_5072_; lean_object* v_ys_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
v_dummy_5071_ = lean_array_fget_borrowed(v_xs_5063_, v___x_5069_);
v___x_5072_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5062_);
lean_inc(v_dummy_5071_);
v_ys_5073_ = lean_mk_array(v___x_5072_, v_dummy_5071_);
v___x_5074_ = l_Array_zip___redArg(v_perm_5062_, v_xs_5063_);
v___x_5075_ = lean_array_to_list(v___x_5074_);
v___x_5076_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5075_, v_ys_5073_);
return v___x_5076_;
}
else
{
lean_object* v___x_5077_; 
v___x_5077_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5078_, lean_object* v_xs_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5078_, v_xs_5079_);
lean_dec_ref(v_xs_5079_);
lean_dec_ref(v_perm_5078_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5081_, lean_object* v_perm_5082_, lean_object* v_xs_5083_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5082_, v_xs_5083_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5085_, lean_object* v_perm_5086_, lean_object* v_xs_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5085_, v_perm_5086_, v_xs_5087_);
lean_dec_ref(v_xs_5087_);
lean_dec_ref(v_perm_5086_);
return v_res_5088_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5089_, lean_object* v_upperBound_5090_, lean_object* v_perm_5091_, lean_object* v_a_5092_, lean_object* v_b_5093_){
_start:
{
lean_object* v_a_5095_; uint8_t v___x_5102_; 
v___x_5102_ = lean_nat_dec_lt(v_a_5092_, v_upperBound_5090_);
if (v___x_5102_ == 0)
{
lean_dec(v_a_5092_);
return v_b_5093_;
}
else
{
lean_object* v___x_5103_; uint8_t v___x_5104_; 
v___x_5103_ = lean_array_get_size(v_perm_5091_);
v___x_5104_ = lean_nat_dec_lt(v_a_5092_, v___x_5103_);
if (v___x_5104_ == 0)
{
goto v___jp_5099_;
}
else
{
lean_object* v___x_5105_; 
v___x_5105_ = lean_array_fget_borrowed(v_perm_5091_, v_a_5092_);
if (lean_obj_tag(v___x_5105_) == 0)
{
goto v___jp_5099_;
}
else
{
v_a_5095_ = v_b_5093_;
goto v___jp_5094_;
}
}
}
v___jp_5094_:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5096_ = lean_unsigned_to_nat(1u);
v___x_5097_ = lean_nat_add(v_a_5092_, v___x_5096_);
lean_dec(v_a_5092_);
v_a_5092_ = v___x_5097_;
v_b_5093_ = v_a_5095_;
goto _start;
}
v___jp_5099_:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; 
v___x_5100_ = lean_array_fget_borrowed(v_xs_5089_, v_a_5092_);
lean_inc(v___x_5100_);
v___x_5101_ = lean_array_push(v_b_5093_, v___x_5100_);
v_a_5095_ = v___x_5101_;
goto v___jp_5094_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5106_, lean_object* v_upperBound_5107_, lean_object* v_perm_5108_, lean_object* v_a_5109_, lean_object* v_b_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5106_, v_upperBound_5107_, v_perm_5108_, v_a_5109_, v_b_5110_);
lean_dec_ref(v_perm_5108_);
lean_dec(v_upperBound_5107_);
lean_dec_ref(v_xs_5106_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5112_, lean_object* v_xs_5113_){
_start:
{
lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v_ys_5116_; lean_object* v___x_5117_; 
v___x_5114_ = lean_array_get_size(v_xs_5113_);
v___x_5115_ = lean_unsigned_to_nat(0u);
v_ys_5116_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5117_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5113_, v___x_5114_, v_perm_5112_, v___x_5115_, v_ys_5116_);
return v___x_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5118_, lean_object* v_xs_5119_){
_start:
{
lean_object* v_res_5120_; 
v_res_5120_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5118_, v_xs_5119_);
lean_dec_ref(v_xs_5119_);
lean_dec_ref(v_perm_5118_);
return v_res_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5121_, lean_object* v_perm_5122_, lean_object* v_xs_5123_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5122_, v_xs_5123_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5125_, lean_object* v_perm_5126_, lean_object* v_xs_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5125_, v_perm_5126_, v_xs_5127_);
lean_dec_ref(v_xs_5127_);
lean_dec_ref(v_perm_5126_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5129_, lean_object* v_xs_5130_, lean_object* v_upperBound_5131_, lean_object* v_perm_5132_, lean_object* v_inst_5133_, lean_object* v_R_5134_, lean_object* v_a_5135_, lean_object* v_b_5136_, lean_object* v_c_5137_){
_start:
{
lean_object* v___x_5138_; 
v___x_5138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5130_, v_upperBound_5131_, v_perm_5132_, v_a_5135_, v_b_5136_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5139_, lean_object* v_xs_5140_, lean_object* v_upperBound_5141_, lean_object* v_perm_5142_, lean_object* v_inst_5143_, lean_object* v_R_5144_, lean_object* v_a_5145_, lean_object* v_b_5146_, lean_object* v_c_5147_){
_start:
{
lean_object* v_res_5148_; 
v_res_5148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5139_, v_xs_5140_, v_upperBound_5141_, v_perm_5142_, v_inst_5143_, v_R_5144_, v_a_5145_, v_b_5146_, v_c_5147_);
lean_dec_ref(v_perm_5142_);
lean_dec(v_upperBound_5141_);
lean_dec_ref(v_xs_5140_);
return v_res_5148_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5149_){
_start:
{
lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5150_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5151_ = lean_panic_fn_borrowed(v___x_5150_, v_msg_5149_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5152_, lean_object* v_msg_5153_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5153_);
return v___x_5154_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5155_, lean_object* v___x_5156_, lean_object* v_i_5157_, lean_object* v___x_5158_, lean_object* v_as_5159_, size_t v_i_5160_, size_t v_stop_5161_){
_start:
{
uint8_t v___x_5162_; 
v___x_5162_ = lean_usize_dec_eq(v_i_5160_, v_stop_5161_);
if (v___x_5162_ == 0)
{
uint8_t v___x_5163_; uint8_t v___y_5165_; lean_object* v___x_5169_; 
v___x_5163_ = 1;
v___x_5169_ = lean_array_uget_borrowed(v_as_5159_, v_i_5160_);
if (lean_obj_tag(v___x_5169_) == 0)
{
uint8_t v___x_5170_; 
v___x_5170_ = lean_nat_dec_lt(v_j_5155_, v___x_5156_);
v___y_5165_ = v___x_5170_;
goto v___jp_5164_;
}
else
{
uint8_t v___x_5171_; 
v___x_5171_ = lean_nat_dec_lt(v_i_5157_, v___x_5158_);
v___y_5165_ = v___x_5171_;
goto v___jp_5164_;
}
v___jp_5164_:
{
if (v___y_5165_ == 0)
{
size_t v___x_5166_; size_t v___x_5167_; 
v___x_5166_ = ((size_t)1ULL);
v___x_5167_ = lean_usize_add(v_i_5160_, v___x_5166_);
v_i_5160_ = v___x_5167_;
goto _start;
}
else
{
return v___x_5163_;
}
}
}
else
{
uint8_t v___x_5172_; 
v___x_5172_ = 0;
return v___x_5172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5173_, lean_object* v___x_5174_, lean_object* v_i_5175_, lean_object* v___x_5176_, lean_object* v_as_5177_, lean_object* v_i_5178_, lean_object* v_stop_5179_){
_start:
{
size_t v_i_boxed_5180_; size_t v_stop_boxed_5181_; uint8_t v_res_5182_; lean_object* v_r_5183_; 
v_i_boxed_5180_ = lean_unbox_usize(v_i_5178_);
lean_dec(v_i_5178_);
v_stop_boxed_5181_ = lean_unbox_usize(v_stop_5179_);
lean_dec(v_stop_5179_);
v_res_5182_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5173_, v___x_5174_, v_i_5175_, v___x_5176_, v_as_5177_, v_i_boxed_5180_, v_stop_boxed_5181_);
lean_dec_ref(v_as_5177_);
lean_dec(v___x_5176_);
lean_dec(v_i_5175_);
lean_dec(v___x_5174_);
lean_dec(v_j_5173_);
v_r_5183_ = lean_box(v_res_5182_);
return v_r_5183_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; 
v___x_5186_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5187_ = lean_unsigned_to_nat(10u);
v___x_5188_ = lean_unsigned_to_nat(425u);
v___x_5189_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5190_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5191_ = l_mkPanicMessageWithDecl(v___x_5190_, v___x_5189_, v___x_5188_, v___x_5187_, v___x_5186_);
return v___x_5191_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5193_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5194_ = lean_unsigned_to_nat(12u);
v___x_5195_ = lean_unsigned_to_nat(433u);
v___x_5196_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5197_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5198_ = l_mkPanicMessageWithDecl(v___x_5197_, v___x_5196_, v___x_5195_, v___x_5194_, v___x_5193_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5199_, lean_object* v_fixedArgs_5200_, lean_object* v_varyingArgs_5201_, lean_object* v_i_5202_, lean_object* v_j_5203_, lean_object* v_xs_5204_){
_start:
{
lean_object* v_lower_5206_; lean_object* v_upper_5207_; lean_object* v___x_5211_; uint8_t v___x_5212_; 
v___x_5211_ = lean_array_get_size(v_perm_5199_);
v___x_5212_ = lean_nat_dec_lt(v_i_5202_, v___x_5211_);
if (v___x_5212_ == 0)
{
lean_object* v___x_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; 
lean_dec(v_i_5202_);
lean_dec_ref(v_perm_5199_);
v___x_5213_ = lean_unsigned_to_nat(0u);
v___x_5214_ = lean_array_get_size(v_varyingArgs_5201_);
v___x_5215_ = lean_nat_dec_le(v_j_5203_, v___x_5213_);
if (v___x_5215_ == 0)
{
v_lower_5206_ = v_j_5203_;
v_upper_5207_ = v___x_5214_;
goto v___jp_5205_;
}
else
{
lean_dec(v_j_5203_);
v_lower_5206_ = v___x_5213_;
v_upper_5207_ = v___x_5214_;
goto v___jp_5205_;
}
}
else
{
lean_object* v___x_5216_; 
v___x_5216_ = lean_array_fget_borrowed(v_perm_5199_, v_i_5202_);
if (lean_obj_tag(v___x_5216_) == 1)
{
lean_object* v_val_5217_; lean_object* v___x_5218_; uint8_t v___x_5219_; 
v_val_5217_ = lean_ctor_get(v___x_5216_, 0);
v___x_5218_ = lean_array_get_size(v_fixedArgs_5200_);
v___x_5219_ = lean_nat_dec_lt(v_val_5217_, v___x_5218_);
if (v___x_5219_ == 0)
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
lean_dec_ref(v_xs_5204_);
lean_dec(v_j_5203_);
lean_dec(v_i_5202_);
lean_dec_ref(v_varyingArgs_5201_);
lean_dec_ref(v_perm_5199_);
v___x_5220_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5221_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5220_);
return v___x_5221_;
}
else
{
lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v___x_5222_ = lean_unsigned_to_nat(1u);
v___x_5223_ = lean_nat_add(v_i_5202_, v___x_5222_);
lean_dec(v_i_5202_);
v___x_5224_ = lean_array_fget_borrowed(v_fixedArgs_5200_, v_val_5217_);
lean_inc(v___x_5224_);
v___x_5225_ = lean_array_push(v_xs_5204_, v___x_5224_);
v_i_5202_ = v___x_5223_;
v_xs_5204_ = v___x_5225_;
goto _start;
}
}
else
{
lean_object* v___x_5227_; lean_object* v___y_5229_; lean_object* v___y_5230_; lean_object* v___y_5231_; lean_object* v_lower_5239_; lean_object* v_upper_5240_; uint8_t v___x_5248_; 
v___x_5227_ = lean_array_get_size(v_varyingArgs_5201_);
v___x_5248_ = lean_nat_dec_lt(v_j_5203_, v___x_5227_);
if (v___x_5248_ == 0)
{
lean_object* v___x_5249_; uint8_t v___x_5250_; 
lean_dec_ref(v_varyingArgs_5201_);
v___x_5249_ = lean_unsigned_to_nat(0u);
v___x_5250_ = lean_nat_dec_le(v_i_5202_, v___x_5249_);
if (v___x_5250_ == 0)
{
lean_inc(v_i_5202_);
v_lower_5239_ = v_i_5202_;
v_upper_5240_ = v___x_5211_;
goto v___jp_5238_;
}
else
{
v_lower_5239_ = v___x_5249_;
v_upper_5240_ = v___x_5211_;
goto v___jp_5238_;
}
}
else
{
lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5251_ = lean_unsigned_to_nat(1u);
v___x_5252_ = lean_nat_add(v_i_5202_, v___x_5251_);
lean_dec(v_i_5202_);
v___x_5253_ = lean_nat_add(v_j_5203_, v___x_5251_);
v___x_5254_ = lean_array_fget_borrowed(v_varyingArgs_5201_, v_j_5203_);
lean_dec(v_j_5203_);
lean_inc(v___x_5254_);
v___x_5255_ = lean_array_push(v_xs_5204_, v___x_5254_);
v_i_5202_ = v___x_5252_;
v_j_5203_ = v___x_5253_;
v_xs_5204_ = v___x_5255_;
goto _start;
}
v___jp_5228_:
{
uint8_t v___x_5232_; 
v___x_5232_ = lean_nat_dec_lt(v___y_5230_, v___y_5231_);
if (v___x_5232_ == 0)
{
lean_dec(v___y_5231_);
lean_dec(v___y_5230_);
lean_dec_ref(v___y_5229_);
lean_dec(v_j_5203_);
lean_dec(v_i_5202_);
return v_xs_5204_;
}
else
{
size_t v___x_5233_; size_t v___x_5234_; uint8_t v___x_5235_; 
v___x_5233_ = lean_usize_of_nat(v___y_5230_);
lean_dec(v___y_5230_);
v___x_5234_ = lean_usize_of_nat(v___y_5231_);
lean_dec(v___y_5231_);
v___x_5235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5203_, v___x_5227_, v_i_5202_, v___x_5211_, v___y_5229_, v___x_5233_, v___x_5234_);
lean_dec_ref(v___y_5229_);
lean_dec(v_i_5202_);
lean_dec(v_j_5203_);
if (v___x_5235_ == 0)
{
return v_xs_5204_;
}
else
{
lean_object* v___x_5236_; lean_object* v___x_5237_; 
lean_dec_ref(v_xs_5204_);
v___x_5236_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5237_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5236_);
return v___x_5237_;
}
}
}
v___jp_5238_:
{
lean_object* v___x_5241_; lean_object* v_array_5242_; lean_object* v_start_5243_; lean_object* v_stop_5244_; uint8_t v___x_5245_; 
v___x_5241_ = l_Array_toSubarray___redArg(v_perm_5199_, v_lower_5239_, v_upper_5240_);
v_array_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc_ref(v_array_5242_);
v_start_5243_ = lean_ctor_get(v___x_5241_, 1);
lean_inc(v_start_5243_);
v_stop_5244_ = lean_ctor_get(v___x_5241_, 2);
lean_inc(v_stop_5244_);
lean_dec_ref(v___x_5241_);
v___x_5245_ = lean_nat_dec_lt(v_start_5243_, v_stop_5244_);
if (v___x_5245_ == 0)
{
lean_dec(v_stop_5244_);
lean_dec(v_start_5243_);
lean_dec_ref(v_array_5242_);
lean_dec(v_j_5203_);
lean_dec(v_i_5202_);
return v_xs_5204_;
}
else
{
lean_object* v___x_5246_; uint8_t v___x_5247_; 
v___x_5246_ = lean_array_get_size(v_array_5242_);
v___x_5247_ = lean_nat_dec_le(v_stop_5244_, v___x_5246_);
if (v___x_5247_ == 0)
{
lean_dec(v_stop_5244_);
v___y_5229_ = v_array_5242_;
v___y_5230_ = v_start_5243_;
v___y_5231_ = v___x_5246_;
goto v___jp_5228_;
}
else
{
v___y_5229_ = v_array_5242_;
v___y_5230_ = v_start_5243_;
v___y_5231_ = v_stop_5244_;
goto v___jp_5228_;
}
}
}
}
}
v___jp_5205_:
{
lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; 
v___x_5208_ = l_Array_toSubarray___redArg(v_varyingArgs_5201_, v_lower_5206_, v_upper_5207_);
v___x_5209_ = l_Subarray_copy___redArg(v___x_5208_);
v___x_5210_ = l_Array_append___redArg(v_xs_5204_, v___x_5209_);
lean_dec_ref(v___x_5209_);
return v___x_5210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5257_, lean_object* v_fixedArgs_5258_, lean_object* v_varyingArgs_5259_, lean_object* v_i_5260_, lean_object* v_j_5261_, lean_object* v_xs_5262_){
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5257_, v_fixedArgs_5258_, v_varyingArgs_5259_, v_i_5260_, v_j_5261_, v_xs_5262_);
lean_dec_ref(v_fixedArgs_5258_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5264_, lean_object* v_perm_5265_, lean_object* v_fixedArgs_5266_, lean_object* v_varyingArgs_5267_, lean_object* v_i_5268_, lean_object* v_j_5269_, lean_object* v_xs_5270_){
_start:
{
lean_object* v___x_5271_; 
v___x_5271_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5265_, v_fixedArgs_5266_, v_varyingArgs_5267_, v_i_5268_, v_j_5269_, v_xs_5270_);
return v___x_5271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5272_, lean_object* v_perm_5273_, lean_object* v_fixedArgs_5274_, lean_object* v_varyingArgs_5275_, lean_object* v_i_5276_, lean_object* v_j_5277_, lean_object* v_xs_5278_){
_start:
{
lean_object* v_res_5279_; 
v_res_5279_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5272_, v_perm_5273_, v_fixedArgs_5274_, v_varyingArgs_5275_, v_i_5276_, v_j_5277_, v_xs_5278_);
lean_dec_ref(v_fixedArgs_5274_);
return v_res_5279_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5282_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5283_ = lean_unsigned_to_nat(2u);
v___x_5284_ = lean_unsigned_to_nat(416u);
v___x_5285_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5286_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5287_ = l_mkPanicMessageWithDecl(v___x_5286_, v___x_5285_, v___x_5284_, v___x_5283_, v___x_5282_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5288_, lean_object* v_fixedArgs_5289_, lean_object* v_varyingArgs_5290_){
_start:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; uint8_t v___x_5293_; 
v___x_5291_ = lean_array_get_size(v_fixedArgs_5289_);
v___x_5292_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5288_);
v___x_5293_ = lean_nat_dec_eq(v___x_5291_, v___x_5292_);
lean_dec(v___x_5292_);
if (v___x_5293_ == 0)
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
lean_dec_ref(v_varyingArgs_5290_);
lean_dec_ref(v_perm_5288_);
v___x_5294_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5295_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5294_);
return v___x_5295_;
}
else
{
lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5296_ = lean_unsigned_to_nat(0u);
v___x_5297_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5298_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5288_, v_fixedArgs_5289_, v_varyingArgs_5290_, v___x_5296_, v___x_5296_, v___x_5297_);
return v___x_5298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5299_, lean_object* v_fixedArgs_5300_, lean_object* v_varyingArgs_5301_){
_start:
{
lean_object* v_res_5302_; 
v_res_5302_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5299_, v_fixedArgs_5300_, v_varyingArgs_5301_);
lean_dec_ref(v_fixedArgs_5300_);
return v_res_5302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5303_, lean_object* v_perm_5304_, lean_object* v_fixedArgs_5305_, lean_object* v_varyingArgs_5306_){
_start:
{
lean_object* v___x_5307_; 
v___x_5307_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5304_, v_fixedArgs_5305_, v_varyingArgs_5306_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5308_, lean_object* v_perm_5309_, lean_object* v_fixedArgs_5310_, lean_object* v_varyingArgs_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5308_, v_perm_5309_, v_fixedArgs_5310_, v_varyingArgs_5311_);
lean_dec_ref(v_fixedArgs_5310_);
return v_res_5312_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5313_, lean_object* v_x_5314_){
_start:
{
if (lean_obj_tag(v_x_5313_) == 0)
{
if (lean_obj_tag(v_x_5314_) == 0)
{
uint8_t v___x_5315_; 
v___x_5315_ = 1;
return v___x_5315_;
}
else
{
uint8_t v___x_5316_; 
v___x_5316_ = 0;
return v___x_5316_;
}
}
else
{
if (lean_obj_tag(v_x_5314_) == 0)
{
uint8_t v___x_5317_; 
v___x_5317_ = 0;
return v___x_5317_;
}
else
{
lean_object* v_val_5318_; lean_object* v_val_5319_; uint8_t v___x_5320_; 
v_val_5318_ = lean_ctor_get(v_x_5313_, 0);
v_val_5319_ = lean_ctor_get(v_x_5314_, 0);
v___x_5320_ = lean_nat_dec_eq(v_val_5318_, v_val_5319_);
return v___x_5320_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5321_, lean_object* v_x_5322_){
_start:
{
uint8_t v_res_5323_; lean_object* v_r_5324_; 
v_res_5323_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5321_, v_x_5322_);
lean_dec(v_x_5322_);
lean_dec(v_x_5321_);
v_r_5324_ = lean_box(v_res_5323_);
return v_r_5324_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5325_, lean_object* v_ys_5326_, lean_object* v_x_5327_){
_start:
{
lean_object* v_zero_5328_; uint8_t v_isZero_5329_; 
v_zero_5328_ = lean_unsigned_to_nat(0u);
v_isZero_5329_ = lean_nat_dec_eq(v_x_5327_, v_zero_5328_);
if (v_isZero_5329_ == 1)
{
lean_dec(v_x_5327_);
return v_isZero_5329_;
}
else
{
lean_object* v_one_5330_; lean_object* v_n_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; uint8_t v___x_5334_; 
v_one_5330_ = lean_unsigned_to_nat(1u);
v_n_5331_ = lean_nat_sub(v_x_5327_, v_one_5330_);
lean_dec(v_x_5327_);
v___x_5332_ = lean_array_fget_borrowed(v_xs_5325_, v_n_5331_);
v___x_5333_ = lean_array_fget_borrowed(v_ys_5326_, v_n_5331_);
v___x_5334_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5332_, v___x_5333_);
if (v___x_5334_ == 0)
{
lean_dec(v_n_5331_);
return v___x_5334_;
}
else
{
v_x_5327_ = v_n_5331_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5336_, lean_object* v_ys_5337_, lean_object* v_x_5338_){
_start:
{
uint8_t v_res_5339_; lean_object* v_r_5340_; 
v_res_5339_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5336_, v_ys_5337_, v_x_5338_);
lean_dec_ref(v_ys_5337_);
lean_dec_ref(v_xs_5336_);
v_r_5340_ = lean_box(v_res_5339_);
return v_r_5340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5341_, size_t v_i_5342_, lean_object* v_bs_5343_){
_start:
{
uint8_t v___x_5344_; 
v___x_5344_ = lean_usize_dec_lt(v_i_5342_, v_sz_5341_);
if (v___x_5344_ == 0)
{
return v_bs_5343_;
}
else
{
lean_object* v_v_5345_; lean_object* v___x_5346_; lean_object* v_bs_x27_5347_; lean_object* v___x_5348_; size_t v___x_5349_; size_t v___x_5350_; lean_object* v___x_5351_; 
v_v_5345_ = lean_array_uget(v_bs_5343_, v_i_5342_);
v___x_5346_ = lean_unsigned_to_nat(0u);
v_bs_x27_5347_ = lean_array_uset(v_bs_5343_, v_i_5342_, v___x_5346_);
v___x_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5348_, 0, v_v_5345_);
v___x_5349_ = ((size_t)1ULL);
v___x_5350_ = lean_usize_add(v_i_5342_, v___x_5349_);
v___x_5351_ = lean_array_uset(v_bs_x27_5347_, v_i_5342_, v___x_5348_);
v_i_5342_ = v___x_5350_;
v_bs_5343_ = v___x_5351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5353_, lean_object* v_i_5354_, lean_object* v_bs_5355_){
_start:
{
size_t v_sz_boxed_5356_; size_t v_i_boxed_5357_; lean_object* v_res_5358_; 
v_sz_boxed_5356_ = lean_unbox_usize(v_sz_5353_);
lean_dec(v_sz_5353_);
v_i_boxed_5357_ = lean_unbox_usize(v_i_5354_);
lean_dec(v_i_5354_);
v_res_5358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5356_, v_i_boxed_5357_, v_bs_5355_);
return v_res_5358_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5359_, lean_object* v_as_5360_, size_t v_i_5361_, size_t v_stop_5362_){
_start:
{
uint8_t v___x_5363_; 
v___x_5363_ = lean_usize_dec_eq(v_i_5361_, v_stop_5362_);
if (v___x_5363_ == 0)
{
lean_object* v_numFixed_5364_; uint8_t v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; size_t v_sz_5368_; size_t v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; uint8_t v___x_5377_; 
v_numFixed_5364_ = lean_ctor_get(v_fixedParamPerms_5359_, 0);
v___x_5365_ = 1;
v___x_5366_ = lean_array_uget_borrowed(v_as_5360_, v_i_5361_);
lean_inc(v_numFixed_5364_);
v___x_5367_ = l_Array_range(v_numFixed_5364_);
v_sz_5368_ = lean_array_size(v___x_5367_);
v___x_5369_ = ((size_t)0ULL);
v___x_5370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5368_, v___x_5369_, v___x_5367_);
v___x_5371_ = lean_array_get_size(v___x_5366_);
v___x_5372_ = lean_nat_sub(v___x_5371_, v_numFixed_5364_);
v___x_5373_ = lean_box(0);
v___x_5374_ = lean_mk_array(v___x_5372_, v___x_5373_);
v___x_5375_ = l_Array_append___redArg(v___x_5370_, v___x_5374_);
lean_dec_ref(v___x_5374_);
v___x_5376_ = lean_array_get_size(v___x_5375_);
v___x_5377_ = lean_nat_dec_eq(v___x_5371_, v___x_5376_);
if (v___x_5377_ == 0)
{
lean_dec_ref(v___x_5375_);
lean_dec_ref(v_fixedParamPerms_5359_);
return v___x_5365_;
}
else
{
uint8_t v___x_5378_; 
v___x_5378_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5366_, v___x_5375_, v___x_5371_);
lean_dec_ref(v___x_5375_);
if (v___x_5378_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5359_);
return v___x_5365_;
}
else
{
size_t v___x_5379_; size_t v___x_5380_; 
v___x_5379_ = ((size_t)1ULL);
v___x_5380_ = lean_usize_add(v_i_5361_, v___x_5379_);
v_i_5361_ = v___x_5380_;
goto _start;
}
}
}
else
{
uint8_t v___x_5382_; 
lean_dec_ref(v_fixedParamPerms_5359_);
v___x_5382_ = 0;
return v___x_5382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5383_, lean_object* v_as_5384_, lean_object* v_i_5385_, lean_object* v_stop_5386_){
_start:
{
size_t v_i_boxed_5387_; size_t v_stop_boxed_5388_; uint8_t v_res_5389_; lean_object* v_r_5390_; 
v_i_boxed_5387_ = lean_unbox_usize(v_i_5385_);
lean_dec(v_i_5385_);
v_stop_boxed_5388_ = lean_unbox_usize(v_stop_5386_);
lean_dec(v_stop_5386_);
v_res_5389_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5383_, v_as_5384_, v_i_boxed_5387_, v_stop_boxed_5388_);
lean_dec_ref(v_as_5384_);
v_r_5390_ = lean_box(v_res_5389_);
return v_r_5390_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5391_){
_start:
{
lean_object* v_perms_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; uint8_t v___x_5395_; 
v_perms_5392_ = lean_ctor_get(v_fixedParamPerms_5391_, 1);
lean_inc_ref(v_perms_5392_);
v___x_5393_ = lean_unsigned_to_nat(0u);
v___x_5394_ = lean_array_get_size(v_perms_5392_);
v___x_5395_ = lean_nat_dec_lt(v___x_5393_, v___x_5394_);
if (v___x_5395_ == 0)
{
uint8_t v___x_5396_; 
lean_dec_ref(v_perms_5392_);
lean_dec_ref(v_fixedParamPerms_5391_);
v___x_5396_ = 1;
return v___x_5396_;
}
else
{
if (v___x_5395_ == 0)
{
lean_dec_ref(v_perms_5392_);
lean_dec_ref(v_fixedParamPerms_5391_);
return v___x_5395_;
}
else
{
size_t v___x_5397_; size_t v___x_5398_; uint8_t v___x_5399_; 
v___x_5397_ = ((size_t)0ULL);
v___x_5398_ = lean_usize_of_nat(v___x_5394_);
v___x_5399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5391_, v_perms_5392_, v___x_5397_, v___x_5398_);
lean_dec_ref(v_perms_5392_);
if (v___x_5399_ == 0)
{
return v___x_5395_;
}
else
{
uint8_t v___x_5400_; 
v___x_5400_ = 0;
return v___x_5400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5401_){
_start:
{
uint8_t v_res_5402_; lean_object* v_r_5403_; 
v_res_5402_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5401_);
v_r_5403_ = lean_box(v_res_5402_);
return v_r_5403_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5404_, lean_object* v_ys_5405_, lean_object* v_hsz_5406_, lean_object* v_x_5407_, lean_object* v_x_5408_){
_start:
{
uint8_t v___x_5409_; 
v___x_5409_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5404_, v_ys_5405_, v_x_5407_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5410_, lean_object* v_ys_5411_, lean_object* v_hsz_5412_, lean_object* v_x_5413_, lean_object* v_x_5414_){
_start:
{
uint8_t v_res_5415_; lean_object* v_r_5416_; 
v_res_5415_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5410_, v_ys_5411_, v_hsz_5412_, v_x_5413_, v_x_5414_);
lean_dec_ref(v_ys_5411_);
lean_dec_ref(v_xs_5410_);
v_r_5416_ = lean_box(v_res_5415_);
return v_r_5416_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; 
v___x_5417_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5418_, 0, v___x_5417_);
lean_ctor_set(v___x_5418_, 1, v___x_5417_);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5419_){
_start:
{
lean_object* v___f_5420_; lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___f_5423_; lean_object* v___f_5424_; lean_object* v___f_5425_; lean_object* v___f_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___f_5420_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5421_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5422_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5423_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5424_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5425_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5426_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5427_, 0, v___f_5420_);
lean_ctor_set(v___x_5427_, 1, v___f_5421_);
v___x_5428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5427_);
lean_ctor_set(v___x_5428_, 1, v___f_5422_);
lean_ctor_set(v___x_5428_, 2, v___f_5423_);
lean_ctor_set(v___x_5428_, 3, v___f_5424_);
lean_ctor_set(v___x_5428_, 4, v___f_5425_);
v___x_5429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5428_);
lean_ctor_set(v___x_5429_, 1, v___f_5426_);
v___x_5430_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5431_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5430_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = l_instInhabitedOfMonad___redArg(v___x_5429_, v___x_5432_);
v___x_5434_ = lean_panic_fn_borrowed(v___x_5433_, v_msg_5419_);
lean_dec(v___x_5433_);
return v___x_5434_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; 
v___x_5435_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5436_, 0, v___x_5435_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5437_){
_start:
{
lean_object* v___f_5438_; lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___f_5441_; lean_object* v___f_5442_; lean_object* v___f_5443_; lean_object* v___f_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___f_5438_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5439_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5440_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5441_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5442_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5443_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5444_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___f_5438_);
lean_ctor_set(v___x_5445_, 1, v___f_5439_);
v___x_5446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5446_, 0, v___x_5445_);
lean_ctor_set(v___x_5446_, 1, v___f_5440_);
lean_ctor_set(v___x_5446_, 2, v___f_5441_);
lean_ctor_set(v___x_5446_, 3, v___f_5442_);
lean_ctor_set(v___x_5446_, 4, v___f_5443_);
v___x_5447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5447_, 0, v___x_5446_);
lean_ctor_set(v___x_5447_, 1, v___f_5444_);
v___x_5448_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5449_ = l_instInhabitedOfMonad___redArg(v___x_5447_, v___x_5448_);
v___x_5450_ = lean_panic_fn_borrowed(v___x_5449_, v_msg_5437_);
lean_dec(v___x_5449_);
return v___x_5450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5451_, uint8_t v___x_5452_, lean_object* v___x_5453_, lean_object* v___x_5454_, lean_object* v_as_5455_, size_t v_sz_5456_, size_t v_i_5457_, lean_object* v_b_5458_){
_start:
{
lean_object* v_a_5460_; uint8_t v___x_5464_; 
v___x_5464_ = lean_usize_dec_lt(v_i_5457_, v_sz_5456_);
if (v___x_5464_ == 0)
{
return v_b_5458_;
}
else
{
lean_object* v_fst_5465_; lean_object* v_snd_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5488_; 
v_fst_5465_ = lean_ctor_get(v_b_5458_, 0);
v_snd_5466_ = lean_ctor_get(v_b_5458_, 1);
v_isSharedCheck_5488_ = !lean_is_exclusive(v_b_5458_);
if (v_isSharedCheck_5488_ == 0)
{
v___x_5468_ = v_b_5458_;
v_isShared_5469_ = v_isSharedCheck_5488_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_snd_5466_);
lean_inc(v_fst_5465_);
lean_dec(v_b_5458_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5488_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5474_; lean_object* v_a_5475_; lean_object* v___x_5476_; 
v___x_5474_ = lean_box(0);
v_a_5475_ = lean_array_uget_borrowed(v_as_5455_, v_i_5457_);
v___x_5476_ = lean_array_get_borrowed(v___x_5474_, v___x_5451_, v_a_5475_);
if (lean_obj_tag(v___x_5476_) == 1)
{
lean_object* v_val_5477_; uint8_t v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; uint8_t v___x_5481_; 
v_val_5477_ = lean_ctor_get(v___x_5476_, 0);
v___x_5478_ = 0;
v___x_5479_ = lean_box(v___x_5478_);
v___x_5480_ = lean_array_get(v___x_5479_, v_fst_5465_, v_val_5477_);
lean_dec(v___x_5479_);
v___x_5481_ = lean_unbox(v___x_5480_);
lean_dec(v___x_5480_);
if (v___x_5481_ == 0)
{
if (v___x_5452_ == 0)
{
goto v___jp_5470_;
}
else
{
uint8_t v_changed_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
lean_del_object(v___x_5468_);
lean_dec(v_snd_5466_);
v_changed_5482_ = lean_nat_dec_eq(v___x_5453_, v___x_5454_);
v___x_5483_ = lean_box(v_changed_5482_);
v___x_5484_ = lean_array_set(v_fst_5465_, v_val_5477_, v___x_5483_);
v___x_5485_ = lean_box(v_changed_5482_);
v___x_5486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5486_, 0, v___x_5484_);
lean_ctor_set(v___x_5486_, 1, v___x_5485_);
v_a_5460_ = v___x_5486_;
goto v___jp_5459_;
}
}
else
{
goto v___jp_5470_;
}
}
else
{
lean_object* v___x_5487_; 
lean_del_object(v___x_5468_);
v___x_5487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5487_, 0, v_fst_5465_);
lean_ctor_set(v___x_5487_, 1, v_snd_5466_);
v_a_5460_ = v___x_5487_;
goto v___jp_5459_;
}
v___jp_5470_:
{
lean_object* v___x_5472_; 
if (v_isShared_5469_ == 0)
{
v___x_5472_ = v___x_5468_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_fst_5465_);
lean_ctor_set(v_reuseFailAlloc_5473_, 1, v_snd_5466_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
v_a_5460_ = v___x_5472_;
goto v___jp_5459_;
}
}
}
}
v___jp_5459_:
{
size_t v___x_5461_; size_t v___x_5462_; 
v___x_5461_ = ((size_t)1ULL);
v___x_5462_ = lean_usize_add(v_i_5457_, v___x_5461_);
v_i_5457_ = v___x_5462_;
v_b_5458_ = v_a_5460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5489_, lean_object* v___x_5490_, lean_object* v___x_5491_, lean_object* v___x_5492_, lean_object* v_as_5493_, lean_object* v_sz_5494_, lean_object* v_i_5495_, lean_object* v_b_5496_){
_start:
{
uint8_t v___x_7006__boxed_5497_; size_t v_sz_boxed_5498_; size_t v_i_boxed_5499_; lean_object* v_res_5500_; 
v___x_7006__boxed_5497_ = lean_unbox(v___x_5490_);
v_sz_boxed_5498_ = lean_unbox_usize(v_sz_5494_);
lean_dec(v_sz_5494_);
v_i_boxed_5499_ = lean_unbox_usize(v_i_5495_);
lean_dec(v_i_5495_);
v_res_5500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5489_, v___x_7006__boxed_5497_, v___x_5491_, v___x_5492_, v_as_5493_, v_sz_boxed_5498_, v_i_boxed_5499_, v_b_5496_);
lean_dec_ref(v_as_5493_);
lean_dec(v___x_5492_);
lean_dec(v___x_5491_);
lean_dec_ref(v___x_5489_);
return v_res_5500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object* v_upperBound_5501_, lean_object* v___x_5502_, lean_object* v_fixedParamPerms_5503_, lean_object* v_next_5504_, lean_object* v___x_5505_, lean_object* v___x_5506_, lean_object* v_a_5507_, lean_object* v_b_5508_){
_start:
{
lean_object* v_a_5510_; uint8_t v___x_5514_; 
v___x_5514_ = lean_nat_dec_lt(v_a_5507_, v_upperBound_5501_);
if (v___x_5514_ == 0)
{
lean_dec(v_a_5507_);
return v_b_5508_;
}
else
{
lean_object* v_fst_5515_; lean_object* v_snd_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5552_; 
v_fst_5515_ = lean_ctor_get(v_b_5508_, 0);
v_snd_5516_ = lean_ctor_get(v_b_5508_, 1);
v_isSharedCheck_5552_ = !lean_is_exclusive(v_b_5508_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5518_ = v_b_5508_;
v_isShared_5519_ = v_isSharedCheck_5552_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_snd_5516_);
lean_inc(v_fst_5515_);
lean_dec(v_b_5508_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5552_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5520_; 
v___x_5520_ = lean_array_fget_borrowed(v___x_5502_, v_a_5507_);
if (lean_obj_tag(v___x_5520_) == 1)
{
lean_object* v_val_5521_; uint8_t v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; uint8_t v___x_5525_; 
v_val_5521_ = lean_ctor_get(v___x_5520_, 0);
v___x_5522_ = 0;
v___x_5523_ = lean_box(v___x_5522_);
v___x_5524_ = lean_array_get(v___x_5523_, v_fst_5515_, v_val_5521_);
lean_dec(v___x_5523_);
v___x_5525_ = lean_unbox(v___x_5524_);
if (v___x_5525_ == 0)
{
lean_object* v___x_5527_; 
lean_dec(v___x_5524_);
if (v_isShared_5519_ == 0)
{
v___x_5527_ = v___x_5518_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v_fst_5515_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v_snd_5516_);
v___x_5527_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
v_a_5510_ = v___x_5527_;
goto v___jp_5509_;
}
}
else
{
lean_object* v_revDeps_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5534_; 
v_revDeps_5529_ = lean_ctor_get(v_fixedParamPerms_5503_, 2);
v___x_5530_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5531_ = lean_array_get_borrowed(v___x_5530_, v_revDeps_5529_, v_next_5504_);
v___x_5532_ = lean_array_get_borrowed(v___x_5530_, v___x_5531_, v_a_5507_);
if (v_isShared_5519_ == 0)
{
v___x_5534_ = v___x_5518_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_fst_5515_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_snd_5516_);
v___x_5534_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
size_t v_sz_5535_; size_t v___x_5536_; uint8_t v___x_5537_; lean_object* v___x_5538_; lean_object* v_fst_5539_; lean_object* v_snd_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
v_sz_5535_ = lean_array_size(v___x_5532_);
v___x_5536_ = ((size_t)0ULL);
v___x_5537_ = lean_unbox(v___x_5524_);
lean_dec(v___x_5524_);
v___x_5538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5502_, v___x_5537_, v___x_5505_, v___x_5506_, v___x_5532_, v_sz_5535_, v___x_5536_, v___x_5534_);
v_fst_5539_ = lean_ctor_get(v___x_5538_, 0);
v_snd_5540_ = lean_ctor_get(v___x_5538_, 1);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5538_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_snd_5540_);
lean_inc(v_fst_5539_);
lean_dec(v___x_5538_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_fst_5539_);
lean_ctor_set(v_reuseFailAlloc_5546_, 1, v_snd_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
v_a_5510_ = v___x_5545_;
goto v___jp_5509_;
}
}
}
}
}
else
{
lean_object* v___x_5550_; 
if (v_isShared_5519_ == 0)
{
v___x_5550_ = v___x_5518_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_fst_5515_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v_snd_5516_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
v_a_5510_ = v___x_5550_;
goto v___jp_5509_;
}
}
}
}
v___jp_5509_:
{
lean_object* v___x_5511_; lean_object* v___x_5512_; 
v___x_5511_ = lean_unsigned_to_nat(1u);
v___x_5512_ = lean_nat_add(v_a_5507_, v___x_5511_);
lean_dec(v_a_5507_);
v_a_5507_ = v___x_5512_;
v_b_5508_ = v_a_5510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object* v_upperBound_5553_, lean_object* v___x_5554_, lean_object* v_fixedParamPerms_5555_, lean_object* v_next_5556_, lean_object* v___x_5557_, lean_object* v___x_5558_, lean_object* v_a_5559_, lean_object* v_b_5560_){
_start:
{
lean_object* v_res_5561_; 
v_res_5561_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5553_, v___x_5554_, v_fixedParamPerms_5555_, v_next_5556_, v___x_5557_, v___x_5558_, v_a_5559_, v_b_5560_);
lean_dec(v___x_5558_);
lean_dec(v___x_5557_);
lean_dec(v_next_5556_);
lean_dec_ref(v_fixedParamPerms_5555_);
lean_dec_ref(v___x_5554_);
lean_dec(v_upperBound_5553_);
return v_res_5561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5562_, lean_object* v___x_5563_, lean_object* v___x_5564_, lean_object* v___x_5565_, lean_object* v_fixedParamPerms_5566_, lean_object* v_next_5567_, lean_object* v_a_5568_, lean_object* v_b_5569_){
_start:
{
lean_object* v_a_5571_; uint8_t v___x_5575_; 
v___x_5575_ = lean_nat_dec_lt(v_a_5568_, v_upperBound_5562_);
if (v___x_5575_ == 0)
{
return v_b_5569_;
}
else
{
lean_object* v_fst_5576_; lean_object* v_snd_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5613_; 
v_fst_5576_ = lean_ctor_get(v_b_5569_, 0);
v_snd_5577_ = lean_ctor_get(v_b_5569_, 1);
v_isSharedCheck_5613_ = !lean_is_exclusive(v_b_5569_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5579_ = v_b_5569_;
v_isShared_5580_ = v_isSharedCheck_5613_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_snd_5577_);
lean_inc(v_fst_5576_);
lean_dec(v_b_5569_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5613_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5581_; 
v___x_5581_ = lean_array_fget_borrowed(v___x_5563_, v_a_5568_);
if (lean_obj_tag(v___x_5581_) == 1)
{
lean_object* v_val_5582_; uint8_t v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; uint8_t v___x_5586_; 
v_val_5582_ = lean_ctor_get(v___x_5581_, 0);
v___x_5583_ = 0;
v___x_5584_ = lean_box(v___x_5583_);
v___x_5585_ = lean_array_get(v___x_5584_, v_fst_5576_, v_val_5582_);
lean_dec(v___x_5584_);
v___x_5586_ = lean_unbox(v___x_5585_);
if (v___x_5586_ == 0)
{
lean_object* v___x_5588_; 
lean_dec(v___x_5585_);
if (v_isShared_5580_ == 0)
{
v___x_5588_ = v___x_5579_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_fst_5576_);
lean_ctor_set(v_reuseFailAlloc_5589_, 1, v_snd_5577_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
v_a_5571_ = v___x_5588_;
goto v___jp_5570_;
}
}
else
{
lean_object* v_revDeps_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5595_; 
v_revDeps_5590_ = lean_ctor_get(v_fixedParamPerms_5566_, 2);
v___x_5591_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5592_ = lean_array_get_borrowed(v___x_5591_, v_revDeps_5590_, v_next_5567_);
v___x_5593_ = lean_array_get_borrowed(v___x_5591_, v___x_5592_, v_a_5568_);
if (v_isShared_5580_ == 0)
{
v___x_5595_ = v___x_5579_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_fst_5576_);
lean_ctor_set(v_reuseFailAlloc_5609_, 1, v_snd_5577_);
v___x_5595_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
size_t v_sz_5596_; size_t v___x_5597_; uint8_t v___x_5598_; lean_object* v___x_5599_; lean_object* v_fst_5600_; lean_object* v_snd_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5608_; 
v_sz_5596_ = lean_array_size(v___x_5593_);
v___x_5597_ = ((size_t)0ULL);
v___x_5598_ = lean_unbox(v___x_5585_);
lean_dec(v___x_5585_);
v___x_5599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5563_, v___x_5598_, v___x_5564_, v___x_5565_, v___x_5593_, v_sz_5596_, v___x_5597_, v___x_5595_);
v_fst_5600_ = lean_ctor_get(v___x_5599_, 0);
v_snd_5601_ = lean_ctor_get(v___x_5599_, 1);
v_isSharedCheck_5608_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5608_ == 0)
{
v___x_5603_ = v___x_5599_;
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_snd_5601_);
lean_inc(v_fst_5600_);
lean_dec(v___x_5599_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_fst_5600_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v_snd_5601_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
v_a_5571_ = v___x_5606_;
goto v___jp_5570_;
}
}
}
}
}
else
{
lean_object* v___x_5611_; 
if (v_isShared_5580_ == 0)
{
v___x_5611_ = v___x_5579_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_fst_5576_);
lean_ctor_set(v_reuseFailAlloc_5612_, 1, v_snd_5577_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
v_a_5571_ = v___x_5611_;
goto v___jp_5570_;
}
}
}
}
v___jp_5570_:
{
lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; 
v___x_5572_ = lean_unsigned_to_nat(1u);
v___x_5573_ = lean_nat_add(v_a_5568_, v___x_5572_);
v___x_5574_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5562_, v___x_5563_, v_fixedParamPerms_5566_, v_next_5567_, v___x_5564_, v___x_5565_, v___x_5573_, v_a_5571_);
return v___x_5574_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5614_, lean_object* v___x_5615_, lean_object* v___x_5616_, lean_object* v___x_5617_, lean_object* v_fixedParamPerms_5618_, lean_object* v_next_5619_, lean_object* v_a_5620_, lean_object* v_b_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5614_, v___x_5615_, v___x_5616_, v___x_5617_, v_fixedParamPerms_5618_, v_next_5619_, v_a_5620_, v_b_5621_);
lean_dec(v_a_5620_);
lean_dec(v_next_5619_);
lean_dec_ref(v_fixedParamPerms_5618_);
lean_dec(v___x_5617_);
lean_dec(v___x_5616_);
lean_dec_ref(v___x_5615_);
lean_dec(v_upperBound_5614_);
return v_res_5622_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5623_, lean_object* v___x_5624_, lean_object* v___x_5625_, lean_object* v___x_5626_, lean_object* v_fixedParamPerms_5627_, lean_object* v_a_5628_, lean_object* v_b_5629_){
_start:
{
uint8_t v___x_5630_; 
v___x_5630_ = lean_nat_dec_lt(v_a_5628_, v_upperBound_5623_);
if (v___x_5630_ == 0)
{
lean_dec(v_a_5628_);
return v_b_5629_;
}
else
{
lean_object* v_fst_5631_; lean_object* v_snd_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5655_; 
v_fst_5631_ = lean_ctor_get(v_b_5629_, 0);
v_snd_5632_ = lean_ctor_get(v_b_5629_, 1);
v_isSharedCheck_5655_ = !lean_is_exclusive(v_b_5629_);
if (v_isSharedCheck_5655_ == 0)
{
v___x_5634_ = v_b_5629_;
v_isShared_5635_ = v_isSharedCheck_5655_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_snd_5632_);
lean_inc(v_fst_5631_);
lean_dec(v_b_5629_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5655_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5640_; 
v___x_5636_ = lean_array_fget_borrowed(v___x_5624_, v_a_5628_);
v___x_5637_ = lean_array_get_size(v___x_5636_);
v___x_5638_ = lean_unsigned_to_nat(0u);
if (v_isShared_5635_ == 0)
{
v___x_5640_ = v___x_5634_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v_fst_5631_);
lean_ctor_set(v_reuseFailAlloc_5654_, 1, v_snd_5632_);
v___x_5640_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
lean_object* v___x_5641_; lean_object* v_fst_5642_; lean_object* v_snd_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5653_; 
v___x_5641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5637_, v___x_5636_, v___x_5625_, v___x_5626_, v_fixedParamPerms_5627_, v_a_5628_, v___x_5638_, v___x_5640_);
v_fst_5642_ = lean_ctor_get(v___x_5641_, 0);
v_snd_5643_ = lean_ctor_get(v___x_5641_, 1);
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5641_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5645_ = v___x_5641_;
v_isShared_5646_ = v_isSharedCheck_5653_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_snd_5643_);
lean_inc(v_fst_5642_);
lean_dec(v___x_5641_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5653_;
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
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_fst_5642_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_snd_5643_);
v___x_5648_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
lean_object* v___x_5649_; lean_object* v___x_5650_; 
v___x_5649_ = lean_unsigned_to_nat(1u);
v___x_5650_ = lean_nat_add(v_a_5628_, v___x_5649_);
lean_dec(v_a_5628_);
v_a_5628_ = v___x_5650_;
v_b_5629_ = v___x_5648_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5656_, lean_object* v___x_5657_, lean_object* v___x_5658_, lean_object* v___x_5659_, lean_object* v_fixedParamPerms_5660_, lean_object* v_a_5661_, lean_object* v_b_5662_){
_start:
{
lean_object* v_res_5663_; 
v_res_5663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5656_, v___x_5657_, v___x_5658_, v___x_5659_, v_fixedParamPerms_5660_, v_a_5661_, v_b_5662_);
lean_dec_ref(v_fixedParamPerms_5660_);
lean_dec(v___x_5659_);
lean_dec(v___x_5658_);
lean_dec_ref(v___x_5657_);
lean_dec(v_upperBound_5656_);
return v_res_5663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5664_, lean_object* v___x_5665_, lean_object* v___x_5666_, lean_object* v_fixedParamPerms_5667_, lean_object* v_a_5668_){
_start:
{
lean_object* v_snd_5669_; uint8_t v___x_5670_; 
v_snd_5669_ = lean_ctor_get(v_a_5668_, 1);
v___x_5670_ = lean_unbox(v_snd_5669_);
if (v___x_5670_ == 0)
{
lean_object* v_fst_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5678_; 
lean_inc(v_snd_5669_);
v_fst_5671_ = lean_ctor_get(v_a_5668_, 0);
v_isSharedCheck_5678_ = !lean_is_exclusive(v_a_5668_);
if (v_isSharedCheck_5678_ == 0)
{
lean_object* v_unused_5679_; 
v_unused_5679_ = lean_ctor_get(v_a_5668_, 1);
lean_dec(v_unused_5679_);
v___x_5673_ = v_a_5668_;
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_fst_5671_);
lean_dec(v_a_5668_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v___x_5676_; 
if (v_isShared_5674_ == 0)
{
v___x_5676_ = v___x_5673_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_fst_5671_);
lean_ctor_set(v_reuseFailAlloc_5677_, 1, v_snd_5669_);
v___x_5676_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
return v___x_5676_;
}
}
}
else
{
lean_object* v_fst_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5701_; 
v_fst_5680_ = lean_ctor_get(v_a_5668_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v_a_5668_);
if (v_isSharedCheck_5701_ == 0)
{
lean_object* v_unused_5702_; 
v_unused_5702_ = lean_ctor_get(v_a_5668_, 1);
lean_dec(v_unused_5702_);
v___x_5682_ = v_a_5668_;
v_isShared_5683_ = v_isSharedCheck_5701_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_fst_5680_);
lean_dec(v_a_5668_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5701_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
uint8_t v_changed_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5688_; 
v_changed_5684_ = 0;
v___x_5685_ = lean_unsigned_to_nat(0u);
v___x_5686_ = lean_box(v_changed_5684_);
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 1, v___x_5686_);
v___x_5688_ = v___x_5682_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_fst_5680_);
lean_ctor_set(v_reuseFailAlloc_5700_, 1, v___x_5686_);
v___x_5688_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
lean_object* v___x_5689_; lean_object* v_fst_5690_; lean_object* v_snd_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5699_; 
v___x_5689_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5664_, v___x_5665_, v___x_5666_, v___x_5664_, v_fixedParamPerms_5667_, v___x_5685_, v___x_5688_);
v_fst_5690_ = lean_ctor_get(v___x_5689_, 0);
v_snd_5691_ = lean_ctor_get(v___x_5689_, 1);
v_isSharedCheck_5699_ = !lean_is_exclusive(v___x_5689_);
if (v_isSharedCheck_5699_ == 0)
{
v___x_5693_ = v___x_5689_;
v_isShared_5694_ = v_isSharedCheck_5699_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_snd_5691_);
lean_inc(v_fst_5690_);
lean_dec(v___x_5689_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5699_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5696_; 
if (v_isShared_5694_ == 0)
{
v___x_5696_ = v___x_5693_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_fst_5690_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v_snd_5691_);
v___x_5696_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
v_a_5668_ = v___x_5696_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5703_, lean_object* v___x_5704_, lean_object* v___x_5705_, lean_object* v_fixedParamPerms_5706_, lean_object* v_a_5707_){
_start:
{
lean_object* v_res_5708_; 
v_res_5708_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5703_, v___x_5704_, v___x_5705_, v_fixedParamPerms_5706_, v_a_5707_);
lean_dec_ref(v_fixedParamPerms_5706_);
lean_dec(v___x_5705_);
lean_dec_ref(v___x_5704_);
lean_dec(v___x_5703_);
return v_res_5708_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5709_, lean_object* v_a_5710_, lean_object* v_b_5711_){
_start:
{
lean_object* v_a_5713_; uint8_t v___x_5717_; 
v___x_5717_ = lean_nat_dec_lt(v_a_5710_, v_upperBound_5709_);
if (v___x_5717_ == 0)
{
lean_dec(v_a_5710_);
return v_b_5711_;
}
else
{
lean_object* v_snd_5718_; lean_object* v_snd_5719_; lean_object* v_snd_5720_; lean_object* v_snd_5721_; lean_object* v_fst_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5834_; 
v_snd_5718_ = lean_ctor_get(v_b_5711_, 1);
lean_inc(v_snd_5718_);
v_snd_5719_ = lean_ctor_get(v_snd_5718_, 1);
lean_inc(v_snd_5719_);
v_snd_5720_ = lean_ctor_get(v_snd_5719_, 1);
lean_inc(v_snd_5720_);
v_snd_5721_ = lean_ctor_get(v_snd_5720_, 1);
lean_inc(v_snd_5721_);
v_fst_5722_ = lean_ctor_get(v_b_5711_, 0);
v_isSharedCheck_5834_ = !lean_is_exclusive(v_b_5711_);
if (v_isSharedCheck_5834_ == 0)
{
lean_object* v_unused_5835_; 
v_unused_5835_ = lean_ctor_get(v_b_5711_, 1);
lean_dec(v_unused_5835_);
v___x_5724_ = v_b_5711_;
v_isShared_5725_ = v_isSharedCheck_5834_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_fst_5722_);
lean_dec(v_b_5711_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5834_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v_fst_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5832_; 
v_fst_5726_ = lean_ctor_get(v_snd_5718_, 0);
v_isSharedCheck_5832_ = !lean_is_exclusive(v_snd_5718_);
if (v_isSharedCheck_5832_ == 0)
{
lean_object* v_unused_5833_; 
v_unused_5833_ = lean_ctor_get(v_snd_5718_, 1);
lean_dec(v_unused_5833_);
v___x_5728_ = v_snd_5718_;
v_isShared_5729_ = v_isSharedCheck_5832_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_fst_5726_);
lean_dec(v_snd_5718_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5832_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v_fst_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5830_; 
v_fst_5730_ = lean_ctor_get(v_snd_5719_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v_snd_5719_);
if (v_isSharedCheck_5830_ == 0)
{
lean_object* v_unused_5831_; 
v_unused_5831_ = lean_ctor_get(v_snd_5719_, 1);
lean_dec(v_unused_5831_);
v___x_5732_ = v_snd_5719_;
v_isShared_5733_ = v_isSharedCheck_5830_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_fst_5730_);
lean_dec(v_snd_5719_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5830_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v_fst_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5828_; 
v_fst_5734_ = lean_ctor_get(v_snd_5720_, 0);
v_isSharedCheck_5828_ = !lean_is_exclusive(v_snd_5720_);
if (v_isSharedCheck_5828_ == 0)
{
lean_object* v_unused_5829_; 
v_unused_5829_ = lean_ctor_get(v_snd_5720_, 1);
lean_dec(v_unused_5829_);
v___x_5736_ = v_snd_5720_;
v_isShared_5737_ = v_isSharedCheck_5828_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_fst_5734_);
lean_dec(v_snd_5720_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5828_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v_array_5738_; lean_object* v_start_5739_; lean_object* v_stop_5740_; uint8_t v___x_5741_; 
v_array_5738_ = lean_ctor_get(v_snd_5721_, 0);
v_start_5739_ = lean_ctor_get(v_snd_5721_, 1);
v_stop_5740_ = lean_ctor_get(v_snd_5721_, 2);
v___x_5741_ = lean_nat_dec_lt(v_start_5739_, v_stop_5740_);
if (v___x_5741_ == 0)
{
lean_object* v___x_5743_; 
lean_dec(v_a_5710_);
if (v_isShared_5737_ == 0)
{
v___x_5743_ = v___x_5736_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v_fst_5734_);
lean_ctor_set(v_reuseFailAlloc_5753_, 1, v_snd_5721_);
v___x_5743_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
lean_object* v___x_5745_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5743_);
v___x_5745_ = v___x_5732_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_fst_5730_);
lean_ctor_set(v_reuseFailAlloc_5752_, 1, v___x_5743_);
v___x_5745_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
lean_object* v___x_5747_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5745_);
v___x_5747_ = v___x_5728_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v___x_5745_);
v___x_5747_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
lean_object* v___x_5749_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5747_);
v___x_5749_ = v___x_5724_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_fst_5722_);
lean_ctor_set(v_reuseFailAlloc_5750_, 1, v___x_5747_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
}
}
else
{
lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5824_; 
lean_inc(v_stop_5740_);
lean_inc(v_start_5739_);
lean_inc_ref(v_array_5738_);
v_isSharedCheck_5824_ = !lean_is_exclusive(v_snd_5721_);
if (v_isSharedCheck_5824_ == 0)
{
lean_object* v_unused_5825_; lean_object* v_unused_5826_; lean_object* v_unused_5827_; 
v_unused_5825_ = lean_ctor_get(v_snd_5721_, 2);
lean_dec(v_unused_5825_);
v_unused_5826_ = lean_ctor_get(v_snd_5721_, 1);
lean_dec(v_unused_5826_);
v_unused_5827_ = lean_ctor_get(v_snd_5721_, 0);
lean_dec(v_unused_5827_);
v___x_5755_ = v_snd_5721_;
v_isShared_5756_ = v_isSharedCheck_5824_;
goto v_resetjp_5754_;
}
else
{
lean_dec(v_snd_5721_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5824_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v_array_5757_; lean_object* v_start_5758_; lean_object* v_stop_5759_; lean_object* v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5764_; 
v_array_5757_ = lean_ctor_get(v_fst_5734_, 0);
v_start_5758_ = lean_ctor_get(v_fst_5734_, 1);
v_stop_5759_ = lean_ctor_get(v_fst_5734_, 2);
v___x_5760_ = lean_array_fget(v_array_5738_, v_start_5739_);
v___x_5761_ = lean_unsigned_to_nat(1u);
v___x_5762_ = lean_nat_add(v_start_5739_, v___x_5761_);
lean_dec(v_start_5739_);
if (v_isShared_5756_ == 0)
{
lean_ctor_set(v___x_5755_, 1, v___x_5762_);
v___x_5764_ = v___x_5755_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_array_5738_);
lean_ctor_set(v_reuseFailAlloc_5823_, 1, v___x_5762_);
lean_ctor_set(v_reuseFailAlloc_5823_, 2, v_stop_5740_);
v___x_5764_ = v_reuseFailAlloc_5823_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
uint8_t v___x_5765_; 
v___x_5765_ = lean_nat_dec_lt(v_start_5758_, v_stop_5759_);
if (v___x_5765_ == 0)
{
lean_object* v___x_5767_; 
lean_dec(v___x_5760_);
lean_dec(v_a_5710_);
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 1, v___x_5764_);
v___x_5767_ = v___x_5736_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_fst_5734_);
lean_ctor_set(v_reuseFailAlloc_5777_, 1, v___x_5764_);
v___x_5767_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
lean_object* v___x_5769_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5767_);
v___x_5769_ = v___x_5732_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_fst_5730_);
lean_ctor_set(v_reuseFailAlloc_5776_, 1, v___x_5767_);
v___x_5769_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
lean_object* v___x_5771_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5769_);
v___x_5771_ = v___x_5728_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5775_, 1, v___x_5769_);
v___x_5771_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
lean_object* v___x_5773_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5771_);
v___x_5773_ = v___x_5724_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_fst_5722_);
lean_ctor_set(v_reuseFailAlloc_5774_, 1, v___x_5771_);
v___x_5773_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
return v___x_5773_;
}
}
}
}
}
else
{
lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5819_; 
lean_inc(v_stop_5759_);
lean_inc(v_start_5758_);
lean_inc_ref(v_array_5757_);
v_isSharedCheck_5819_ = !lean_is_exclusive(v_fst_5734_);
if (v_isSharedCheck_5819_ == 0)
{
lean_object* v_unused_5820_; lean_object* v_unused_5821_; lean_object* v_unused_5822_; 
v_unused_5820_ = lean_ctor_get(v_fst_5734_, 2);
lean_dec(v_unused_5820_);
v_unused_5821_ = lean_ctor_get(v_fst_5734_, 1);
lean_dec(v_unused_5821_);
v_unused_5822_ = lean_ctor_get(v_fst_5734_, 0);
lean_dec(v_unused_5822_);
v___x_5779_ = v_fst_5734_;
v_isShared_5780_ = v_isSharedCheck_5819_;
goto v_resetjp_5778_;
}
else
{
lean_dec(v_fst_5734_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5819_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5784_; 
v___x_5781_ = lean_array_fget(v_array_5757_, v_start_5758_);
v___x_5782_ = lean_nat_add(v_start_5758_, v___x_5761_);
lean_dec(v_start_5758_);
if (v_isShared_5780_ == 0)
{
lean_ctor_set(v___x_5779_, 1, v___x_5782_);
v___x_5784_ = v___x_5779_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_array_5757_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v___x_5782_);
lean_ctor_set(v_reuseFailAlloc_5818_, 2, v_stop_5759_);
v___x_5784_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
uint8_t v___x_5785_; 
v___x_5785_ = lean_unbox(v___x_5781_);
lean_dec(v___x_5781_);
if (v___x_5785_ == 0)
{
lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5791_; 
v___x_5786_ = lean_array_get_size(v_fst_5730_);
v___x_5787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5787_, 0, v___x_5786_);
v___x_5788_ = lean_array_push(v_fst_5722_, v___x_5787_);
v___x_5789_ = lean_array_push(v_fst_5730_, v___x_5760_);
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 1, v___x_5764_);
lean_ctor_set(v___x_5736_, 0, v___x_5784_);
v___x_5791_ = v___x_5736_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5784_);
lean_ctor_set(v_reuseFailAlloc_5801_, 1, v___x_5764_);
v___x_5791_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
lean_object* v___x_5793_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5791_);
lean_ctor_set(v___x_5732_, 0, v___x_5789_);
v___x_5793_ = v___x_5732_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v___x_5789_);
lean_ctor_set(v_reuseFailAlloc_5800_, 1, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
lean_object* v___x_5795_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5793_);
v___x_5795_ = v___x_5728_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5799_, 1, v___x_5793_);
v___x_5795_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
lean_object* v___x_5797_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5795_);
lean_ctor_set(v___x_5724_, 0, v___x_5788_);
v___x_5797_ = v___x_5724_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v___x_5788_);
lean_ctor_set(v_reuseFailAlloc_5798_, 1, v___x_5795_);
v___x_5797_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
v_a_5713_ = v___x_5797_;
goto v___jp_5712_;
}
}
}
}
}
else
{
lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5807_; 
v___x_5802_ = lean_box(0);
v___x_5803_ = lean_array_push(v_fst_5722_, v___x_5802_);
v___x_5804_ = l_Lean_Expr_fvarId_x21(v___x_5760_);
lean_dec(v___x_5760_);
v___x_5805_ = lean_array_push(v_fst_5726_, v___x_5804_);
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 1, v___x_5764_);
lean_ctor_set(v___x_5736_, 0, v___x_5784_);
v___x_5807_ = v___x_5736_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v___x_5784_);
lean_ctor_set(v_reuseFailAlloc_5817_, 1, v___x_5764_);
v___x_5807_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
lean_object* v___x_5809_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5807_);
v___x_5809_ = v___x_5732_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_fst_5730_);
lean_ctor_set(v_reuseFailAlloc_5816_, 1, v___x_5807_);
v___x_5809_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
lean_object* v___x_5811_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5809_);
lean_ctor_set(v___x_5728_, 0, v___x_5805_);
v___x_5811_ = v___x_5728_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5815_; 
v_reuseFailAlloc_5815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5815_, 0, v___x_5805_);
lean_ctor_set(v_reuseFailAlloc_5815_, 1, v___x_5809_);
v___x_5811_ = v_reuseFailAlloc_5815_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
lean_object* v___x_5813_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5811_);
lean_ctor_set(v___x_5724_, 0, v___x_5803_);
v___x_5813_ = v___x_5724_;
goto v_reusejp_5812_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v___x_5803_);
lean_ctor_set(v_reuseFailAlloc_5814_, 1, v___x_5811_);
v___x_5813_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5812_;
}
v_reusejp_5812_:
{
v_a_5713_ = v___x_5813_;
goto v___jp_5712_;
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
v___jp_5712_:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; 
v___x_5714_ = lean_unsigned_to_nat(1u);
v___x_5715_ = lean_nat_add(v_a_5710_, v___x_5714_);
lean_dec(v_a_5710_);
v_a_5710_ = v___x_5715_;
v_b_5711_ = v_a_5713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5836_, lean_object* v_a_5837_, lean_object* v_b_5838_){
_start:
{
lean_object* v_res_5839_; 
v_res_5839_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5836_, v_a_5837_, v_b_5838_);
lean_dec(v_upperBound_5836_);
return v_res_5839_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5840_, size_t v_i_5841_, size_t v_stop_5842_){
_start:
{
uint8_t v___x_5843_; 
v___x_5843_ = lean_usize_dec_eq(v_i_5841_, v_stop_5842_);
if (v___x_5843_ == 0)
{
lean_object* v___x_5844_; uint8_t v___x_5845_; 
v___x_5844_ = lean_array_uget_borrowed(v_as_5840_, v_i_5841_);
v___x_5845_ = l_Lean_Expr_isFVar(v___x_5844_);
if (v___x_5845_ == 0)
{
uint8_t v___x_5846_; 
v___x_5846_ = 1;
return v___x_5846_;
}
else
{
size_t v___x_5847_; size_t v___x_5848_; 
v___x_5847_ = ((size_t)1ULL);
v___x_5848_ = lean_usize_add(v_i_5841_, v___x_5847_);
v_i_5841_ = v___x_5848_;
goto _start;
}
}
else
{
uint8_t v___x_5850_; 
v___x_5850_ = 0;
return v___x_5850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5851_, lean_object* v_i_5852_, lean_object* v_stop_5853_){
_start:
{
size_t v_i_boxed_5854_; size_t v_stop_boxed_5855_; uint8_t v_res_5856_; lean_object* v_r_5857_; 
v_i_boxed_5854_ = lean_unbox_usize(v_i_5852_);
lean_dec(v_i_5852_);
v_stop_boxed_5855_ = lean_unbox_usize(v_stop_5853_);
lean_dec(v_stop_5853_);
v_res_5856_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5851_, v_i_boxed_5854_, v_stop_boxed_5855_);
lean_dec_ref(v_as_5851_);
v_r_5857_ = lean_box(v_res_5856_);
return v_r_5857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5858_, size_t v_sz_5859_, size_t v_i_5860_, lean_object* v_bs_5861_){
_start:
{
uint8_t v___x_5862_; 
v___x_5862_ = lean_usize_dec_lt(v_i_5860_, v_sz_5859_);
if (v___x_5862_ == 0)
{
return v_bs_5861_;
}
else
{
lean_object* v_v_5863_; lean_object* v___x_5864_; lean_object* v_bs_x27_5865_; lean_object* v___y_5867_; 
v_v_5863_ = lean_array_uget(v_bs_5861_, v_i_5860_);
v___x_5864_ = lean_unsigned_to_nat(0u);
v_bs_x27_5865_ = lean_array_uset(v_bs_5861_, v_i_5860_, v___x_5864_);
if (lean_obj_tag(v_v_5863_) == 0)
{
v___y_5867_ = v_v_5863_;
goto v___jp_5866_;
}
else
{
lean_object* v_val_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; 
v_val_5872_ = lean_ctor_get(v_v_5863_, 0);
lean_inc(v_val_5872_);
lean_dec_ref_known(v_v_5863_, 1);
v___x_5873_ = lean_box(0);
v___x_5874_ = lean_array_get_borrowed(v___x_5873_, v___x_5858_, v_val_5872_);
lean_dec(v_val_5872_);
lean_inc(v___x_5874_);
v___y_5867_ = v___x_5874_;
goto v___jp_5866_;
}
v___jp_5866_:
{
size_t v___x_5868_; size_t v___x_5869_; lean_object* v___x_5870_; 
v___x_5868_ = ((size_t)1ULL);
v___x_5869_ = lean_usize_add(v_i_5860_, v___x_5868_);
v___x_5870_ = lean_array_uset(v_bs_x27_5865_, v_i_5860_, v___y_5867_);
v_i_5860_ = v___x_5869_;
v_bs_5861_ = v___x_5870_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5875_, lean_object* v_sz_5876_, lean_object* v_i_5877_, lean_object* v_bs_5878_){
_start:
{
size_t v_sz_boxed_5879_; size_t v_i_boxed_5880_; lean_object* v_res_5881_; 
v_sz_boxed_5879_ = lean_unbox_usize(v_sz_5876_);
lean_dec(v_sz_5876_);
v_i_boxed_5880_ = lean_unbox_usize(v_i_5877_);
lean_dec(v_i_5877_);
v_res_5881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5875_, v_sz_boxed_5879_, v_i_boxed_5880_, v_bs_5878_);
lean_dec_ref(v___x_5875_);
return v_res_5881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5882_, size_t v_sz_5883_, size_t v_i_5884_, lean_object* v_bs_5885_){
_start:
{
uint8_t v___x_5886_; 
v___x_5886_ = lean_usize_dec_lt(v_i_5884_, v_sz_5883_);
if (v___x_5886_ == 0)
{
return v_bs_5885_;
}
else
{
lean_object* v_v_5887_; lean_object* v___x_5888_; lean_object* v_bs_x27_5889_; size_t v_sz_5890_; size_t v___x_5891_; lean_object* v___x_5892_; size_t v___x_5893_; size_t v___x_5894_; lean_object* v___x_5895_; 
v_v_5887_ = lean_array_uget(v_bs_5885_, v_i_5884_);
v___x_5888_ = lean_unsigned_to_nat(0u);
v_bs_x27_5889_ = lean_array_uset(v_bs_5885_, v_i_5884_, v___x_5888_);
v_sz_5890_ = lean_array_size(v_v_5887_);
v___x_5891_ = ((size_t)0ULL);
v___x_5892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5882_, v_sz_5890_, v___x_5891_, v_v_5887_);
v___x_5893_ = ((size_t)1ULL);
v___x_5894_ = lean_usize_add(v_i_5884_, v___x_5893_);
v___x_5895_ = lean_array_uset(v_bs_x27_5889_, v_i_5884_, v___x_5892_);
v_i_5884_ = v___x_5894_;
v_bs_5885_ = v___x_5895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5897_, lean_object* v_sz_5898_, lean_object* v_i_5899_, lean_object* v_bs_5900_){
_start:
{
size_t v_sz_boxed_5901_; size_t v_i_boxed_5902_; lean_object* v_res_5903_; 
v_sz_boxed_5901_ = lean_unbox_usize(v_sz_5898_);
lean_dec(v_sz_5898_);
v_i_boxed_5902_ = lean_unbox_usize(v_i_5899_);
lean_dec(v_i_5899_);
v_res_5903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5897_, v_sz_boxed_5901_, v_i_boxed_5902_, v_bs_5900_);
lean_dec_ref(v___x_5897_);
return v_res_5903_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
v___x_5906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5907_ = lean_unsigned_to_nat(6u);
v___x_5908_ = lean_unsigned_to_nat(463u);
v___x_5909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5910_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5911_ = l_mkPanicMessageWithDecl(v___x_5910_, v___x_5909_, v___x_5908_, v___x_5907_, v___x_5906_);
return v___x_5911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5912_, lean_object* v___x_5913_, lean_object* v___x_5914_, lean_object* v_as_5915_, size_t v_sz_5916_, size_t v_i_5917_, lean_object* v_b_5918_){
_start:
{
lean_object* v_a_5920_; uint8_t v___x_5924_; 
v___x_5924_ = lean_usize_dec_lt(v_i_5917_, v_sz_5916_);
if (v___x_5924_ == 0)
{
return v_b_5918_;
}
else
{
lean_object* v_a_5925_; lean_object* v___x_5926_; uint8_t v___x_5927_; 
v_a_5925_ = lean_array_uget_borrowed(v_as_5915_, v_i_5917_);
v___x_5926_ = lean_array_get_size(v___x_5912_);
v___x_5927_ = lean_nat_dec_lt(v_a_5925_, v___x_5926_);
if (v___x_5927_ == 0)
{
lean_object* v___x_5928_; lean_object* v___x_5929_; 
lean_dec_ref(v_b_5918_);
v___x_5928_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5929_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5928_);
if (lean_obj_tag(v___x_5929_) == 0)
{
lean_object* v_a_5930_; 
v_a_5930_ = lean_ctor_get(v___x_5929_, 0);
lean_inc(v_a_5930_);
lean_dec_ref_known(v___x_5929_, 1);
return v_a_5930_;
}
else
{
lean_object* v_a_5931_; 
v_a_5931_ = lean_ctor_get(v___x_5929_, 0);
lean_inc(v_a_5931_);
lean_dec_ref_known(v___x_5929_, 1);
v_a_5920_ = v_a_5931_;
goto v___jp_5919_;
}
}
else
{
lean_object* v___x_5932_; lean_object* v___x_5933_; 
v___x_5932_ = lean_box(0);
v___x_5933_ = lean_array_get_borrowed(v___x_5932_, v___x_5912_, v_a_5925_);
if (lean_obj_tag(v___x_5933_) == 1)
{
lean_object* v_val_5934_; uint8_t v_changed_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; 
v_val_5934_ = lean_ctor_get(v___x_5933_, 0);
v_changed_5935_ = lean_nat_dec_eq(v___x_5913_, v___x_5914_);
v___x_5936_ = lean_box(v_changed_5935_);
v___x_5937_ = lean_array_set(v_b_5918_, v_val_5934_, v___x_5936_);
v_a_5920_ = v___x_5937_;
goto v___jp_5919_;
}
else
{
v_a_5920_ = v_b_5918_;
goto v___jp_5919_;
}
}
}
v___jp_5919_:
{
size_t v___x_5921_; size_t v___x_5922_; 
v___x_5921_ = ((size_t)1ULL);
v___x_5922_ = lean_usize_add(v_i_5917_, v___x_5921_);
v_i_5917_ = v___x_5922_;
v_b_5918_ = v_a_5920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5938_, lean_object* v___x_5939_, lean_object* v___x_5940_, lean_object* v_as_5941_, lean_object* v_sz_5942_, lean_object* v_i_5943_, lean_object* v_b_5944_){
_start:
{
size_t v_sz_boxed_5945_; size_t v_i_boxed_5946_; lean_object* v_res_5947_; 
v_sz_boxed_5945_ = lean_unbox_usize(v_sz_5942_);
lean_dec(v_sz_5942_);
v_i_boxed_5946_ = lean_unbox_usize(v_i_5943_);
lean_dec(v_i_5943_);
v_res_5947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5938_, v___x_5939_, v___x_5940_, v_as_5941_, v_sz_boxed_5945_, v_i_boxed_5946_, v_b_5944_);
lean_dec_ref(v_as_5941_);
lean_dec(v___x_5940_);
lean_dec(v___x_5939_);
lean_dec_ref(v___x_5938_);
return v_res_5947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5948_, lean_object* v___x_5949_, lean_object* v___x_5950_, lean_object* v_a_5951_, lean_object* v_b_5952_){
_start:
{
uint8_t v___x_5953_; 
v___x_5953_ = lean_nat_dec_lt(v_a_5951_, v_upperBound_5948_);
if (v___x_5953_ == 0)
{
lean_dec(v_a_5951_);
return v_b_5952_;
}
else
{
lean_object* v_snd_5954_; lean_object* v_snd_5955_; lean_object* v_fst_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_6022_; 
v_snd_5954_ = lean_ctor_get(v_b_5952_, 1);
lean_inc(v_snd_5954_);
v_snd_5955_ = lean_ctor_get(v_snd_5954_, 1);
lean_inc(v_snd_5955_);
v_fst_5956_ = lean_ctor_get(v_b_5952_, 0);
v_isSharedCheck_6022_ = !lean_is_exclusive(v_b_5952_);
if (v_isSharedCheck_6022_ == 0)
{
lean_object* v_unused_6023_; 
v_unused_6023_ = lean_ctor_get(v_b_5952_, 1);
lean_dec(v_unused_6023_);
v___x_5958_ = v_b_5952_;
v_isShared_5959_ = v_isSharedCheck_6022_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_fst_5956_);
lean_dec(v_b_5952_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_6022_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v_fst_5960_; lean_object* v___x_5962_; uint8_t v_isShared_5963_; uint8_t v_isSharedCheck_6020_; 
v_fst_5960_ = lean_ctor_get(v_snd_5954_, 0);
v_isSharedCheck_6020_ = !lean_is_exclusive(v_snd_5954_);
if (v_isSharedCheck_6020_ == 0)
{
lean_object* v_unused_6021_; 
v_unused_6021_ = lean_ctor_get(v_snd_5954_, 1);
lean_dec(v_unused_6021_);
v___x_5962_ = v_snd_5954_;
v_isShared_5963_ = v_isSharedCheck_6020_;
goto v_resetjp_5961_;
}
else
{
lean_inc(v_fst_5960_);
lean_dec(v_snd_5954_);
v___x_5962_ = lean_box(0);
v_isShared_5963_ = v_isSharedCheck_6020_;
goto v_resetjp_5961_;
}
v_resetjp_5961_:
{
lean_object* v_array_5964_; lean_object* v_start_5965_; lean_object* v_stop_5966_; uint8_t v___x_5967_; 
v_array_5964_ = lean_ctor_get(v_snd_5955_, 0);
v_start_5965_ = lean_ctor_get(v_snd_5955_, 1);
v_stop_5966_ = lean_ctor_get(v_snd_5955_, 2);
v___x_5967_ = lean_nat_dec_lt(v_start_5965_, v_stop_5966_);
if (v___x_5967_ == 0)
{
lean_object* v___x_5969_; 
lean_dec(v_a_5951_);
if (v_isShared_5963_ == 0)
{
v___x_5969_ = v___x_5962_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_fst_5960_);
lean_ctor_set(v_reuseFailAlloc_5973_, 1, v_snd_5955_);
v___x_5969_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
lean_object* v___x_5971_; 
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 1, v___x_5969_);
v___x_5971_ = v___x_5958_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_fst_5956_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___x_5969_);
v___x_5971_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
return v___x_5971_;
}
}
}
else
{
lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_6016_; 
lean_inc(v_stop_5966_);
lean_inc(v_start_5965_);
lean_inc_ref(v_array_5964_);
v_isSharedCheck_6016_ = !lean_is_exclusive(v_snd_5955_);
if (v_isSharedCheck_6016_ == 0)
{
lean_object* v_unused_6017_; lean_object* v_unused_6018_; lean_object* v_unused_6019_; 
v_unused_6017_ = lean_ctor_get(v_snd_5955_, 2);
lean_dec(v_unused_6017_);
v_unused_6018_ = lean_ctor_get(v_snd_5955_, 1);
lean_dec(v_unused_6018_);
v_unused_6019_ = lean_ctor_get(v_snd_5955_, 0);
lean_dec(v_unused_6019_);
v___x_5975_ = v_snd_5955_;
v_isShared_5976_ = v_isSharedCheck_6016_;
goto v_resetjp_5974_;
}
else
{
lean_dec(v_snd_5955_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_6016_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v_array_5977_; lean_object* v_start_5978_; lean_object* v_stop_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5984_; 
v_array_5977_ = lean_ctor_get(v_fst_5960_, 0);
v_start_5978_ = lean_ctor_get(v_fst_5960_, 1);
v_stop_5979_ = lean_ctor_get(v_fst_5960_, 2);
v___x_5980_ = lean_array_fget(v_array_5964_, v_start_5965_);
v___x_5981_ = lean_unsigned_to_nat(1u);
v___x_5982_ = lean_nat_add(v_start_5965_, v___x_5981_);
lean_dec(v_start_5965_);
if (v_isShared_5976_ == 0)
{
lean_ctor_set(v___x_5975_, 1, v___x_5982_);
v___x_5984_ = v___x_5975_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_array_5964_);
lean_ctor_set(v_reuseFailAlloc_6015_, 1, v___x_5982_);
lean_ctor_set(v_reuseFailAlloc_6015_, 2, v_stop_5966_);
v___x_5984_ = v_reuseFailAlloc_6015_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
uint8_t v___x_5985_; 
v___x_5985_ = lean_nat_dec_lt(v_start_5978_, v_stop_5979_);
if (v___x_5985_ == 0)
{
lean_object* v___x_5987_; 
lean_dec(v___x_5980_);
lean_dec(v_a_5951_);
if (v_isShared_5963_ == 0)
{
lean_ctor_set(v___x_5962_, 1, v___x_5984_);
v___x_5987_ = v___x_5962_;
goto v_reusejp_5986_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_fst_5960_);
lean_ctor_set(v_reuseFailAlloc_5991_, 1, v___x_5984_);
v___x_5987_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5986_;
}
v_reusejp_5986_:
{
lean_object* v___x_5989_; 
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 1, v___x_5987_);
v___x_5989_ = v___x_5958_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_fst_5956_);
lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5987_);
v___x_5989_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
return v___x_5989_;
}
}
}
else
{
lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_6011_; 
lean_inc(v_stop_5979_);
lean_inc(v_start_5978_);
lean_inc_ref(v_array_5977_);
v_isSharedCheck_6011_ = !lean_is_exclusive(v_fst_5960_);
if (v_isSharedCheck_6011_ == 0)
{
lean_object* v_unused_6012_; lean_object* v_unused_6013_; lean_object* v_unused_6014_; 
v_unused_6012_ = lean_ctor_get(v_fst_5960_, 2);
lean_dec(v_unused_6012_);
v_unused_6013_ = lean_ctor_get(v_fst_5960_, 1);
lean_dec(v_unused_6013_);
v_unused_6014_ = lean_ctor_get(v_fst_5960_, 0);
lean_dec(v_unused_6014_);
v___x_5993_ = v_fst_5960_;
v_isShared_5994_ = v_isSharedCheck_6011_;
goto v_resetjp_5992_;
}
else
{
lean_dec(v_fst_5960_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_6011_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5998_; 
v___x_5995_ = lean_array_fget(v_array_5977_, v_start_5978_);
v___x_5996_ = lean_nat_add(v_start_5978_, v___x_5981_);
lean_dec(v_start_5978_);
if (v_isShared_5994_ == 0)
{
lean_ctor_set(v___x_5993_, 1, v___x_5996_);
v___x_5998_ = v___x_5993_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_array_5977_);
lean_ctor_set(v_reuseFailAlloc_6010_, 1, v___x_5996_);
lean_ctor_set(v_reuseFailAlloc_6010_, 2, v_stop_5979_);
v___x_5998_ = v_reuseFailAlloc_6010_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
size_t v_sz_5999_; size_t v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6003_; 
v_sz_5999_ = lean_array_size(v___x_5995_);
v___x_6000_ = ((size_t)0ULL);
v___x_6001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5980_, v___x_5949_, v___x_5950_, v___x_5995_, v_sz_5999_, v___x_6000_, v_fst_5956_);
lean_dec(v___x_5995_);
lean_dec(v___x_5980_);
if (v_isShared_5963_ == 0)
{
lean_ctor_set(v___x_5962_, 1, v___x_5984_);
lean_ctor_set(v___x_5962_, 0, v___x_5998_);
v___x_6003_ = v___x_5962_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6009_; 
v_reuseFailAlloc_6009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6009_, 0, v___x_5998_);
lean_ctor_set(v_reuseFailAlloc_6009_, 1, v___x_5984_);
v___x_6003_ = v_reuseFailAlloc_6009_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
lean_object* v___x_6005_; 
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 1, v___x_6003_);
lean_ctor_set(v___x_5958_, 0, v___x_6001_);
v___x_6005_ = v___x_5958_;
goto v_reusejp_6004_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v___x_6001_);
lean_ctor_set(v_reuseFailAlloc_6008_, 1, v___x_6003_);
v___x_6005_ = v_reuseFailAlloc_6008_;
goto v_reusejp_6004_;
}
v_reusejp_6004_:
{
lean_object* v___x_6006_; 
v___x_6006_ = lean_nat_add(v_a_5951_, v___x_5981_);
lean_dec(v_a_5951_);
v_a_5951_ = v___x_6006_;
v_b_5952_ = v___x_6005_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6024_, lean_object* v___x_6025_, lean_object* v___x_6026_, lean_object* v_a_6027_, lean_object* v_b_6028_){
_start:
{
lean_object* v_res_6029_; 
v_res_6029_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6024_, v___x_6025_, v___x_6026_, v_a_6027_, v_b_6028_);
lean_dec(v___x_6026_);
lean_dec(v___x_6025_);
lean_dec(v_upperBound_6024_);
return v_res_6029_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; 
v___x_6031_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6032_ = lean_unsigned_to_nat(2u);
v___x_6033_ = lean_unsigned_to_nat(457u);
v___x_6034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6035_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6036_ = l_mkPanicMessageWithDecl(v___x_6035_, v___x_6034_, v___x_6033_, v___x_6032_, v___x_6031_);
return v___x_6036_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; 
v___x_6038_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6039_ = lean_unsigned_to_nat(2u);
v___x_6040_ = lean_unsigned_to_nat(458u);
v___x_6041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6042_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6043_ = l_mkPanicMessageWithDecl(v___x_6042_, v___x_6041_, v___x_6040_, v___x_6039_, v___x_6038_);
return v___x_6043_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; 
v___x_6045_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6046_ = lean_unsigned_to_nat(2u);
v___x_6047_ = lean_unsigned_to_nat(456u);
v___x_6048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6049_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6050_ = l_mkPanicMessageWithDecl(v___x_6049_, v___x_6048_, v___x_6047_, v___x_6046_, v___x_6045_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6051_, lean_object* v_xs_6052_, lean_object* v_toErase_6053_){
_start:
{
lean_object* v___x_6054_; lean_object* v___x_6055_; uint8_t v___x_6139_; 
v___x_6054_ = lean_unsigned_to_nat(0u);
v___x_6055_ = lean_array_get_size(v_xs_6052_);
v___x_6139_ = lean_nat_dec_lt(v___x_6054_, v___x_6055_);
if (v___x_6139_ == 0)
{
goto v___jp_6056_;
}
else
{
if (v___x_6139_ == 0)
{
goto v___jp_6056_;
}
else
{
size_t v___x_6140_; size_t v___x_6141_; uint8_t v___x_6142_; 
v___x_6140_ = ((size_t)0ULL);
v___x_6141_ = lean_usize_of_nat(v___x_6055_);
v___x_6142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6052_, v___x_6140_, v___x_6141_);
if (v___x_6142_ == 0)
{
goto v___jp_6056_;
}
else
{
lean_object* v___x_6143_; lean_object* v___x_6144_; 
lean_dec_ref(v_toErase_6053_);
lean_dec_ref(v_xs_6052_);
lean_dec_ref(v_fixedParamPerms_6051_);
v___x_6143_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6144_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6143_);
return v___x_6144_;
}
}
}
v___jp_6056_:
{
lean_object* v_numFixed_6057_; lean_object* v_perms_6058_; lean_object* v_revDeps_6059_; uint8_t v___x_6060_; 
v_numFixed_6057_ = lean_ctor_get(v_fixedParamPerms_6051_, 0);
v_perms_6058_ = lean_ctor_get(v_fixedParamPerms_6051_, 1);
lean_inc_ref(v_perms_6058_);
v_revDeps_6059_ = lean_ctor_get(v_fixedParamPerms_6051_, 2);
lean_inc_ref(v_revDeps_6059_);
v___x_6060_ = lean_nat_dec_eq(v_numFixed_6057_, v___x_6055_);
if (v___x_6060_ == 0)
{
lean_object* v___x_6061_; lean_object* v___x_6062_; 
lean_dec_ref(v_revDeps_6059_);
lean_dec_ref(v_perms_6058_);
lean_dec_ref(v_toErase_6053_);
lean_dec_ref(v_xs_6052_);
lean_dec_ref(v_fixedParamPerms_6051_);
v___x_6061_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6062_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6061_);
return v___x_6062_;
}
else
{
lean_object* v___x_6063_; lean_object* v___x_6064_; uint8_t v_changed_6065_; 
v___x_6063_ = lean_array_get_size(v_toErase_6053_);
v___x_6064_ = lean_array_get_size(v_perms_6058_);
v_changed_6065_ = lean_nat_dec_eq(v___x_6063_, v___x_6064_);
if (v_changed_6065_ == 0)
{
lean_object* v___x_6066_; lean_object* v___x_6067_; 
lean_dec_ref(v_revDeps_6059_);
lean_dec_ref(v_perms_6058_);
lean_dec_ref(v_toErase_6053_);
lean_dec_ref(v_xs_6052_);
lean_dec_ref(v_fixedParamPerms_6051_);
v___x_6066_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6067_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6066_);
return v___x_6067_;
}
else
{
uint8_t v_changed_6068_; lean_object* v___x_6069_; lean_object* v_mask_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v_fst_6076_; lean_object* v___x_6078_; uint8_t v_isShared_6079_; uint8_t v_isSharedCheck_6137_; 
v_changed_6068_ = 0;
v___x_6069_ = lean_box(v_changed_6068_);
lean_inc(v_numFixed_6057_);
v_mask_6070_ = lean_mk_array(v_numFixed_6057_, v___x_6069_);
v___x_6071_ = l_Array_toSubarray___redArg(v_toErase_6053_, v___x_6054_, v___x_6063_);
lean_inc_ref(v_perms_6058_);
v___x_6072_ = l_Array_toSubarray___redArg(v_perms_6058_, v___x_6054_, v___x_6064_);
v___x_6073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6071_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6074_, 0, v_mask_6070_);
lean_ctor_set(v___x_6074_, 1, v___x_6073_);
v___x_6075_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6063_, v___x_6063_, v___x_6064_, v___x_6054_, v___x_6074_);
v_fst_6076_ = lean_ctor_get(v___x_6075_, 0);
v_isSharedCheck_6137_ = !lean_is_exclusive(v___x_6075_);
if (v_isSharedCheck_6137_ == 0)
{
lean_object* v_unused_6138_; 
v_unused_6138_ = lean_ctor_get(v___x_6075_, 1);
lean_dec(v_unused_6138_);
v___x_6078_ = v___x_6075_;
v_isShared_6079_ = v_isSharedCheck_6137_;
goto v_resetjp_6077_;
}
else
{
lean_inc(v_fst_6076_);
lean_dec(v___x_6075_);
v___x_6078_ = lean_box(0);
v_isShared_6079_ = v_isSharedCheck_6137_;
goto v_resetjp_6077_;
}
v_resetjp_6077_:
{
lean_object* v___x_6080_; lean_object* v___x_6082_; 
v___x_6080_ = lean_box(v_changed_6065_);
if (v_isShared_6079_ == 0)
{
lean_ctor_set(v___x_6078_, 1, v___x_6080_);
v___x_6082_ = v___x_6078_;
goto v_reusejp_6081_;
}
else
{
lean_object* v_reuseFailAlloc_6136_; 
v_reuseFailAlloc_6136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6136_, 0, v_fst_6076_);
lean_ctor_set(v_reuseFailAlloc_6136_, 1, v___x_6080_);
v___x_6082_ = v_reuseFailAlloc_6136_;
goto v_reusejp_6081_;
}
v_reusejp_6081_:
{
lean_object* v___x_6083_; lean_object* v___x_6085_; uint8_t v_isShared_6086_; uint8_t v_isSharedCheck_6132_; 
v___x_6083_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6064_, v_perms_6058_, v___x_6063_, v_fixedParamPerms_6051_, v___x_6082_);
v_isSharedCheck_6132_ = !lean_is_exclusive(v_fixedParamPerms_6051_);
if (v_isSharedCheck_6132_ == 0)
{
lean_object* v_unused_6133_; lean_object* v_unused_6134_; lean_object* v_unused_6135_; 
v_unused_6133_ = lean_ctor_get(v_fixedParamPerms_6051_, 2);
lean_dec(v_unused_6133_);
v_unused_6134_ = lean_ctor_get(v_fixedParamPerms_6051_, 1);
lean_dec(v_unused_6134_);
v_unused_6135_ = lean_ctor_get(v_fixedParamPerms_6051_, 0);
lean_dec(v_unused_6135_);
v___x_6085_ = v_fixedParamPerms_6051_;
v_isShared_6086_ = v_isSharedCheck_6132_;
goto v_resetjp_6084_;
}
else
{
lean_dec(v_fixedParamPerms_6051_);
v___x_6085_ = lean_box(0);
v_isShared_6086_ = v_isSharedCheck_6132_;
goto v_resetjp_6084_;
}
v_resetjp_6084_:
{
lean_object* v_fst_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6130_; 
v_fst_6087_ = lean_ctor_get(v___x_6083_, 0);
v_isSharedCheck_6130_ = !lean_is_exclusive(v___x_6083_);
if (v_isSharedCheck_6130_ == 0)
{
lean_object* v_unused_6131_; 
v_unused_6131_ = lean_ctor_get(v___x_6083_, 1);
lean_dec(v_unused_6131_);
v___x_6089_ = v___x_6083_;
v_isShared_6090_ = v_isSharedCheck_6130_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_fst_6087_);
lean_dec(v___x_6083_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6130_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6096_; 
v___x_6091_ = lean_array_get_size(v_fst_6087_);
v___x_6092_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6093_ = l_Array_toSubarray___redArg(v_fst_6087_, v___x_6054_, v___x_6091_);
v___x_6094_ = l_Array_toSubarray___redArg(v_xs_6052_, v___x_6054_, v___x_6055_);
if (v_isShared_6090_ == 0)
{
lean_ctor_set(v___x_6089_, 1, v___x_6094_);
lean_ctor_set(v___x_6089_, 0, v___x_6093_);
v___x_6096_ = v___x_6089_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v___x_6093_);
lean_ctor_set(v_reuseFailAlloc_6129_, 1, v___x_6094_);
v___x_6096_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v_snd_6101_; lean_object* v_snd_6102_; lean_object* v_fst_6103_; lean_object* v_fst_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6127_; 
v___x_6097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6092_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6098_, 0, v___x_6092_);
lean_ctor_set(v___x_6098_, 1, v___x_6097_);
v___x_6099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6092_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
v___x_6100_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6091_, v___x_6054_, v___x_6099_);
v_snd_6101_ = lean_ctor_get(v___x_6100_, 1);
lean_inc(v_snd_6101_);
v_snd_6102_ = lean_ctor_get(v_snd_6101_, 1);
lean_inc(v_snd_6102_);
v_fst_6103_ = lean_ctor_get(v___x_6100_, 0);
lean_inc(v_fst_6103_);
lean_dec_ref(v___x_6100_);
v_fst_6104_ = lean_ctor_get(v_snd_6101_, 0);
v_isSharedCheck_6127_ = !lean_is_exclusive(v_snd_6101_);
if (v_isSharedCheck_6127_ == 0)
{
lean_object* v_unused_6128_; 
v_unused_6128_ = lean_ctor_get(v_snd_6101_, 1);
lean_dec(v_unused_6128_);
v___x_6106_ = v_snd_6101_;
v_isShared_6107_ = v_isSharedCheck_6127_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_fst_6104_);
lean_dec(v_snd_6101_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6127_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v_fst_6108_; lean_object* v___x_6110_; uint8_t v_isShared_6111_; uint8_t v_isSharedCheck_6125_; 
v_fst_6108_ = lean_ctor_get(v_snd_6102_, 0);
v_isSharedCheck_6125_ = !lean_is_exclusive(v_snd_6102_);
if (v_isSharedCheck_6125_ == 0)
{
lean_object* v_unused_6126_; 
v_unused_6126_ = lean_ctor_get(v_snd_6102_, 1);
lean_dec(v_unused_6126_);
v___x_6110_ = v_snd_6102_;
v_isShared_6111_ = v_isSharedCheck_6125_;
goto v_resetjp_6109_;
}
else
{
lean_inc(v_fst_6108_);
lean_dec(v_snd_6102_);
v___x_6110_ = lean_box(0);
v_isShared_6111_ = v_isSharedCheck_6125_;
goto v_resetjp_6109_;
}
v_resetjp_6109_:
{
lean_object* v___x_6112_; size_t v_sz_6113_; size_t v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6117_; 
v___x_6112_ = lean_array_get_size(v_fst_6108_);
v_sz_6113_ = lean_array_size(v_perms_6058_);
v___x_6114_ = ((size_t)0ULL);
v___x_6115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6103_, v_sz_6113_, v___x_6114_, v_perms_6058_);
lean_dec(v_fst_6103_);
if (v_isShared_6086_ == 0)
{
lean_ctor_set(v___x_6085_, 1, v___x_6115_);
lean_ctor_set(v___x_6085_, 0, v___x_6112_);
v___x_6117_ = v___x_6085_;
goto v_reusejp_6116_;
}
else
{
lean_object* v_reuseFailAlloc_6124_; 
v_reuseFailAlloc_6124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6124_, 0, v___x_6112_);
lean_ctor_set(v_reuseFailAlloc_6124_, 1, v___x_6115_);
lean_ctor_set(v_reuseFailAlloc_6124_, 2, v_revDeps_6059_);
v___x_6117_ = v_reuseFailAlloc_6124_;
goto v_reusejp_6116_;
}
v_reusejp_6116_:
{
lean_object* v___x_6119_; 
if (v_isShared_6111_ == 0)
{
lean_ctor_set(v___x_6110_, 1, v_fst_6104_);
v___x_6119_ = v___x_6110_;
goto v_reusejp_6118_;
}
else
{
lean_object* v_reuseFailAlloc_6123_; 
v_reuseFailAlloc_6123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6123_, 0, v_fst_6108_);
lean_ctor_set(v_reuseFailAlloc_6123_, 1, v_fst_6104_);
v___x_6119_ = v_reuseFailAlloc_6123_;
goto v_reusejp_6118_;
}
v_reusejp_6118_:
{
lean_object* v___x_6121_; 
if (v_isShared_6107_ == 0)
{
lean_ctor_set(v___x_6106_, 1, v___x_6119_);
lean_ctor_set(v___x_6106_, 0, v___x_6117_);
v___x_6121_ = v___x_6106_;
goto v_reusejp_6120_;
}
else
{
lean_object* v_reuseFailAlloc_6122_; 
v_reuseFailAlloc_6122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6122_, 0, v___x_6117_);
lean_ctor_set(v_reuseFailAlloc_6122_, 1, v___x_6119_);
v___x_6121_ = v_reuseFailAlloc_6122_;
goto v_reusejp_6120_;
}
v_reusejp_6120_:
{
return v___x_6121_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6145_, lean_object* v___x_6146_, lean_object* v___x_6147_, lean_object* v___x_6148_, lean_object* v_fixedParamPerms_6149_, lean_object* v_next_6150_, lean_object* v_inst_6151_, lean_object* v_R_6152_, lean_object* v_a_6153_, lean_object* v_b_6154_, lean_object* v_c_6155_){
_start:
{
lean_object* v___x_6156_; 
v___x_6156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6145_, v___x_6146_, v___x_6147_, v___x_6148_, v_fixedParamPerms_6149_, v_next_6150_, v_a_6153_, v_b_6154_);
return v___x_6156_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6157_, lean_object* v___x_6158_, lean_object* v___x_6159_, lean_object* v___x_6160_, lean_object* v_fixedParamPerms_6161_, lean_object* v_next_6162_, lean_object* v_inst_6163_, lean_object* v_R_6164_, lean_object* v_a_6165_, lean_object* v_b_6166_, lean_object* v_c_6167_){
_start:
{
lean_object* v_res_6168_; 
v_res_6168_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6157_, v___x_6158_, v___x_6159_, v___x_6160_, v_fixedParamPerms_6161_, v_next_6162_, v_inst_6163_, v_R_6164_, v_a_6165_, v_b_6166_, v_c_6167_);
lean_dec(v_a_6165_);
lean_dec(v_next_6162_);
lean_dec_ref(v_fixedParamPerms_6161_);
lean_dec(v___x_6160_);
lean_dec(v___x_6159_);
lean_dec_ref(v___x_6158_);
lean_dec(v_upperBound_6157_);
return v_res_6168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6169_, lean_object* v___x_6170_, lean_object* v___x_6171_, lean_object* v___x_6172_, lean_object* v_fixedParamPerms_6173_, lean_object* v_inst_6174_, lean_object* v_R_6175_, lean_object* v_a_6176_, lean_object* v_b_6177_, lean_object* v_c_6178_){
_start:
{
lean_object* v___x_6179_; 
v___x_6179_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6169_, v___x_6170_, v___x_6171_, v___x_6172_, v_fixedParamPerms_6173_, v_a_6176_, v_b_6177_);
return v___x_6179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6180_, lean_object* v___x_6181_, lean_object* v___x_6182_, lean_object* v___x_6183_, lean_object* v_fixedParamPerms_6184_, lean_object* v_inst_6185_, lean_object* v_R_6186_, lean_object* v_a_6187_, lean_object* v_b_6188_, lean_object* v_c_6189_){
_start:
{
lean_object* v_res_6190_; 
v_res_6190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6180_, v___x_6181_, v___x_6182_, v___x_6183_, v_fixedParamPerms_6184_, v_inst_6185_, v_R_6186_, v_a_6187_, v_b_6188_, v_c_6189_);
lean_dec_ref(v_fixedParamPerms_6184_);
lean_dec(v___x_6183_);
lean_dec(v___x_6182_);
lean_dec_ref(v___x_6181_);
lean_dec(v_upperBound_6180_);
return v_res_6190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6191_, lean_object* v___x_6192_, lean_object* v___x_6193_, lean_object* v_fixedParamPerms_6194_, lean_object* v_inst_6195_, lean_object* v_a_6196_){
_start:
{
lean_object* v___x_6197_; 
v___x_6197_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6191_, v___x_6192_, v___x_6193_, v_fixedParamPerms_6194_, v_a_6196_);
return v___x_6197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6198_, lean_object* v___x_6199_, lean_object* v___x_6200_, lean_object* v_fixedParamPerms_6201_, lean_object* v_inst_6202_, lean_object* v_a_6203_){
_start:
{
lean_object* v_res_6204_; 
v_res_6204_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6198_, v___x_6199_, v___x_6200_, v_fixedParamPerms_6201_, v_inst_6202_, v_a_6203_);
lean_dec_ref(v_fixedParamPerms_6201_);
lean_dec(v___x_6200_);
lean_dec_ref(v___x_6199_);
lean_dec(v___x_6198_);
return v_res_6204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6205_, lean_object* v_inst_6206_, lean_object* v_R_6207_, lean_object* v_a_6208_, lean_object* v_b_6209_, lean_object* v_c_6210_){
_start:
{
lean_object* v___x_6211_; 
v___x_6211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6205_, v_a_6208_, v_b_6209_);
return v___x_6211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6212_, lean_object* v_inst_6213_, lean_object* v_R_6214_, lean_object* v_a_6215_, lean_object* v_b_6216_, lean_object* v_c_6217_){
_start:
{
lean_object* v_res_6218_; 
v_res_6218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6212_, v_inst_6213_, v_R_6214_, v_a_6215_, v_b_6216_, v_c_6217_);
lean_dec(v_upperBound_6212_);
return v_res_6218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6219_, lean_object* v___x_6220_, lean_object* v___x_6221_, lean_object* v_inst_6222_, lean_object* v_R_6223_, lean_object* v_a_6224_, lean_object* v_b_6225_, lean_object* v_c_6226_){
_start:
{
lean_object* v___x_6227_; 
v___x_6227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6219_, v___x_6220_, v___x_6221_, v_a_6224_, v_b_6225_);
return v___x_6227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6228_, lean_object* v___x_6229_, lean_object* v___x_6230_, lean_object* v_inst_6231_, lean_object* v_R_6232_, lean_object* v_a_6233_, lean_object* v_b_6234_, lean_object* v_c_6235_){
_start:
{
lean_object* v_res_6236_; 
v_res_6236_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6228_, v___x_6229_, v___x_6230_, v_inst_6231_, v_R_6232_, v_a_6233_, v_b_6234_, v_c_6235_);
lean_dec(v___x_6230_);
lean_dec(v___x_6229_);
lean_dec(v_upperBound_6228_);
return v_res_6236_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object* v_upperBound_6237_, lean_object* v___x_6238_, lean_object* v_fixedParamPerms_6239_, lean_object* v_next_6240_, lean_object* v___x_6241_, lean_object* v___x_6242_, lean_object* v_inst_6243_, lean_object* v_R_6244_, lean_object* v_a_6245_, lean_object* v_b_6246_, lean_object* v_c_6247_){
_start:
{
lean_object* v___x_6248_; 
v___x_6248_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_6237_, v___x_6238_, v_fixedParamPerms_6239_, v_next_6240_, v___x_6241_, v___x_6242_, v_a_6245_, v_b_6246_);
return v___x_6248_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object* v_upperBound_6249_, lean_object* v___x_6250_, lean_object* v_fixedParamPerms_6251_, lean_object* v_next_6252_, lean_object* v___x_6253_, lean_object* v___x_6254_, lean_object* v_inst_6255_, lean_object* v_R_6256_, lean_object* v_a_6257_, lean_object* v_b_6258_, lean_object* v_c_6259_){
_start:
{
lean_object* v_res_6260_; 
v_res_6260_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(v_upperBound_6249_, v___x_6250_, v_fixedParamPerms_6251_, v_next_6252_, v___x_6253_, v___x_6254_, v_inst_6255_, v_R_6256_, v_a_6257_, v_b_6258_, v_c_6259_);
lean_dec(v___x_6254_);
lean_dec(v___x_6253_);
lean_dec(v_next_6252_);
lean_dec_ref(v_fixedParamPerms_6251_);
lean_dec_ref(v___x_6250_);
lean_dec(v_upperBound_6249_);
return v_res_6260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6318_; uint8_t v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; 
v___x_6318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6319_ = 0;
v___x_6320_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6321_ = l_Lean_registerTraceClass(v___x_6318_, v___x_6319_, v___x_6320_);
return v___x_6321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6322_){
_start:
{
lean_object* v_res_6323_; 
v_res_6323_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6323_;
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
