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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_1008_; lean_object* v___x_27266__overap_1009_; lean_object* v___x_1010_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_27266__overap_1009_ = lean_panic_fn_borrowed(v___f_1008_, v_msg_1002_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1010_ = lean_apply_5(v___x_27266__overap_1009_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, lean_box(0));
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
lean_object* v___y_1473_; lean_object* v_toCold_1482_; lean_object* v_currRecDepth_1483_; lean_object* v_ref_1484_; uint16_t v_optionFlags_1485_; uint8_t v_suppressElabErrors_1486_; uint8_t v_checkDeprecated_1487_; uint8_t v_isRecordingDeps_1488_; lean_object* v_maxRecDepth_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_toCold_1482_ = lean_ctor_get(v___y_1469_, 0);
v_currRecDepth_1483_ = lean_ctor_get(v___y_1469_, 1);
v_ref_1484_ = lean_ctor_get(v___y_1469_, 2);
v_optionFlags_1485_ = lean_ctor_get_uint16(v___y_1469_, sizeof(void*)*3);
v_suppressElabErrors_1486_ = lean_ctor_get_uint8(v___y_1469_, sizeof(void*)*3 + 2);
v_checkDeprecated_1487_ = lean_ctor_get_uint8(v___y_1469_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1488_ = lean_ctor_get_uint8(v___y_1469_, sizeof(void*)*3 + 4);
v_maxRecDepth_1494_ = lean_ctor_get(v_toCold_1482_, 3);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_nat_dec_eq(v_maxRecDepth_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_nat_dec_eq(v_currRecDepth_1483_, v_maxRecDepth_1494_);
if (v___x_1497_ == 0)
{
goto v___jp_1489_;
}
else
{
lean_object* v___x_1498_; 
lean_dec_ref(v_x_1465_);
lean_inc(v_ref_1484_);
v___x_1498_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1484_);
v___y_1473_ = v___x_1498_;
goto v___jp_1472_;
}
}
else
{
goto v___jp_1489_;
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
v___jp_1489_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_add(v_currRecDepth_1483_, v___x_1490_);
lean_inc(v_ref_1484_);
lean_inc_ref(v_toCold_1482_);
v___x_1492_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1492_, 0, v_toCold_1482_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
lean_ctor_set(v___x_1492_, 2, v_ref_1484_);
lean_ctor_set_uint16(v___x_1492_, sizeof(void*)*3, v_optionFlags_1485_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*3 + 2, v_suppressElabErrors_1486_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*3 + 3, v_checkDeprecated_1487_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*3 + 4, v_isRecordingDeps_1488_);
lean_inc(v___y_1470_);
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
v___x_1493_ = lean_apply_6(v_x_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___x_1492_, v___y_1470_, lean_box(0));
v___y_1473_ = v___x_1493_;
goto v___jp_1472_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_1540_, lean_object* v_pre_1541_, lean_object* v_post_1542_, lean_object* v_usedLetOnly_1543_, lean_object* v_skipConstInApp_1544_, lean_object* v_skipInstances_1545_, lean_object* v_body_1546_, lean_object* v_x_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v_usedLetOnly_boxed_1554_; uint8_t v_skipConstInApp_boxed_1555_; uint8_t v_skipInstances_boxed_1556_; lean_object* v_res_1557_; 
v_usedLetOnly_boxed_1554_ = lean_unbox(v_usedLetOnly_1543_);
v_skipConstInApp_boxed_1555_ = lean_unbox(v_skipConstInApp_1544_);
v_skipInstances_boxed_1556_ = lean_unbox(v_skipInstances_1545_);
v_res_1557_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_1540_, v_pre_1541_, v_post_1542_, v_usedLetOnly_boxed_1554_, v_skipConstInApp_boxed_1555_, v_skipInstances_boxed_1556_, v_body_1546_, v_x_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1561_, lean_object* v_pre_1562_, lean_object* v_post_1563_, uint8_t v_usedLetOnly_1564_, uint8_t v_skipConstInApp_1565_, uint8_t v_skipInstances_1566_, lean_object* v_body_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_array_push(v_fvars_1561_, v_x_1568_);
v___x_1576_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1562_, v_post_1563_, v_usedLetOnly_1564_, v_skipConstInApp_1565_, v_skipInstances_1566_, v___x_1575_, v_body_1567_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1577_, lean_object* v_pre_1578_, lean_object* v_post_1579_, lean_object* v_usedLetOnly_1580_, lean_object* v_skipConstInApp_1581_, lean_object* v_skipInstances_1582_, lean_object* v_body_1583_, lean_object* v_x_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v_usedLetOnly_boxed_1591_; uint8_t v_skipConstInApp_boxed_1592_; uint8_t v_skipInstances_boxed_1593_; lean_object* v_res_1594_; 
v_usedLetOnly_boxed_1591_ = lean_unbox(v_usedLetOnly_1580_);
v_skipConstInApp_boxed_1592_ = lean_unbox(v_skipConstInApp_1581_);
v_skipInstances_boxed_1593_ = lean_unbox(v_skipInstances_1582_);
v_res_1594_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1577_, v_pre_1578_, v_post_1579_, v_usedLetOnly_boxed_1591_, v_skipConstInApp_boxed_1592_, v_skipInstances_boxed_1593_, v_body_1583_, v_x_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1595_, lean_object* v_post_1596_, uint8_t v_usedLetOnly_1597_, uint8_t v_skipConstInApp_1598_, uint8_t v_skipInstances_1599_, lean_object* v_e_1600_, lean_object* v_a_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; 
lean_inc_ref(v_post_1596_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
lean_inc(v___y_1603_);
lean_inc_ref(v___y_1602_);
lean_inc_ref(v_e_1600_);
v___x_1607_ = lean_apply_6(v_post_1596_, v_e_1600_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, lean_box(0));
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1626_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1626_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1626_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
switch(lean_obj_tag(v_a_1608_))
{
case 0:
{
lean_object* v_e_1612_; lean_object* v___x_1614_; 
lean_dec_ref(v_e_1600_);
lean_dec_ref(v_post_1596_);
lean_dec_ref(v_pre_1595_);
v_e_1612_ = lean_ctor_get(v_a_1608_, 0);
lean_inc_ref(v_e_1612_);
lean_dec_ref_known(v_a_1608_, 1);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_e_1612_);
v___x_1614_ = v___x_1610_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_e_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
case 1:
{
lean_object* v_e_1616_; lean_object* v___x_1617_; 
lean_del_object(v___x_1610_);
lean_dec_ref(v_e_1600_);
v_e_1616_ = lean_ctor_get(v_a_1608_, 0);
lean_inc_ref(v_e_1616_);
lean_dec_ref_known(v_a_1608_, 1);
v___x_1617_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1595_, v_post_1596_, v_usedLetOnly_1597_, v_skipConstInApp_1598_, v_skipInstances_1599_, v_e_1616_, v_a_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
return v___x_1617_;
}
default: 
{
lean_object* v_e_x3f_1618_; 
lean_dec_ref(v_post_1596_);
lean_dec_ref(v_pre_1595_);
v_e_x3f_1618_ = lean_ctor_get(v_a_1608_, 0);
lean_inc(v_e_x3f_1618_);
lean_dec_ref_known(v_a_1608_, 1);
if (lean_obj_tag(v_e_x3f_1618_) == 0)
{
lean_object* v___x_1620_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_e_1600_);
v___x_1620_ = v___x_1610_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_e_1600_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
else
{
lean_object* v_val_1622_; lean_object* v___x_1624_; 
lean_dec_ref(v_e_1600_);
v_val_1622_ = lean_ctor_get(v_e_x3f_1618_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v_e_x3f_1618_, 1);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v_val_1622_);
v___x_1624_ = v___x_1610_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_val_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v_e_1600_);
lean_dec_ref(v_post_1596_);
lean_dec_ref(v_pre_1595_);
v_a_1627_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1607_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1607_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1635_, lean_object* v_post_1636_, uint8_t v_usedLetOnly_1637_, uint8_t v_skipConstInApp_1638_, uint8_t v_skipInstances_1639_, lean_object* v_fvars_1640_, lean_object* v_e_1641_, lean_object* v_a_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
if (lean_obj_tag(v_e_1641_) == 6)
{
lean_object* v_binderName_1648_; lean_object* v_binderType_1649_; lean_object* v_body_1650_; uint8_t v_binderInfo_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___f_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_binderName_1648_ = lean_ctor_get(v_e_1641_, 0);
lean_inc(v_binderName_1648_);
v_binderType_1649_ = lean_ctor_get(v_e_1641_, 1);
lean_inc_ref(v_binderType_1649_);
v_body_1650_ = lean_ctor_get(v_e_1641_, 2);
lean_inc_ref(v_body_1650_);
v_binderInfo_1651_ = lean_ctor_get_uint8(v_e_1641_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1641_, 3);
v___x_1652_ = lean_box(v_usedLetOnly_1637_);
v___x_1653_ = lean_box(v_skipConstInApp_1638_);
v___x_1654_ = lean_box(v_skipInstances_1639_);
lean_inc_ref(v_post_1636_);
lean_inc_ref(v_pre_1635_);
lean_inc_ref(v_fvars_1640_);
v___f_1655_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1655_, 0, v_fvars_1640_);
lean_closure_set(v___f_1655_, 1, v_pre_1635_);
lean_closure_set(v___f_1655_, 2, v_post_1636_);
lean_closure_set(v___f_1655_, 3, v___x_1652_);
lean_closure_set(v___f_1655_, 4, v___x_1653_);
lean_closure_set(v___f_1655_, 5, v___x_1654_);
lean_closure_set(v___f_1655_, 6, v_body_1650_);
v___x_1656_ = lean_expr_instantiate_rev(v_binderType_1649_, v_fvars_1640_);
lean_dec_ref(v_fvars_1640_);
lean_dec_ref(v_binderType_1649_);
v___x_1657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1635_, v_post_1636_, v_usedLetOnly_1637_, v_skipConstInApp_1638_, v_skipInstances_1639_, v___x_1656_, v_a_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = 0;
v___x_1660_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1648_, v_binderInfo_1651_, v_a_1658_, v___f_1655_, v___x_1659_, v_a_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v___x_1660_;
}
else
{
lean_dec_ref(v___f_1655_);
lean_dec(v_binderName_1648_);
return v___x_1657_;
}
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_expr_instantiate_rev(v_e_1641_, v_fvars_1640_);
lean_dec_ref(v_e_1641_);
lean_inc_ref(v_post_1636_);
lean_inc_ref(v_pre_1635_);
v___x_1662_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1635_, v_post_1636_, v_usedLetOnly_1637_, v_skipConstInApp_1638_, v_skipInstances_1639_, v___x_1661_, v_a_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; uint8_t v___x_1664_; uint8_t v___x_1665_; uint8_t v___x_1666_; lean_object* v___x_1667_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v___x_1664_ = 0;
v___x_1665_ = 1;
v___x_1666_ = 1;
v___x_1667_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1640_, v_a_1663_, v___x_1664_, v_usedLetOnly_1637_, v___x_1664_, v___x_1665_, v___x_1666_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec_ref(v_fvars_1640_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1635_, v_post_1636_, v_usedLetOnly_1637_, v_skipConstInApp_1638_, v_skipInstances_1639_, v_a_1668_, v_a_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
return v___x_1669_;
}
else
{
lean_dec_ref(v_post_1636_);
lean_dec_ref(v_pre_1635_);
return v___x_1667_;
}
}
else
{
lean_dec_ref(v_fvars_1640_);
lean_dec_ref(v_post_1636_);
lean_dec_ref(v_pre_1635_);
return v___x_1662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1670_, lean_object* v_pre_1671_, lean_object* v_post_1672_, uint8_t v_usedLetOnly_1673_, uint8_t v_skipConstInApp_1674_, uint8_t v_skipInstances_1675_, lean_object* v_body_1676_, lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_array_push(v_fvars_1670_, v_x_1677_);
v___x_1685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1671_, v_post_1672_, v_usedLetOnly_1673_, v_skipConstInApp_1674_, v_skipInstances_1675_, v___x_1684_, v_body_1676_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1686_, lean_object* v_pre_1687_, lean_object* v_post_1688_, lean_object* v_usedLetOnly_1689_, lean_object* v_skipConstInApp_1690_, lean_object* v_skipInstances_1691_, lean_object* v_body_1692_, lean_object* v_x_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v_usedLetOnly_boxed_1700_; uint8_t v_skipConstInApp_boxed_1701_; uint8_t v_skipInstances_boxed_1702_; lean_object* v_res_1703_; 
v_usedLetOnly_boxed_1700_ = lean_unbox(v_usedLetOnly_1689_);
v_skipConstInApp_boxed_1701_ = lean_unbox(v_skipConstInApp_1690_);
v_skipInstances_boxed_1702_ = lean_unbox(v_skipInstances_1691_);
v_res_1703_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1686_, v_pre_1687_, v_post_1688_, v_usedLetOnly_boxed_1700_, v_skipConstInApp_boxed_1701_, v_skipInstances_boxed_1702_, v_body_1692_, v_x_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1704_, lean_object* v_post_1705_, uint8_t v_usedLetOnly_1706_, uint8_t v_skipConstInApp_1707_, uint8_t v_skipInstances_1708_, lean_object* v_fvars_1709_, lean_object* v_e_1710_, lean_object* v_a_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
if (lean_obj_tag(v_e_1710_) == 8)
{
lean_object* v_declName_1717_; lean_object* v_type_1718_; lean_object* v_value_1719_; lean_object* v_body_1720_; uint8_t v_nondep_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___f_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_declName_1717_ = lean_ctor_get(v_e_1710_, 0);
lean_inc(v_declName_1717_);
v_type_1718_ = lean_ctor_get(v_e_1710_, 1);
lean_inc_ref(v_type_1718_);
v_value_1719_ = lean_ctor_get(v_e_1710_, 2);
lean_inc_ref(v_value_1719_);
v_body_1720_ = lean_ctor_get(v_e_1710_, 3);
lean_inc_ref(v_body_1720_);
v_nondep_1721_ = lean_ctor_get_uint8(v_e_1710_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1710_, 4);
v___x_1722_ = lean_box(v_usedLetOnly_1706_);
v___x_1723_ = lean_box(v_skipConstInApp_1707_);
v___x_1724_ = lean_box(v_skipInstances_1708_);
lean_inc_ref_n(v_post_1705_, 2);
lean_inc_ref_n(v_pre_1704_, 2);
lean_inc_ref(v_fvars_1709_);
v___f_1725_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1725_, 0, v_fvars_1709_);
lean_closure_set(v___f_1725_, 1, v_pre_1704_);
lean_closure_set(v___f_1725_, 2, v_post_1705_);
lean_closure_set(v___f_1725_, 3, v___x_1722_);
lean_closure_set(v___f_1725_, 4, v___x_1723_);
lean_closure_set(v___f_1725_, 5, v___x_1724_);
lean_closure_set(v___f_1725_, 6, v_body_1720_);
v___x_1726_ = lean_expr_instantiate_rev(v_type_1718_, v_fvars_1709_);
lean_dec_ref(v_type_1718_);
v___x_1727_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1704_, v_post_1705_, v_usedLetOnly_1706_, v_skipConstInApp_1707_, v_skipInstances_1708_, v___x_1726_, v_a_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = lean_expr_instantiate_rev(v_value_1719_, v_fvars_1709_);
lean_dec_ref(v_fvars_1709_);
lean_dec_ref(v_value_1719_);
v___x_1730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1704_, v_post_1705_, v_usedLetOnly_1706_, v_skipConstInApp_1707_, v_skipInstances_1708_, v___x_1729_, v_a_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = 0;
v___x_1733_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1717_, v_a_1728_, v_a_1731_, v___f_1725_, v_nondep_1721_, v___x_1732_, v_a_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1733_;
}
else
{
lean_dec(v_a_1728_);
lean_dec_ref(v___f_1725_);
lean_dec(v_declName_1717_);
return v___x_1730_;
}
}
else
{
lean_dec_ref(v___f_1725_);
lean_dec_ref(v_value_1719_);
lean_dec(v_declName_1717_);
lean_dec_ref(v_fvars_1709_);
lean_dec_ref(v_post_1705_);
lean_dec_ref(v_pre_1704_);
return v___x_1727_;
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_expr_instantiate_rev(v_e_1710_, v_fvars_1709_);
lean_dec_ref(v_e_1710_);
lean_inc_ref(v_post_1705_);
lean_inc_ref(v_pre_1704_);
v___x_1735_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1704_, v_post_1705_, v_usedLetOnly_1706_, v_skipConstInApp_1707_, v_skipInstances_1708_, v___x_1734_, v_a_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; uint8_t v___x_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = 0;
v___x_1738_ = 1;
v___x_1739_ = l_Lean_Meta_mkLetFVars(v_fvars_1709_, v_a_1736_, v_usedLetOnly_1706_, v___x_1737_, v___x_1738_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec_ref(v_fvars_1709_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1704_, v_post_1705_, v_usedLetOnly_1706_, v_skipConstInApp_1707_, v_skipInstances_1708_, v_a_1740_, v_a_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1741_;
}
else
{
lean_dec_ref(v_post_1705_);
lean_dec_ref(v_pre_1704_);
return v___x_1739_;
}
}
else
{
lean_dec_ref(v_fvars_1709_);
lean_dec_ref(v_post_1705_);
lean_dec_ref(v_pre_1704_);
return v___x_1735_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1742_; lean_object* v_dummy_1743_; 
v___x_1742_ = lean_box(0);
v_dummy_1743_ = l_Lean_Expr_sort___override(v___x_1742_);
return v_dummy_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1744_, lean_object* v_post_1745_, uint8_t v_usedLetOnly_1746_, uint8_t v_skipConstInApp_1747_, uint8_t v_skipInstances_1748_, size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_bs_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_lt(v_i_1750_, v_sz_1749_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
lean_dec_ref(v_post_1745_);
lean_dec_ref(v_pre_1744_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_bs_1751_);
return v___x_1759_;
}
else
{
lean_object* v_v_1760_; lean_object* v___x_1761_; lean_object* v_bs_x27_1762_; lean_object* v___x_1763_; 
v_v_1760_ = lean_array_uget(v_bs_1751_, v_i_1750_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v_bs_x27_1762_ = lean_array_uset(v_bs_1751_, v_i_1750_, v___x_1761_);
lean_inc_ref(v_post_1745_);
lean_inc_ref(v_pre_1744_);
v___x_1763_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1744_, v_post_1745_, v_usedLetOnly_1746_, v_skipConstInApp_1747_, v_skipInstances_1748_, v_v_1760_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_add(v_i_1750_, v___x_1765_);
v___x_1767_ = lean_array_uset(v_bs_x27_1762_, v_i_1750_, v_a_1764_);
v_i_1750_ = v___x_1766_;
v_bs_1751_ = v___x_1767_;
goto _start;
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_bs_x27_1762_);
lean_dec_ref(v_post_1745_);
lean_dec_ref(v_pre_1744_);
v_a_1769_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1763_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1763_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1777_, lean_object* v_post_1778_, uint8_t v_usedLetOnly_1779_, uint8_t v_skipConstInApp_1780_, uint8_t v_skipInstances_1781_, lean_object* v___x_1782_, lean_object* v___y_1783_, lean_object* v_b_1784_, lean_object* v_a_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1777_, v_post_1778_, v_usedLetOnly_1779_, v_skipConstInApp_1780_, v_skipInstances_1781_, v___x_1782_, v___y_1783_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1801_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1801_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1801_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
v___x_1796_ = lean_array_fset(v_b_1784_, v_a_1785_, v_a_1792_);
v___x_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1797_);
v___x_1799_ = v___x_1794_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec_ref(v_b_1784_);
v_a_1802_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1791_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1791_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1810_, lean_object* v_post_1811_, lean_object* v_usedLetOnly_1812_, lean_object* v_skipConstInApp_1813_, lean_object* v_skipInstances_1814_, lean_object* v___x_1815_, lean_object* v___y_1816_, lean_object* v_b_1817_, lean_object* v_a_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v_usedLetOnly_boxed_1824_; uint8_t v_skipConstInApp_boxed_1825_; uint8_t v_skipInstances_boxed_1826_; lean_object* v_res_1827_; 
v_usedLetOnly_boxed_1824_ = lean_unbox(v_usedLetOnly_1812_);
v_skipConstInApp_boxed_1825_ = lean_unbox(v_skipConstInApp_1813_);
v_skipInstances_boxed_1826_ = lean_unbox(v_skipInstances_1814_);
v_res_1827_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1810_, v_post_1811_, v_usedLetOnly_boxed_1824_, v_skipConstInApp_boxed_1825_, v_skipInstances_boxed_1826_, v___x_1815_, v___y_1816_, v_b_1817_, v_a_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v_a_1818_);
lean_dec(v___y_1816_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1828_, lean_object* v___x_1829_, lean_object* v_pre_1830_, lean_object* v_post_1831_, uint8_t v_usedLetOnly_1832_, uint8_t v_skipConstInApp_1833_, uint8_t v_skipInstances_1834_, lean_object* v_a_1835_, lean_object* v_b_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___y_1844_; uint8_t v___x_1867_; 
v___x_1867_ = lean_nat_dec_lt(v_a_1835_, v_upperBound_1828_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec(v_a_1835_);
lean_dec_ref(v_post_1831_);
lean_dec_ref(v_pre_1830_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_b_1836_);
return v___x_1868_;
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1869_ = lean_array_fget_borrowed(v_b_1836_, v_a_1835_);
v___x_1870_ = lean_array_get_size(v___x_1829_);
v___x_1871_ = lean_nat_dec_lt(v_a_1835_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___f_1875_; 
lean_inc(v___x_1869_);
v___x_1872_ = lean_box(v_usedLetOnly_1832_);
v___x_1873_ = lean_box(v_skipConstInApp_1833_);
v___x_1874_ = lean_box(v_skipInstances_1834_);
lean_inc(v_a_1835_);
lean_inc(v___y_1837_);
lean_inc_ref(v_post_1831_);
lean_inc_ref(v_pre_1830_);
v___f_1875_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1875_, 0, v_pre_1830_);
lean_closure_set(v___f_1875_, 1, v_post_1831_);
lean_closure_set(v___f_1875_, 2, v___x_1872_);
lean_closure_set(v___f_1875_, 3, v___x_1873_);
lean_closure_set(v___f_1875_, 4, v___x_1874_);
lean_closure_set(v___f_1875_, 5, v___x_1869_);
lean_closure_set(v___f_1875_, 6, v___y_1837_);
lean_closure_set(v___f_1875_, 7, v_b_1836_);
lean_closure_set(v___f_1875_, 8, v_a_1835_);
v___y_1844_ = v___f_1875_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1876_; uint8_t v_isInstance_1877_; 
v___x_1876_ = lean_array_fget_borrowed(v___x_1829_, v_a_1835_);
v_isInstance_1877_ = lean_ctor_get_uint8(v___x_1876_, sizeof(void*)*1 + 4);
if (v_isInstance_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___f_1881_; 
lean_inc(v___x_1869_);
v___x_1878_ = lean_box(v_usedLetOnly_1832_);
v___x_1879_ = lean_box(v_skipConstInApp_1833_);
v___x_1880_ = lean_box(v_skipInstances_1834_);
lean_inc(v_a_1835_);
lean_inc(v___y_1837_);
lean_inc_ref(v_post_1831_);
lean_inc_ref(v_pre_1830_);
v___f_1881_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1881_, 0, v_pre_1830_);
lean_closure_set(v___f_1881_, 1, v_post_1831_);
lean_closure_set(v___f_1881_, 2, v___x_1878_);
lean_closure_set(v___f_1881_, 3, v___x_1879_);
lean_closure_set(v___f_1881_, 4, v___x_1880_);
lean_closure_set(v___f_1881_, 5, v___x_1869_);
lean_closure_set(v___f_1881_, 6, v___y_1837_);
lean_closure_set(v___f_1881_, 7, v_b_1836_);
lean_closure_set(v___f_1881_, 8, v_a_1835_);
v___y_1844_ = v___f_1881_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1882_; lean_object* v___f_1883_; 
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_b_1836_);
v___f_1883_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1883_, 0, v___x_1882_);
v___y_1844_ = v___f_1883_;
goto v___jp_1843_;
}
}
}
v___jp_1843_:
{
lean_object* v___x_1845_; 
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
v___x_1845_ = lean_apply_5(v___y_1844_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, lean_box(0));
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1858_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1858_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1858_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
if (lean_obj_tag(v_a_1846_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; 
lean_dec(v_a_1835_);
lean_dec_ref(v_post_1831_);
lean_dec_ref(v_pre_1830_);
v_a_1850_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v_a_1846_, 1);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v_a_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_del_object(v___x_1848_);
v_a_1854_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v_a_1846_, 1);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_nat_add(v_a_1835_, v___x_1855_);
lean_dec(v_a_1835_);
v_a_1835_ = v___x_1856_;
v_b_1836_ = v_a_1854_;
goto _start;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1835_);
lean_dec_ref(v_post_1831_);
lean_dec_ref(v_pre_1830_);
v_a_1859_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1845_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1845_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1884_, lean_object* v_pre_1885_, lean_object* v_post_1886_, uint8_t v_usedLetOnly_1887_, uint8_t v_skipConstInApp_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_f_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; 
if (lean_obj_tag(v_x_1889_) == 5)
{
lean_object* v_fn_1947_; lean_object* v_arg_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_fn_1947_ = lean_ctor_get(v_x_1889_, 0);
lean_inc_ref(v_fn_1947_);
v_arg_1948_ = lean_ctor_get(v_x_1889_, 1);
lean_inc_ref(v_arg_1948_);
lean_dec_ref_known(v_x_1889_, 2);
v___x_1949_ = lean_array_set(v_x_1890_, v_x_1891_, v_arg_1948_);
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = lean_nat_sub(v_x_1891_, v___x_1950_);
lean_dec(v_x_1891_);
v_x_1889_ = v_fn_1947_;
v_x_1890_ = v___x_1949_;
v_x_1891_ = v___x_1951_;
goto _start;
}
else
{
lean_dec(v_x_1891_);
if (v_skipConstInApp_1888_ == 0)
{
goto v___jp_1944_;
}
else
{
uint8_t v___x_1953_; 
v___x_1953_ = l_Lean_Expr_isConst(v_x_1889_);
if (v___x_1953_ == 0)
{
goto v___jp_1944_;
}
else
{
v_f_1899_ = v_x_1889_;
v___y_1900_ = v___y_1892_;
v___y_1901_ = v___y_1893_;
v___y_1902_ = v___y_1894_;
v___y_1903_ = v___y_1895_;
v___y_1904_ = v___y_1896_;
goto v___jp_1898_;
}
}
}
v___jp_1898_:
{
if (v_skipInstances_1884_ == 0)
{
size_t v_sz_1905_; size_t v___x_1906_; lean_object* v___x_1907_; 
v_sz_1905_ = lean_array_size(v_x_1890_);
v___x_1906_ = ((size_t)0ULL);
lean_inc_ref(v_post_1886_);
lean_inc_ref(v_pre_1885_);
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1885_, v_post_1886_, v_usedLetOnly_1887_, v_skipConstInApp_1888_, v_skipInstances_1884_, v_sz_1905_, v___x_1906_, v_x_1890_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1909_ = l_Lean_mkAppN(v_f_1899_, v_a_1908_);
lean_dec(v_a_1908_);
v___x_1910_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1885_, v_post_1886_, v_usedLetOnly_1887_, v_skipConstInApp_1888_, v_skipInstances_1884_, v___x_1909_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
return v___x_1910_;
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_post_1886_);
lean_dec_ref(v_pre_1885_);
v_a_1911_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1907_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1907_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_array_get_size(v_x_1890_);
lean_inc_ref(v_f_1899_);
v___x_1920_ = l_Lean_Meta_getFunInfoNArgs(v_f_1899_, v___x_1919_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_paramInfo_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v_paramInfo_1922_ = lean_ctor_get(v_a_1921_, 0);
lean_inc_ref(v_paramInfo_1922_);
lean_dec(v_a_1921_);
v___x_1923_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1886_);
lean_inc_ref(v_pre_1885_);
v___x_1924_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1919_, v_paramInfo_1922_, v_pre_1885_, v_post_1886_, v_usedLetOnly_1887_, v_skipConstInApp_1888_, v_skipInstances_1884_, v___x_1923_, v_x_1890_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec_ref(v_paramInfo_1922_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = l_Lean_mkAppN(v_f_1899_, v_a_1925_);
lean_dec(v_a_1925_);
v___x_1927_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1885_, v_post_1886_, v_usedLetOnly_1887_, v_skipConstInApp_1888_, v_skipInstances_1884_, v___x_1926_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
return v___x_1927_;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_post_1886_);
lean_dec_ref(v_pre_1885_);
v_a_1928_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1924_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1924_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_x_1890_);
lean_dec_ref(v_post_1886_);
lean_dec_ref(v_pre_1885_);
v_a_1936_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1920_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1920_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
v___jp_1944_:
{
lean_object* v___x_1945_; 
lean_inc_ref(v_post_1886_);
lean_inc_ref(v_pre_1885_);
v___x_1945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1885_, v_post_1886_, v_usedLetOnly_1887_, v_skipConstInApp_1888_, v_skipInstances_1884_, v_x_1889_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1945_, 1);
v_f_1899_ = v_a_1946_;
v___y_1900_ = v___y_1892_;
v___y_1901_ = v___y_1893_;
v___y_1902_ = v___y_1894_;
v___y_1903_ = v___y_1895_;
v___y_1904_ = v___y_1896_;
goto v___jp_1898_;
}
else
{
lean_dec_ref(v_x_1890_);
lean_dec_ref(v_post_1886_);
lean_dec_ref(v_pre_1885_);
return v___x_1945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1954_, lean_object* v_pre_1955_, lean_object* v_e_1956_, lean_object* v_post_1957_, uint8_t v_usedLetOnly_1958_, uint8_t v_skipConstInApp_1959_, uint8_t v_skipInstances_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Core_checkSystem(v___x_1954_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref_known(v___x_1967_, 1);
lean_inc_ref(v_pre_1955_);
lean_inc(v___y_1965_);
lean_inc_ref(v___y_1964_);
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1962_);
lean_inc_ref(v_e_1956_);
v___x_1968_ = lean_apply_6(v_pre_1955_, v_e_1956_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, lean_box(0));
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2017_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_2017_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2017_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___y_1974_; 
switch(lean_obj_tag(v_a_1969_))
{
case 0:
{
lean_object* v_e_2009_; lean_object* v___x_2011_; 
lean_dec_ref(v_post_1957_);
lean_dec_ref(v_e_1956_);
lean_dec_ref(v_pre_1955_);
v_e_2009_ = lean_ctor_get(v_a_1969_, 0);
lean_inc_ref(v_e_2009_);
lean_dec_ref_known(v_a_1969_, 1);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v_e_2009_);
v___x_2011_ = v___x_1971_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_e_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
case 1:
{
lean_object* v_e_2013_; lean_object* v___x_2014_; 
lean_del_object(v___x_1971_);
lean_dec_ref(v_e_1956_);
v_e_2013_ = lean_ctor_get(v_a_1969_, 0);
lean_inc_ref(v_e_2013_);
lean_dec_ref_known(v_a_1969_, 1);
v___x_2014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v_e_2013_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_2014_;
}
default: 
{
lean_object* v_e_x3f_2015_; 
lean_del_object(v___x_1971_);
v_e_x3f_2015_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_e_x3f_2015_);
lean_dec_ref_known(v_a_1969_, 1);
if (lean_obj_tag(v_e_x3f_2015_) == 0)
{
v___y_1974_ = v_e_1956_;
goto v___jp_1973_;
}
else
{
lean_object* v_val_2016_; 
lean_dec_ref(v_e_1956_);
v_val_2016_ = lean_ctor_get(v_e_x3f_2015_, 0);
lean_inc(v_val_2016_);
lean_dec_ref_known(v_e_x3f_2015_, 1);
v___y_1974_ = v_val_2016_;
goto v___jp_1973_;
}
}
}
v___jp_1973_:
{
switch(lean_obj_tag(v___y_1974_))
{
case 7:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1976_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v___x_1975_, v___y_1974_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1976_;
}
case 6:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v___x_1977_, v___y_1974_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1978_;
}
case 8:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1980_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v___x_1979_, v___y_1974_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1980_;
}
case 5:
{
lean_object* v_dummy_1981_; lean_object* v_nargs_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_dummy_1981_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1982_ = l_Lean_Expr_getAppNumArgs(v___y_1974_);
lean_inc(v_nargs_1982_);
v___x_1983_ = lean_mk_array(v_nargs_1982_, v_dummy_1981_);
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = lean_nat_sub(v_nargs_1982_, v___x_1984_);
lean_dec(v_nargs_1982_);
v___x_1986_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1960_, v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v___y_1974_, v___x_1983_, v___x_1985_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1986_;
}
case 10:
{
lean_object* v_data_1987_; lean_object* v_expr_1988_; lean_object* v___x_1989_; 
v_data_1987_ = lean_ctor_get(v___y_1974_, 0);
v_expr_1988_ = lean_ctor_get(v___y_1974_, 1);
lean_inc_ref(v_expr_1988_);
lean_inc_ref(v_post_1957_);
lean_inc_ref(v_pre_1955_);
v___x_1989_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v_expr_1988_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; size_t v___x_1991_; size_t v___x_1992_; uint8_t v___x_1993_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v___x_1991_ = lean_ptr_addr(v_expr_1988_);
v___x_1992_ = lean_ptr_addr(v_a_1990_);
v___x_1993_ = lean_usize_dec_eq(v___x_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_inc(v_data_1987_);
lean_dec_ref_known(v___y_1974_, 2);
v___x_1994_ = l_Lean_Expr_mdata___override(v_data_1987_, v_a_1990_);
v___x_1995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v___x_1994_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1995_;
}
else
{
lean_object* v___x_1996_; 
lean_dec(v_a_1990_);
v___x_1996_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v___y_1974_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1996_;
}
}
else
{
lean_dec_ref_known(v___y_1974_, 2);
lean_dec_ref(v_post_1957_);
lean_dec_ref(v_pre_1955_);
return v___x_1989_;
}
}
case 11:
{
lean_object* v_typeName_1997_; lean_object* v_idx_1998_; lean_object* v_struct_1999_; lean_object* v___x_2000_; 
v_typeName_1997_ = lean_ctor_get(v___y_1974_, 0);
v_idx_1998_ = lean_ctor_get(v___y_1974_, 1);
v_struct_1999_ = lean_ctor_get(v___y_1974_, 2);
lean_inc_ref(v_struct_1999_);
lean_inc_ref(v_post_1957_);
lean_inc_ref(v_pre_1955_);
v___x_2000_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v_struct_1999_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; size_t v___x_2002_; size_t v___x_2003_; uint8_t v___x_2004_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = lean_ptr_addr(v_struct_1999_);
v___x_2003_ = lean_ptr_addr(v_a_2001_);
v___x_2004_ = lean_usize_dec_eq(v___x_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_inc(v_idx_1998_);
lean_inc(v_typeName_1997_);
lean_dec_ref_known(v___y_1974_, 3);
v___x_2005_ = l_Lean_Expr_proj___override(v_typeName_1997_, v_idx_1998_, v_a_2001_);
v___x_2006_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v___x_2005_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; 
lean_dec(v_a_2001_);
v___x_2007_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v___y_1974_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_2007_;
}
}
else
{
lean_dec_ref_known(v___y_1974_, 3);
lean_dec_ref(v_post_1957_);
lean_dec_ref(v_pre_1955_);
return v___x_2000_;
}
}
default: 
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1955_, v_post_1957_, v_usedLetOnly_1958_, v_skipConstInApp_1959_, v_skipInstances_1960_, v___y_1974_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_2008_;
}
}
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v_post_1957_);
lean_dec_ref(v_e_1956_);
lean_dec_ref(v_pre_1955_);
v_a_2018_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1968_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1968_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec_ref(v_post_1957_);
lean_dec_ref(v_e_1956_);
lean_dec_ref(v_pre_1955_);
v_a_2026_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1967_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1967_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2034_, lean_object* v_pre_2035_, lean_object* v_e_2036_, lean_object* v_post_2037_, lean_object* v_usedLetOnly_2038_, lean_object* v_skipConstInApp_2039_, lean_object* v_skipInstances_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
uint8_t v_usedLetOnly_boxed_2047_; uint8_t v_skipConstInApp_boxed_2048_; uint8_t v_skipInstances_boxed_2049_; lean_object* v_res_2050_; 
v_usedLetOnly_boxed_2047_ = lean_unbox(v_usedLetOnly_2038_);
v_skipConstInApp_boxed_2048_ = lean_unbox(v_skipConstInApp_2039_);
v_skipInstances_boxed_2049_ = lean_unbox(v_skipInstances_2040_);
v_res_2050_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2034_, v_pre_2035_, v_e_2036_, v_post_2037_, v_usedLetOnly_boxed_2047_, v_skipConstInApp_boxed_2048_, v_skipInstances_boxed_2049_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2051_, lean_object* v_post_2052_, uint8_t v_usedLetOnly_2053_, uint8_t v_skipConstInApp_2054_, uint8_t v_skipInstances_2055_, lean_object* v_e_2056_, lean_object* v_a_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_inc(v_a_2057_);
v___x_2063_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2063_, 0, lean_box(0));
lean_closure_set(v___x_2063_, 1, lean_box(0));
lean_closure_set(v___x_2063_, 2, v_a_2057_);
v___x_2064_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2063_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2099_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2067_ = v___x_2064_;
v_isShared_2068_ = v_isSharedCheck_2099_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2064_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2099_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2065_, v_e_2056_);
lean_dec(v_a_2065_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; 
lean_del_object(v___x_2067_);
v___x_2070_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2071_ = lean_box(v_usedLetOnly_2053_);
v___x_2072_ = lean_box(v_skipConstInApp_2054_);
v___x_2073_ = lean_box(v_skipInstances_2055_);
lean_inc_ref(v_e_2056_);
v___f_2074_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2074_, 0, v___x_2070_);
lean_closure_set(v___f_2074_, 1, v_pre_2051_);
lean_closure_set(v___f_2074_, 2, v_e_2056_);
lean_closure_set(v___f_2074_, 3, v_post_2052_);
lean_closure_set(v___f_2074_, 4, v___x_2071_);
lean_closure_set(v___f_2074_, 5, v___x_2072_);
lean_closure_set(v___f_2074_, 6, v___x_2073_);
v___x_2075_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2074_, v_a_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___f_2077_; lean_object* v___x_2078_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc_n(v_a_2076_, 2);
lean_dec_ref_known(v___x_2075_, 1);
lean_inc(v_a_2057_);
v___f_2077_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2077_, 0, v_a_2057_);
lean_closure_set(v___f_2077_, 1, v_e_2056_);
lean_closure_set(v___f_2077_, 2, v_a_2076_);
v___x_2078_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2077_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2078_, 0);
lean_dec(v_unused_2086_);
v___x_2080_ = v___x_2078_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_dec(v___x_2078_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v_a_2076_);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2076_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v_a_2076_);
v_a_2087_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2078_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2078_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_dec_ref(v_e_2056_);
return v___x_2075_;
}
}
else
{
lean_object* v_val_2095_; lean_object* v___x_2097_; 
lean_dec_ref(v_e_2056_);
lean_dec_ref(v_post_2052_);
lean_dec_ref(v_pre_2051_);
v_val_2095_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v___x_2069_, 1);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v_val_2095_);
v___x_2097_ = v___x_2067_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_val_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_e_2056_);
lean_dec_ref(v_post_2052_);
lean_dec_ref(v_pre_2051_);
v_a_2100_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2064_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2064_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2108_, lean_object* v_post_2109_, uint8_t v_usedLetOnly_2110_, uint8_t v_skipConstInApp_2111_, uint8_t v_skipInstances_2112_, lean_object* v_fvars_2113_, lean_object* v_e_2114_, lean_object* v_a_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
if (lean_obj_tag(v_e_2114_) == 7)
{
lean_object* v_binderName_2121_; lean_object* v_binderType_2122_; lean_object* v_body_2123_; uint8_t v_binderInfo_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_binderName_2121_ = lean_ctor_get(v_e_2114_, 0);
lean_inc(v_binderName_2121_);
v_binderType_2122_ = lean_ctor_get(v_e_2114_, 1);
lean_inc_ref(v_binderType_2122_);
v_body_2123_ = lean_ctor_get(v_e_2114_, 2);
lean_inc_ref(v_body_2123_);
v_binderInfo_2124_ = lean_ctor_get_uint8(v_e_2114_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2114_, 3);
v___x_2125_ = lean_box(v_usedLetOnly_2110_);
v___x_2126_ = lean_box(v_skipConstInApp_2111_);
v___x_2127_ = lean_box(v_skipInstances_2112_);
lean_inc_ref(v_post_2109_);
lean_inc_ref(v_pre_2108_);
lean_inc_ref(v_fvars_2113_);
v___f_2128_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2128_, 0, v_fvars_2113_);
lean_closure_set(v___f_2128_, 1, v_pre_2108_);
lean_closure_set(v___f_2128_, 2, v_post_2109_);
lean_closure_set(v___f_2128_, 3, v___x_2125_);
lean_closure_set(v___f_2128_, 4, v___x_2126_);
lean_closure_set(v___f_2128_, 5, v___x_2127_);
lean_closure_set(v___f_2128_, 6, v_body_2123_);
v___x_2129_ = lean_expr_instantiate_rev(v_binderType_2122_, v_fvars_2113_);
lean_dec_ref(v_fvars_2113_);
lean_dec_ref(v_binderType_2122_);
v___x_2130_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2108_, v_post_2109_, v_usedLetOnly_2110_, v_skipConstInApp_2111_, v_skipInstances_2112_, v___x_2129_, v_a_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = 0;
v___x_2133_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2121_, v_binderInfo_2124_, v_a_2131_, v___f_2128_, v___x_2132_, v_a_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2133_;
}
else
{
lean_dec_ref(v___f_2128_);
lean_dec(v_binderName_2121_);
return v___x_2130_;
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
uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v_a_2314_; lean_object* v___x_2315_; 
v___x_2311_ = 0;
v___x_2312_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2313_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2312_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
v___x_2315_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2302_, v_post_2303_, v_usedLetOnly_2304_, v_skipConstInApp_2305_, v___x_2311_, v_input_2301_, v_a_2314_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2317_, 0, lean_box(0));
lean_closure_set(v___x_2317_, 1, lean_box(0));
lean_closure_set(v___x_2317_, 2, v_a_2314_);
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
lean_dec(v_a_2314_);
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
uint8_t v___x_2422_; lean_object* v___y_2424_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2422_ = lean_nat_dec_eq(v___x_2402_, v___x_2403_);
v___x_2438_ = lean_st_ref_get(v_val_2398_);
v___x_2439_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2401_, v_a_2407_, v___x_2438_);
lean_dec(v___x_2438_);
if (v___x_2439_ == 0)
{
v_a_2415_ = v_b_2408_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2440_; uint8_t v_foApprox_2441_; uint8_t v_ctxApprox_2442_; uint8_t v_quasiPatternApprox_2443_; uint8_t v_constApprox_2444_; uint8_t v_isDefEqStuckEx_2445_; uint8_t v_unificationHints_2446_; uint8_t v_assignSyntheticOpaque_2447_; uint8_t v_offsetCnstrs_2448_; uint8_t v_transparency_2449_; uint8_t v_etaStruct_2450_; uint8_t v_univApprox_2451_; uint8_t v_iota_2452_; uint8_t v_beta_2453_; uint8_t v_proj_2454_; uint8_t v_zeta_2455_; uint8_t v_zetaDelta_2456_; uint8_t v_zetaUnused_2457_; uint8_t v_zetaHave_2458_; uint8_t v_canUnfoldPredicateConfig_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2489_; 
v___x_2440_ = l_Lean_Meta_Context_config(v___y_2409_);
v_foApprox_2441_ = lean_ctor_get_uint8(v___x_2440_, 0);
v_ctxApprox_2442_ = lean_ctor_get_uint8(v___x_2440_, 1);
v_quasiPatternApprox_2443_ = lean_ctor_get_uint8(v___x_2440_, 2);
v_constApprox_2444_ = lean_ctor_get_uint8(v___x_2440_, 3);
v_isDefEqStuckEx_2445_ = lean_ctor_get_uint8(v___x_2440_, 4);
v_unificationHints_2446_ = lean_ctor_get_uint8(v___x_2440_, 5);
v_assignSyntheticOpaque_2447_ = lean_ctor_get_uint8(v___x_2440_, 7);
v_offsetCnstrs_2448_ = lean_ctor_get_uint8(v___x_2440_, 8);
v_transparency_2449_ = lean_ctor_get_uint8(v___x_2440_, 9);
v_etaStruct_2450_ = lean_ctor_get_uint8(v___x_2440_, 10);
v_univApprox_2451_ = lean_ctor_get_uint8(v___x_2440_, 11);
v_iota_2452_ = lean_ctor_get_uint8(v___x_2440_, 12);
v_beta_2453_ = lean_ctor_get_uint8(v___x_2440_, 13);
v_proj_2454_ = lean_ctor_get_uint8(v___x_2440_, 14);
v_zeta_2455_ = lean_ctor_get_uint8(v___x_2440_, 15);
v_zetaDelta_2456_ = lean_ctor_get_uint8(v___x_2440_, 16);
v_zetaUnused_2457_ = lean_ctor_get_uint8(v___x_2440_, 17);
v_zetaHave_2458_ = lean_ctor_get_uint8(v___x_2440_, 18);
v_canUnfoldPredicateConfig_2459_ = lean_ctor_get_uint8(v___x_2440_, 19);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2461_ = v___x_2440_;
v_isShared_2462_ = v_isSharedCheck_2489_;
goto v_resetjp_2460_;
}
else
{
lean_dec(v___x_2440_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2489_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
uint8_t v_trackZetaDelta_2463_; lean_object* v_zetaDeltaSet_2464_; lean_object* v_lctx_2465_; lean_object* v_localInstances_2466_; lean_object* v_defEqCtx_x3f_2467_; lean_object* v_synthPendingDepth_2468_; lean_object* v_customCanUnfoldPredicate_x3f_2469_; uint8_t v_univApprox_2470_; uint8_t v_inTypeClassResolution_2471_; uint8_t v_cacheInferType_2472_; uint8_t v___x_2473_; lean_object* v___x_2475_; 
v_trackZetaDelta_2463_ = lean_ctor_get_uint8(v___y_2409_, sizeof(void*)*7);
v_zetaDeltaSet_2464_ = lean_ctor_get(v___y_2409_, 1);
v_lctx_2465_ = lean_ctor_get(v___y_2409_, 2);
v_localInstances_2466_ = lean_ctor_get(v___y_2409_, 3);
v_defEqCtx_x3f_2467_ = lean_ctor_get(v___y_2409_, 4);
v_synthPendingDepth_2468_ = lean_ctor_get(v___y_2409_, 5);
v_customCanUnfoldPredicate_x3f_2469_ = lean_ctor_get(v___y_2409_, 6);
v_univApprox_2470_ = lean_ctor_get_uint8(v___y_2409_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2471_ = lean_ctor_get_uint8(v___y_2409_, sizeof(void*)*7 + 2);
v_cacheInferType_2472_ = lean_ctor_get_uint8(v___y_2409_, sizeof(void*)*7 + 3);
v___x_2473_ = 0;
if (v_isShared_2462_ == 0)
{
v___x_2475_ = v___x_2461_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 0, v_foApprox_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 1, v_ctxApprox_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 2, v_quasiPatternApprox_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 3, v_constApprox_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 4, v_isDefEqStuckEx_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 5, v_unificationHints_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 7, v_assignSyntheticOpaque_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 8, v_offsetCnstrs_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 9, v_transparency_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 10, v_etaStruct_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 11, v_univApprox_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 12, v_iota_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 13, v_beta_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 14, v_proj_2454_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 15, v_zeta_2455_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 16, v_zetaDelta_2456_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 17, v_zetaUnused_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 18, v_zetaHave_2458_);
lean_ctor_set_uint8(v_reuseFailAlloc_2488_, 19, v_canUnfoldPredicateConfig_2459_);
v___x_2475_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
uint64_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v_transparency_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; uint8_t v___x_2483_; 
lean_ctor_set_uint8(v___x_2475_, 6, v___x_2473_);
v___x_2476_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2475_);
v___x_2477_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set_uint64(v___x_2477_, sizeof(void*)*1, v___x_2476_);
lean_inc(v_customCanUnfoldPredicate_x3f_2469_);
lean_inc(v_synthPendingDepth_2468_);
lean_inc(v_defEqCtx_x3f_2467_);
lean_inc_ref(v_localInstances_2466_);
lean_inc_ref(v_lctx_2465_);
lean_inc(v_zetaDeltaSet_2464_);
lean_inc_ref(v___x_2477_);
v___x_2478_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v_zetaDeltaSet_2464_);
lean_ctor_set(v___x_2478_, 2, v_lctx_2465_);
lean_ctor_set(v___x_2478_, 3, v_localInstances_2466_);
lean_ctor_set(v___x_2478_, 4, v_defEqCtx_x3f_2467_);
lean_ctor_set(v___x_2478_, 5, v_synthPendingDepth_2468_);
lean_ctor_set(v___x_2478_, 6, v_customCanUnfoldPredicate_x3f_2469_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*7, v_trackZetaDelta_2463_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*7 + 1, v_univApprox_2470_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2471_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*7 + 3, v_cacheInferType_2472_);
v___x_2479_ = l_Lean_Meta_Context_config(v___x_2478_);
v_transparency_2480_ = lean_ctor_get_uint8(v___x_2479_, 9);
lean_dec_ref(v___x_2479_);
v___x_2481_ = lean_array_fget_borrowed(v_params_2405_, v_a_2407_);
v___x_2482_ = 2;
v___x_2483_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2480_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref_known(v___x_2478_, 7);
v___x_2484_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2482_, v___x_2477_);
lean_inc(v_customCanUnfoldPredicate_x3f_2469_);
lean_inc(v_synthPendingDepth_2468_);
lean_inc(v_defEqCtx_x3f_2467_);
lean_inc_ref(v_localInstances_2466_);
lean_inc_ref(v_lctx_2465_);
lean_inc(v_zetaDeltaSet_2464_);
v___x_2485_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v_zetaDeltaSet_2464_);
lean_ctor_set(v___x_2485_, 2, v_lctx_2465_);
lean_ctor_set(v___x_2485_, 3, v_localInstances_2466_);
lean_ctor_set(v___x_2485_, 4, v_defEqCtx_x3f_2467_);
lean_ctor_set(v___x_2485_, 5, v_synthPendingDepth_2468_);
lean_ctor_set(v___x_2485_, 6, v_customCanUnfoldPredicate_x3f_2469_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*7, v_trackZetaDelta_2463_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*7 + 1, v_univApprox_2470_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2471_);
lean_ctor_set_uint8(v___x_2485_, sizeof(void*)*7 + 3, v_cacheInferType_2472_);
lean_inc_ref(v___x_2406_);
lean_inc(v___x_2481_);
v___x_2486_ = l_Lean_Meta_isExprDefEq(v___x_2481_, v___x_2406_, v___x_2485_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec_ref_known(v___x_2485_, 7);
v___y_2424_ = v___x_2486_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2487_; 
lean_dec_ref_known(v___x_2477_, 1);
lean_inc_ref(v___x_2406_);
lean_inc(v___x_2481_);
v___x_2487_ = l_Lean_Meta_isExprDefEq(v___x_2481_, v___x_2406_, v___x_2478_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec_ref_known(v___x_2478_, 7);
v___y_2424_ = v___x_2487_;
goto v___jp_2423_;
}
}
}
}
v___jp_2423_:
{
if (lean_obj_tag(v___y_2424_) == 0)
{
lean_object* v_a_2425_; uint8_t v___x_2426_; 
v_a_2425_ = lean_ctor_get(v___y_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___y_2424_, 1);
v___x_2426_ = lean_unbox(v_a_2425_);
lean_dec(v_a_2425_);
if (v___x_2426_ == 0)
{
v_a_2415_ = v_b_2408_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_st_ref_take(v_val_2398_);
lean_inc(v_a_2407_);
lean_inc(v_next_2400_);
v___x_2428_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2399_, v_next_2400_, v_next_2401_, v_a_2407_, v___x_2427_);
v___x_2429_ = lean_st_ref_put(v_val_2398_, v___x_2428_);
v_a_2415_ = v___x_2422_;
goto v___jp_2414_;
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_a_2407_);
lean_dec_ref(v___x_2406_);
lean_dec(v_next_2400_);
v_a_2430_ = lean_ctor_get(v___y_2424_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___y_2424_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___y_2424_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___y_2424_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
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
lean_object* v___x_2584_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2584_ = lean_box(0);
v___x_2591_ = l_Lean_instInhabitedExpr;
v___x_2592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2541_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; uint8_t v___x_2594_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
v___x_2594_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2542_, v_a_2550_, v_a_2593_);
lean_dec(v_a_2593_);
if (v___x_2594_ == 0)
{
v_a_2558_ = v___x_2584_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2595_ = lean_array_get_size(v_args_2544_);
v___x_2596_ = lean_nat_dec_lt(v_a_2550_, v___x_2595_);
if (v___x_2596_ == 0)
{
lean_object* v_toCold_2597_; lean_object* v_options_2598_; uint8_t v_hasTrace_2599_; 
v_toCold_2597_ = lean_ctor_get(v___y_2554_, 0);
v_options_2598_ = lean_ctor_get(v_toCold_2597_, 2);
v_hasTrace_2599_ = lean_ctor_get_uint8(v_options_2598_, sizeof(void*)*1);
if (v_hasTrace_2599_ == 0)
{
goto v___jp_2587_;
}
else
{
lean_object* v_inheritedTraceOptions_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v_inheritedTraceOptions_2600_ = lean_ctor_get(v_toCold_2597_, 11);
v___x_2601_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2602_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2603_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2600_, v_options_2598_, v___x_2602_);
if (v___x_2603_ == 0)
{
goto v___jp_2587_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2604_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2542_);
v___x_2605_ = l_Nat_reprFast(v_val_2542_);
v___x_2606_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
v___x_2607_ = l_Lean_MessageData_ofFormat(v___x_2606_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2604_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
lean_inc(v_a_2550_);
v___x_2611_ = l_Nat_reprFast(v_a_2550_);
v___x_2612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
v___x_2613_ = l_Lean_MessageData_ofFormat(v___x_2612_);
lean_inc_ref(v___x_2613_);
v___x_2614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2610_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
lean_inc_ref(v_e_2545_);
v___x_2617_ = l_Lean_MessageData_ofExpr(v_e_2545_);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2616_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___x_2613_);
v___x_2622_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2601_, v___x_2621_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2624_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
lean_inc(v_a_2550_);
v___x_2624_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2584_, v_a_2623_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2624_;
goto v___jp_2562_;
}
else
{
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
return v___x_2622_;
}
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_array_fget_borrowed(v_args_2544_, v_a_2550_);
v___x_2626_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2541_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2542_, v_a_2550_, v_next_2546_, v_a_2627_);
lean_dec(v_a_2627_);
if (lean_obj_tag(v___x_2628_) == 1)
{
lean_object* v_val_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2730_; 
v_val_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2730_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_val_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2730_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; uint8_t v_foApprox_2634_; uint8_t v_ctxApprox_2635_; uint8_t v_quasiPatternApprox_2636_; uint8_t v_constApprox_2637_; uint8_t v_isDefEqStuckEx_2638_; uint8_t v_unificationHints_2639_; uint8_t v_assignSyntheticOpaque_2640_; uint8_t v_offsetCnstrs_2641_; uint8_t v_transparency_2642_; uint8_t v_etaStruct_2643_; uint8_t v_univApprox_2644_; uint8_t v_iota_2645_; uint8_t v_beta_2646_; uint8_t v_proj_2647_; uint8_t v_zeta_2648_; uint8_t v_zetaDelta_2649_; uint8_t v_zetaUnused_2650_; uint8_t v_zetaHave_2651_; uint8_t v_canUnfoldPredicateConfig_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2729_; 
v___x_2633_ = l_Lean_Meta_Context_config(v___y_2552_);
v_foApprox_2634_ = lean_ctor_get_uint8(v___x_2633_, 0);
v_ctxApprox_2635_ = lean_ctor_get_uint8(v___x_2633_, 1);
v_quasiPatternApprox_2636_ = lean_ctor_get_uint8(v___x_2633_, 2);
v_constApprox_2637_ = lean_ctor_get_uint8(v___x_2633_, 3);
v_isDefEqStuckEx_2638_ = lean_ctor_get_uint8(v___x_2633_, 4);
v_unificationHints_2639_ = lean_ctor_get_uint8(v___x_2633_, 5);
v_assignSyntheticOpaque_2640_ = lean_ctor_get_uint8(v___x_2633_, 7);
v_offsetCnstrs_2641_ = lean_ctor_get_uint8(v___x_2633_, 8);
v_transparency_2642_ = lean_ctor_get_uint8(v___x_2633_, 9);
v_etaStruct_2643_ = lean_ctor_get_uint8(v___x_2633_, 10);
v_univApprox_2644_ = lean_ctor_get_uint8(v___x_2633_, 11);
v_iota_2645_ = lean_ctor_get_uint8(v___x_2633_, 12);
v_beta_2646_ = lean_ctor_get_uint8(v___x_2633_, 13);
v_proj_2647_ = lean_ctor_get_uint8(v___x_2633_, 14);
v_zeta_2648_ = lean_ctor_get_uint8(v___x_2633_, 15);
v_zetaDelta_2649_ = lean_ctor_get_uint8(v___x_2633_, 16);
v_zetaUnused_2650_ = lean_ctor_get_uint8(v___x_2633_, 17);
v_zetaHave_2651_ = lean_ctor_get_uint8(v___x_2633_, 18);
v_canUnfoldPredicateConfig_2652_ = lean_ctor_get_uint8(v___x_2633_, 19);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2654_ = v___x_2633_;
v_isShared_2655_ = v_isSharedCheck_2729_;
goto v_resetjp_2653_;
}
else
{
lean_dec(v___x_2633_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2729_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
uint8_t v_trackZetaDelta_2656_; lean_object* v_zetaDeltaSet_2657_; lean_object* v_lctx_2658_; lean_object* v_localInstances_2659_; lean_object* v_defEqCtx_x3f_2660_; lean_object* v_synthPendingDepth_2661_; lean_object* v_customCanUnfoldPredicate_x3f_2662_; uint8_t v_univApprox_2663_; uint8_t v_inTypeClassResolution_2664_; uint8_t v_cacheInferType_2665_; uint8_t v___x_2666_; lean_object* v___x_2668_; 
v_trackZetaDelta_2656_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*7);
v_zetaDeltaSet_2657_ = lean_ctor_get(v___y_2552_, 1);
v_lctx_2658_ = lean_ctor_get(v___y_2552_, 2);
v_localInstances_2659_ = lean_ctor_get(v___y_2552_, 3);
v_defEqCtx_x3f_2660_ = lean_ctor_get(v___y_2552_, 4);
v_synthPendingDepth_2661_ = lean_ctor_get(v___y_2552_, 5);
v_customCanUnfoldPredicate_x3f_2662_ = lean_ctor_get(v___y_2552_, 6);
v_univApprox_2663_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2664_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*7 + 2);
v_cacheInferType_2665_ = lean_ctor_get_uint8(v___y_2552_, sizeof(void*)*7 + 3);
v___x_2666_ = 0;
if (v_isShared_2655_ == 0)
{
v___x_2668_ = v___x_2654_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 0, v_foApprox_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 1, v_ctxApprox_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 2, v_quasiPatternApprox_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 3, v_constApprox_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 4, v_isDefEqStuckEx_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 5, v_unificationHints_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 7, v_assignSyntheticOpaque_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 8, v_offsetCnstrs_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 9, v_transparency_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 10, v_etaStruct_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 11, v_univApprox_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 12, v_iota_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 13, v_beta_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 14, v_proj_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 15, v_zeta_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 16, v_zetaDelta_2649_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 17, v_zetaUnused_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 18, v_zetaHave_2651_);
lean_ctor_set_uint8(v_reuseFailAlloc_2728_, 19, v_canUnfoldPredicateConfig_2652_);
v___x_2668_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
uint64_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v_transparency_2673_; lean_object* v___x_2674_; lean_object* v___y_2676_; uint8_t v___x_2722_; uint8_t v___x_2723_; 
lean_ctor_set_uint8(v___x_2668_, 6, v___x_2666_);
v___x_2669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2668_);
v___x_2670_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set_uint64(v___x_2670_, sizeof(void*)*1, v___x_2669_);
lean_inc(v_customCanUnfoldPredicate_x3f_2662_);
lean_inc(v_synthPendingDepth_2661_);
lean_inc(v_defEqCtx_x3f_2660_);
lean_inc_ref(v_localInstances_2659_);
lean_inc_ref(v_lctx_2658_);
lean_inc(v_zetaDeltaSet_2657_);
lean_inc_ref(v___x_2670_);
v___x_2671_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v_zetaDeltaSet_2657_);
lean_ctor_set(v___x_2671_, 2, v_lctx_2658_);
lean_ctor_set(v___x_2671_, 3, v_localInstances_2659_);
lean_ctor_set(v___x_2671_, 4, v_defEqCtx_x3f_2660_);
lean_ctor_set(v___x_2671_, 5, v_synthPendingDepth_2661_);
lean_ctor_set(v___x_2671_, 6, v_customCanUnfoldPredicate_x3f_2662_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7, v_trackZetaDelta_2656_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 1, v_univApprox_2663_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2664_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 3, v_cacheInferType_2665_);
v___x_2672_ = l_Lean_Meta_Context_config(v___x_2671_);
v_transparency_2673_ = lean_ctor_get_uint8(v___x_2672_, 9);
lean_dec_ref(v___x_2672_);
v___x_2674_ = lean_array_get_borrowed(v___x_2591_, v_params_2547_, v_val_2629_);
lean_dec(v_val_2629_);
v___x_2722_ = 2;
v___x_2723_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2673_, v___x_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec_ref_known(v___x_2671_, 7);
v___x_2724_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2722_, v___x_2670_);
lean_inc(v_customCanUnfoldPredicate_x3f_2662_);
lean_inc(v_synthPendingDepth_2661_);
lean_inc(v_defEqCtx_x3f_2660_);
lean_inc_ref(v_localInstances_2659_);
lean_inc_ref(v_lctx_2658_);
lean_inc(v_zetaDeltaSet_2657_);
v___x_2725_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v_zetaDeltaSet_2657_);
lean_ctor_set(v___x_2725_, 2, v_lctx_2658_);
lean_ctor_set(v___x_2725_, 3, v_localInstances_2659_);
lean_ctor_set(v___x_2725_, 4, v_defEqCtx_x3f_2660_);
lean_ctor_set(v___x_2725_, 5, v_synthPendingDepth_2661_);
lean_ctor_set(v___x_2725_, 6, v_customCanUnfoldPredicate_x3f_2662_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*7, v_trackZetaDelta_2656_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*7 + 1, v_univApprox_2663_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2664_);
lean_ctor_set_uint8(v___x_2725_, sizeof(void*)*7 + 3, v_cacheInferType_2665_);
lean_inc(v___x_2625_);
lean_inc(v___x_2674_);
v___x_2726_ = l_Lean_Meta_isExprDefEq(v___x_2674_, v___x_2625_, v___x_2725_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec_ref_known(v___x_2725_, 7);
v___y_2676_ = v___x_2726_;
goto v___jp_2675_;
}
else
{
lean_object* v___x_2727_; 
lean_dec_ref_known(v___x_2670_, 1);
lean_inc(v___x_2625_);
lean_inc(v___x_2674_);
v___x_2727_ = l_Lean_Meta_isExprDefEq(v___x_2674_, v___x_2625_, v___x_2671_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec_ref_known(v___x_2671_, 7);
v___y_2676_ = v___x_2727_;
goto v___jp_2675_;
}
v___jp_2675_:
{
if (lean_obj_tag(v___y_2676_) == 0)
{
lean_object* v_a_2677_; uint8_t v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___y_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___y_2676_, 1);
v___x_2678_ = lean_unbox(v_a_2677_);
lean_dec(v_a_2677_);
if (v___x_2678_ == 0)
{
lean_object* v_toCold_2679_; lean_object* v_options_2680_; uint8_t v_hasTrace_2681_; 
v_toCold_2679_ = lean_ctor_get(v___y_2554_, 0);
v_options_2680_ = lean_ctor_get(v_toCold_2679_, 2);
v_hasTrace_2681_ = lean_ctor_get_uint8(v_options_2680_, sizeof(void*)*1);
if (v_hasTrace_2681_ == 0)
{
lean_del_object(v___x_2631_);
goto v___jp_2589_;
}
else
{
lean_object* v_inheritedTraceOptions_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v_inheritedTraceOptions_2682_ = lean_ctor_get(v_toCold_2679_, 11);
v___x_2683_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2684_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2685_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2682_, v_options_2680_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_del_object(v___x_2631_);
goto v___jp_2589_;
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2686_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2542_);
v___x_2687_ = l_Nat_reprFast(v_val_2542_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set_tag(v___x_2631_, 3);
lean_ctor_set(v___x_2631_, 0, v___x_2687_);
v___x_2689_ = v___x_2631_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2690_ = l_Lean_MessageData_ofFormat(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2686_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
lean_inc(v_a_2550_);
v___x_2694_ = l_Nat_reprFast(v_a_2550_);
v___x_2695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
v___x_2696_ = l_Lean_MessageData_ofFormat(v___x_2695_);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2693_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
lean_inc_ref(v_e_2545_);
v___x_2700_ = l_Lean_MessageData_ofExpr(v_e_2545_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
lean_inc(v___x_2674_);
v___x_2704_ = l_Lean_MessageData_ofExpr(v___x_2674_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
lean_inc(v___x_2625_);
v___x_2708_ = l_Lean_MessageData_ofExpr(v___x_2625_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2683_, v___x_2709_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
lean_inc(v_a_2550_);
v___x_2712_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2584_, v_a_2711_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2712_;
goto v___jp_2562_;
}
else
{
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
return v___x_2710_;
}
}
}
}
}
else
{
lean_del_object(v___x_2631_);
v_a_2558_ = v___x_2584_;
goto v___jp_2557_;
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_del_object(v___x_2631_);
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v_a_2714_ = lean_ctor_get(v___y_2676_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___y_2676_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___y_2676_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___y_2676_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
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
lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; 
lean_dec(v___x_2628_);
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = 0;
lean_inc(v___x_2625_);
lean_inc(v_a_2550_);
v___x_2733_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2541_, v_val_2542_, v_a_2550_, v_next_2546_, v___x_2548_, v___x_2549_, v___x_2548_, v_params_2547_, v___x_2625_, v___x_2731_, v___x_2732_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; uint8_t v___x_2735_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = lean_unbox(v_a_2734_);
lean_dec(v_a_2734_);
if (v___x_2735_ == 0)
{
lean_object* v_toCold_2736_; lean_object* v_options_2737_; uint8_t v_hasTrace_2738_; 
v_toCold_2736_ = lean_ctor_get(v___y_2554_, 0);
v_options_2737_ = lean_ctor_get(v_toCold_2736_, 2);
v_hasTrace_2738_ = lean_ctor_get_uint8(v_options_2737_, sizeof(void*)*1);
if (v_hasTrace_2738_ == 0)
{
goto v___jp_2585_;
}
else
{
lean_object* v_inheritedTraceOptions_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v_inheritedTraceOptions_2739_ = lean_ctor_get(v_toCold_2736_, 11);
v___x_2740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2741_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2739_, v_options_2737_, v___x_2741_);
if (v___x_2742_ == 0)
{
goto v___jp_2585_;
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
lean_inc(v___x_2625_);
v___x_2760_ = l_Lean_MessageData_ofExpr(v___x_2625_);
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
v___x_2766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2584_, v_a_2765_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
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
}
else
{
v_a_2558_ = v___x_2584_;
goto v___jp_2557_;
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec(v_a_2550_);
lean_dec_ref(v_e_2545_);
lean_dec(v_val_2542_);
v_a_2767_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2733_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2733_);
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
v_a_2775_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2626_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2626_);
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
v_a_2783_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2592_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2592_);
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
v___jp_2585_:
{
lean_object* v___x_2586_; 
lean_inc(v_a_2550_);
v___x_2586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2584_, v___x_2584_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2586_;
goto v___jp_2562_;
}
v___jp_2587_:
{
lean_object* v___x_2588_; 
lean_inc(v_a_2550_);
v___x_2588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2584_, v___x_2584_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2588_;
goto v___jp_2562_;
}
v___jp_2589_:
{
lean_object* v___x_2590_; 
lean_inc(v_a_2550_);
v___x_2590_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2541_, v_val_2542_, v_a_2550_, v___x_2584_, v___x_2584_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
v___y_2563_ = v___x_2590_;
goto v___jp_2562_;
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
lean_object* v___x_3052_; lean_object* v_toCold_3053_; lean_object* v_options_3054_; uint8_t v_hasTrace_3055_; 
v___x_3052_ = lean_st_ref_get(v___x_3041_);
lean_dec(v___x_3041_);
v_toCold_3053_ = lean_ctor_get(v_a_3031_, 0);
v_options_3054_ = lean_ctor_get(v_toCold_3053_, 2);
v_hasTrace_3055_ = lean_ctor_get_uint8(v_options_3054_, sizeof(void*)*1);
if (v_hasTrace_3055_ == 0)
{
lean_object* v___x_3057_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3052_);
v___x_3057_ = v___x_3050_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v___x_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_inheritedTraceOptions_3059_ = lean_ctor_get(v_toCold_3053_, 11);
v___x_3060_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3061_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3062_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3059_, v_options_3054_, v___x_3061_);
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
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4197_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4198_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
lean_inc_ref(v_preDefs_4191_);
v___x_4199_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v_value_4203_; lean_object* v___f_4204_; uint8_t v___x_4205_; lean_object* v___x_4206_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = lean_unsigned_to_nat(0u);
v___x_4202_ = lean_array_get(v___x_4197_, v_preDefs_4191_, v___x_4201_);
lean_dec_ref(v_preDefs_4191_);
v_value_4203_ = lean_ctor_get(v___x_4202_, 7);
lean_inc_ref(v_value_4203_);
lean_dec(v___x_4202_);
v___f_4204_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4204_, 0, v_a_4200_);
lean_closure_set(v___f_4204_, 1, v___x_4198_);
lean_closure_set(v___f_4204_, 2, v___x_4201_);
v___x_4205_ = 0;
v___x_4206_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4203_, v___f_4204_, v___x_4205_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
return v___x_4206_;
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v_preDefs_4191_);
v_a_4207_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4199_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4199_);
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
lean_object* v___f_4318_; lean_object* v___x_757__overap_4319_; lean_object* v___x_4320_; 
v___f_4318_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_757__overap_4319_ = lean_panic_fn_borrowed(v___f_4318_, v_msg_4312_);
lean_inc(v___y_4316_);
lean_inc_ref(v___y_4315_);
lean_inc(v___y_4314_);
lean_inc_ref(v___y_4313_);
v___x_4320_ = lean_apply_5(v___x_757__overap_4319_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, lean_box(0));
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
lean_object* v___f_4682_; lean_object* v___x_512__overap_4683_; lean_object* v___x_4684_; 
v___f_4682_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_512__overap_4683_ = lean_panic_fn_borrowed(v___f_4682_, v_msg_4676_);
lean_inc(v___y_4680_);
lean_inc_ref(v___y_4679_);
lean_inc(v___y_4678_);
lean_inc_ref(v___y_4677_);
v___x_4684_ = lean_apply_5(v___x_512__overap_4683_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, lean_box(0));
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
uint8_t v___x_1127__boxed_4900_; uint8_t v___x_1128__boxed_4901_; lean_object* v_res_4902_; 
v___x_1127__boxed_4900_ = lean_unbox(v___x_4891_);
v___x_1128__boxed_4901_ = lean_unbox(v___x_4892_);
v_res_4902_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4888_, v_xs_4889_, v_tail_4890_, v___x_1127__boxed_4900_, v___x_1128__boxed_4901_, v_ys_4893_, v_value_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5009_){
_start:
{
lean_object* v___f_5010_; lean_object* v___f_5011_; lean_object* v___f_5012_; lean_object* v___f_5013_; lean_object* v___f_5014_; lean_object* v___f_5015_; lean_object* v___f_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___f_5010_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5011_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5012_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5013_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5014_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5015_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5016_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5017_, 0, v___f_5010_);
lean_ctor_set(v___x_5017_, 1, v___f_5011_);
v___x_5018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5017_);
lean_ctor_set(v___x_5018_, 1, v___f_5012_);
lean_ctor_set(v___x_5018_, 2, v___f_5013_);
lean_ctor_set(v___x_5018_, 3, v___f_5014_);
lean_ctor_set(v___x_5018_, 4, v___f_5015_);
v___x_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
lean_ctor_set(v___x_5019_, 1, v___f_5016_);
v___x_5020_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5021_ = l_instInhabitedOfMonad___redArg(v___x_5019_, v___x_5020_);
v___x_5022_ = lean_panic_fn_borrowed(v___x_5021_, v_msg_5009_);
lean_dec(v___x_5021_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5023_, lean_object* v_msg_5024_){
_start:
{
lean_object* v___x_5025_; 
v___x_5025_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5024_);
return v___x_5025_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
v___x_5028_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5029_ = lean_unsigned_to_nat(8u);
v___x_5030_ = lean_unsigned_to_nat(394u);
v___x_5031_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5032_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5033_ = l_mkPanicMessageWithDecl(v___x_5032_, v___x_5031_, v___x_5030_, v___x_5029_, v___x_5028_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5034_, lean_object* v_x_5035_){
_start:
{
if (lean_obj_tag(v_x_5034_) == 0)
{
return v_x_5035_;
}
else
{
lean_object* v_head_5036_; lean_object* v_fst_5037_; 
v_head_5036_ = lean_ctor_get(v_x_5034_, 0);
v_fst_5037_ = lean_ctor_get(v_head_5036_, 0);
if (lean_obj_tag(v_fst_5037_) == 0)
{
lean_object* v_tail_5038_; 
v_tail_5038_ = lean_ctor_get(v_x_5034_, 1);
lean_inc(v_tail_5038_);
lean_dec_ref_known(v_x_5034_, 2);
v_x_5034_ = v_tail_5038_;
goto _start;
}
else
{
lean_object* v_tail_5040_; lean_object* v_snd_5041_; lean_object* v_val_5042_; lean_object* v___x_5043_; uint8_t v___x_5044_; 
lean_inc_ref(v_fst_5037_);
lean_inc(v_head_5036_);
v_tail_5040_ = lean_ctor_get(v_x_5034_, 1);
lean_inc(v_tail_5040_);
lean_dec_ref_known(v_x_5034_, 2);
v_snd_5041_ = lean_ctor_get(v_head_5036_, 1);
lean_inc(v_snd_5041_);
lean_dec(v_head_5036_);
v_val_5042_ = lean_ctor_get(v_fst_5037_, 0);
lean_inc(v_val_5042_);
lean_dec_ref_known(v_fst_5037_, 1);
v___x_5043_ = lean_array_get_size(v_x_5035_);
v___x_5044_ = lean_nat_dec_lt(v_val_5042_, v___x_5043_);
if (v___x_5044_ == 0)
{
lean_object* v___x_5045_; lean_object* v___x_5046_; 
lean_dec(v_val_5042_);
lean_dec(v_snd_5041_);
lean_dec(v_tail_5040_);
lean_dec_ref(v_x_5035_);
v___x_5045_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5046_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5045_);
return v___x_5046_;
}
else
{
lean_object* v___x_5047_; 
v___x_5047_ = lean_array_set(v_x_5035_, v_val_5042_, v_snd_5041_);
lean_dec(v_val_5042_);
v_x_5034_ = v_tail_5040_;
v_x_5035_ = v___x_5047_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5049_, lean_object* v_x_5050_, lean_object* v_x_5051_){
_start:
{
lean_object* v___x_5052_; 
v___x_5052_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5050_, v_x_5051_);
return v___x_5052_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5055_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5056_ = lean_unsigned_to_nat(2u);
v___x_5057_ = lean_unsigned_to_nat(384u);
v___x_5058_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5059_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5060_ = l_mkPanicMessageWithDecl(v___x_5059_, v___x_5058_, v___x_5057_, v___x_5056_, v___x_5055_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5063_, lean_object* v_xs_5064_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; uint8_t v___x_5067_; 
v___x_5065_ = lean_array_get_size(v_xs_5064_);
v___x_5066_ = lean_array_get_size(v_perm_5063_);
v___x_5067_ = lean_nat_dec_eq(v___x_5065_, v___x_5066_);
if (v___x_5067_ == 0)
{
lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5068_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5069_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5068_);
return v___x_5069_;
}
else
{
lean_object* v___x_5070_; uint8_t v___x_5071_; 
v___x_5070_ = lean_unsigned_to_nat(0u);
v___x_5071_ = lean_nat_dec_eq(v___x_5065_, v___x_5070_);
if (v___x_5071_ == 0)
{
lean_object* v_dummy_5072_; lean_object* v___x_5073_; lean_object* v_ys_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v_dummy_5072_ = lean_array_fget_borrowed(v_xs_5064_, v___x_5070_);
v___x_5073_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5063_);
lean_inc(v_dummy_5072_);
v_ys_5074_ = lean_mk_array(v___x_5073_, v_dummy_5072_);
v___x_5075_ = l_Array_zip___redArg(v_perm_5063_, v_xs_5064_);
v___x_5076_ = lean_array_to_list(v___x_5075_);
v___x_5077_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5076_, v_ys_5074_);
return v___x_5077_;
}
else
{
lean_object* v___x_5078_; 
v___x_5078_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5079_, lean_object* v_xs_5080_){
_start:
{
lean_object* v_res_5081_; 
v_res_5081_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5079_, v_xs_5080_);
lean_dec_ref(v_xs_5080_);
lean_dec_ref(v_perm_5079_);
return v_res_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5082_, lean_object* v_perm_5083_, lean_object* v_xs_5084_){
_start:
{
lean_object* v___x_5085_; 
v___x_5085_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5083_, v_xs_5084_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5086_, lean_object* v_perm_5087_, lean_object* v_xs_5088_){
_start:
{
lean_object* v_res_5089_; 
v_res_5089_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5086_, v_perm_5087_, v_xs_5088_);
lean_dec_ref(v_xs_5088_);
lean_dec_ref(v_perm_5087_);
return v_res_5089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5090_, lean_object* v_upperBound_5091_, lean_object* v_perm_5092_, lean_object* v_a_5093_, lean_object* v_b_5094_){
_start:
{
lean_object* v_a_5096_; uint8_t v___x_5103_; 
v___x_5103_ = lean_nat_dec_lt(v_a_5093_, v_upperBound_5091_);
if (v___x_5103_ == 0)
{
lean_dec(v_a_5093_);
return v_b_5094_;
}
else
{
lean_object* v___x_5104_; uint8_t v___x_5105_; 
v___x_5104_ = lean_array_get_size(v_perm_5092_);
v___x_5105_ = lean_nat_dec_lt(v_a_5093_, v___x_5104_);
if (v___x_5105_ == 0)
{
goto v___jp_5100_;
}
else
{
lean_object* v___x_5106_; 
v___x_5106_ = lean_array_fget_borrowed(v_perm_5092_, v_a_5093_);
if (lean_obj_tag(v___x_5106_) == 0)
{
goto v___jp_5100_;
}
else
{
v_a_5096_ = v_b_5094_;
goto v___jp_5095_;
}
}
}
v___jp_5095_:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = lean_unsigned_to_nat(1u);
v___x_5098_ = lean_nat_add(v_a_5093_, v___x_5097_);
lean_dec(v_a_5093_);
v_a_5093_ = v___x_5098_;
v_b_5094_ = v_a_5096_;
goto _start;
}
v___jp_5100_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5101_ = lean_array_fget_borrowed(v_xs_5090_, v_a_5093_);
lean_inc(v___x_5101_);
v___x_5102_ = lean_array_push(v_b_5094_, v___x_5101_);
v_a_5096_ = v___x_5102_;
goto v___jp_5095_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5107_, lean_object* v_upperBound_5108_, lean_object* v_perm_5109_, lean_object* v_a_5110_, lean_object* v_b_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5107_, v_upperBound_5108_, v_perm_5109_, v_a_5110_, v_b_5111_);
lean_dec_ref(v_perm_5109_);
lean_dec(v_upperBound_5108_);
lean_dec_ref(v_xs_5107_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5113_, lean_object* v_xs_5114_){
_start:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v_ys_5117_; lean_object* v___x_5118_; 
v___x_5115_ = lean_array_get_size(v_xs_5114_);
v___x_5116_ = lean_unsigned_to_nat(0u);
v_ys_5117_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5118_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5114_, v___x_5115_, v_perm_5113_, v___x_5116_, v_ys_5117_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5119_, lean_object* v_xs_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5119_, v_xs_5120_);
lean_dec_ref(v_xs_5120_);
lean_dec_ref(v_perm_5119_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5122_, lean_object* v_perm_5123_, lean_object* v_xs_5124_){
_start:
{
lean_object* v___x_5125_; 
v___x_5125_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5123_, v_xs_5124_);
return v___x_5125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5126_, lean_object* v_perm_5127_, lean_object* v_xs_5128_){
_start:
{
lean_object* v_res_5129_; 
v_res_5129_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5126_, v_perm_5127_, v_xs_5128_);
lean_dec_ref(v_xs_5128_);
lean_dec_ref(v_perm_5127_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5130_, lean_object* v_xs_5131_, lean_object* v_upperBound_5132_, lean_object* v_perm_5133_, lean_object* v_inst_5134_, lean_object* v_R_5135_, lean_object* v_a_5136_, lean_object* v_b_5137_, lean_object* v_c_5138_){
_start:
{
lean_object* v___x_5139_; 
v___x_5139_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5131_, v_upperBound_5132_, v_perm_5133_, v_a_5136_, v_b_5137_);
return v___x_5139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5140_, lean_object* v_xs_5141_, lean_object* v_upperBound_5142_, lean_object* v_perm_5143_, lean_object* v_inst_5144_, lean_object* v_R_5145_, lean_object* v_a_5146_, lean_object* v_b_5147_, lean_object* v_c_5148_){
_start:
{
lean_object* v_res_5149_; 
v_res_5149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5140_, v_xs_5141_, v_upperBound_5142_, v_perm_5143_, v_inst_5144_, v_R_5145_, v_a_5146_, v_b_5147_, v_c_5148_);
lean_dec_ref(v_perm_5143_);
lean_dec(v_upperBound_5142_);
lean_dec_ref(v_xs_5141_);
return v_res_5149_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5150_){
_start:
{
lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5151_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5152_ = lean_panic_fn_borrowed(v___x_5151_, v_msg_5150_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5153_, lean_object* v_msg_5154_){
_start:
{
lean_object* v___x_5155_; 
v___x_5155_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5154_);
return v___x_5155_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5156_, lean_object* v___x_5157_, lean_object* v_i_5158_, lean_object* v___x_5159_, lean_object* v_as_5160_, size_t v_i_5161_, size_t v_stop_5162_){
_start:
{
uint8_t v___x_5163_; 
v___x_5163_ = lean_usize_dec_eq(v_i_5161_, v_stop_5162_);
if (v___x_5163_ == 0)
{
uint8_t v___x_5164_; uint8_t v___y_5166_; lean_object* v___x_5170_; 
v___x_5164_ = 1;
v___x_5170_ = lean_array_uget_borrowed(v_as_5160_, v_i_5161_);
if (lean_obj_tag(v___x_5170_) == 0)
{
uint8_t v___x_5171_; 
v___x_5171_ = lean_nat_dec_lt(v_j_5156_, v___x_5157_);
v___y_5166_ = v___x_5171_;
goto v___jp_5165_;
}
else
{
uint8_t v___x_5172_; 
v___x_5172_ = lean_nat_dec_lt(v_i_5158_, v___x_5159_);
v___y_5166_ = v___x_5172_;
goto v___jp_5165_;
}
v___jp_5165_:
{
if (v___y_5166_ == 0)
{
size_t v___x_5167_; size_t v___x_5168_; 
v___x_5167_ = ((size_t)1ULL);
v___x_5168_ = lean_usize_add(v_i_5161_, v___x_5167_);
v_i_5161_ = v___x_5168_;
goto _start;
}
else
{
return v___x_5164_;
}
}
}
else
{
uint8_t v___x_5173_; 
v___x_5173_ = 0;
return v___x_5173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5174_, lean_object* v___x_5175_, lean_object* v_i_5176_, lean_object* v___x_5177_, lean_object* v_as_5178_, lean_object* v_i_5179_, lean_object* v_stop_5180_){
_start:
{
size_t v_i_boxed_5181_; size_t v_stop_boxed_5182_; uint8_t v_res_5183_; lean_object* v_r_5184_; 
v_i_boxed_5181_ = lean_unbox_usize(v_i_5179_);
lean_dec(v_i_5179_);
v_stop_boxed_5182_ = lean_unbox_usize(v_stop_5180_);
lean_dec(v_stop_5180_);
v_res_5183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5174_, v___x_5175_, v_i_5176_, v___x_5177_, v_as_5178_, v_i_boxed_5181_, v_stop_boxed_5182_);
lean_dec_ref(v_as_5178_);
lean_dec(v___x_5177_);
lean_dec(v_i_5176_);
lean_dec(v___x_5175_);
lean_dec(v_j_5174_);
v_r_5184_ = lean_box(v_res_5183_);
return v_r_5184_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5188_ = lean_unsigned_to_nat(10u);
v___x_5189_ = lean_unsigned_to_nat(425u);
v___x_5190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5191_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5192_ = l_mkPanicMessageWithDecl(v___x_5191_, v___x_5190_, v___x_5189_, v___x_5188_, v___x_5187_);
return v___x_5192_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5194_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5195_ = lean_unsigned_to_nat(12u);
v___x_5196_ = lean_unsigned_to_nat(433u);
v___x_5197_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5199_ = l_mkPanicMessageWithDecl(v___x_5198_, v___x_5197_, v___x_5196_, v___x_5195_, v___x_5194_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5200_, lean_object* v_fixedArgs_5201_, lean_object* v_varyingArgs_5202_, lean_object* v_i_5203_, lean_object* v_j_5204_, lean_object* v_xs_5205_){
_start:
{
lean_object* v_lower_5207_; lean_object* v_upper_5208_; lean_object* v___x_5212_; uint8_t v___x_5213_; 
v___x_5212_ = lean_array_get_size(v_perm_5200_);
v___x_5213_ = lean_nat_dec_lt(v_i_5203_, v___x_5212_);
if (v___x_5213_ == 0)
{
lean_object* v___x_5214_; lean_object* v___x_5215_; uint8_t v___x_5216_; 
lean_dec(v_i_5203_);
lean_dec_ref(v_perm_5200_);
v___x_5214_ = lean_unsigned_to_nat(0u);
v___x_5215_ = lean_array_get_size(v_varyingArgs_5202_);
v___x_5216_ = lean_nat_dec_le(v_j_5204_, v___x_5214_);
if (v___x_5216_ == 0)
{
v_lower_5207_ = v_j_5204_;
v_upper_5208_ = v___x_5215_;
goto v___jp_5206_;
}
else
{
lean_dec(v_j_5204_);
v_lower_5207_ = v___x_5214_;
v_upper_5208_ = v___x_5215_;
goto v___jp_5206_;
}
}
else
{
lean_object* v___x_5217_; 
v___x_5217_ = lean_array_fget_borrowed(v_perm_5200_, v_i_5203_);
if (lean_obj_tag(v___x_5217_) == 1)
{
lean_object* v_val_5218_; lean_object* v___x_5219_; uint8_t v___x_5220_; 
v_val_5218_ = lean_ctor_get(v___x_5217_, 0);
v___x_5219_ = lean_array_get_size(v_fixedArgs_5201_);
v___x_5220_ = lean_nat_dec_lt(v_val_5218_, v___x_5219_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; lean_object* v___x_5222_; 
lean_dec_ref(v_xs_5205_);
lean_dec(v_j_5204_);
lean_dec(v_i_5203_);
lean_dec_ref(v_varyingArgs_5202_);
lean_dec_ref(v_perm_5200_);
v___x_5221_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5222_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5221_);
return v___x_5222_;
}
else
{
lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v___x_5223_ = lean_unsigned_to_nat(1u);
v___x_5224_ = lean_nat_add(v_i_5203_, v___x_5223_);
lean_dec(v_i_5203_);
v___x_5225_ = lean_array_fget_borrowed(v_fixedArgs_5201_, v_val_5218_);
lean_inc(v___x_5225_);
v___x_5226_ = lean_array_push(v_xs_5205_, v___x_5225_);
v_i_5203_ = v___x_5224_;
v_xs_5205_ = v___x_5226_;
goto _start;
}
}
else
{
lean_object* v___x_5228_; lean_object* v___y_5230_; lean_object* v___y_5231_; lean_object* v___y_5232_; lean_object* v_lower_5240_; lean_object* v_upper_5241_; uint8_t v___x_5249_; 
v___x_5228_ = lean_array_get_size(v_varyingArgs_5202_);
v___x_5249_ = lean_nat_dec_lt(v_j_5204_, v___x_5228_);
if (v___x_5249_ == 0)
{
lean_object* v___x_5250_; uint8_t v___x_5251_; 
lean_dec_ref(v_varyingArgs_5202_);
v___x_5250_ = lean_unsigned_to_nat(0u);
v___x_5251_ = lean_nat_dec_le(v_i_5203_, v___x_5250_);
if (v___x_5251_ == 0)
{
lean_inc(v_i_5203_);
v_lower_5240_ = v_i_5203_;
v_upper_5241_ = v___x_5212_;
goto v___jp_5239_;
}
else
{
v_lower_5240_ = v___x_5250_;
v_upper_5241_ = v___x_5212_;
goto v___jp_5239_;
}
}
else
{
lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; 
v___x_5252_ = lean_unsigned_to_nat(1u);
v___x_5253_ = lean_nat_add(v_i_5203_, v___x_5252_);
lean_dec(v_i_5203_);
v___x_5254_ = lean_nat_add(v_j_5204_, v___x_5252_);
v___x_5255_ = lean_array_fget_borrowed(v_varyingArgs_5202_, v_j_5204_);
lean_dec(v_j_5204_);
lean_inc(v___x_5255_);
v___x_5256_ = lean_array_push(v_xs_5205_, v___x_5255_);
v_i_5203_ = v___x_5253_;
v_j_5204_ = v___x_5254_;
v_xs_5205_ = v___x_5256_;
goto _start;
}
v___jp_5229_:
{
uint8_t v___x_5233_; 
v___x_5233_ = lean_nat_dec_lt(v___y_5230_, v___y_5232_);
if (v___x_5233_ == 0)
{
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
lean_dec(v___y_5230_);
lean_dec(v_j_5204_);
lean_dec(v_i_5203_);
return v_xs_5205_;
}
else
{
size_t v___x_5234_; size_t v___x_5235_; uint8_t v___x_5236_; 
v___x_5234_ = lean_usize_of_nat(v___y_5230_);
lean_dec(v___y_5230_);
v___x_5235_ = lean_usize_of_nat(v___y_5232_);
lean_dec(v___y_5232_);
v___x_5236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5204_, v___x_5228_, v_i_5203_, v___x_5212_, v___y_5231_, v___x_5234_, v___x_5235_);
lean_dec_ref(v___y_5231_);
lean_dec(v_i_5203_);
lean_dec(v_j_5204_);
if (v___x_5236_ == 0)
{
return v_xs_5205_;
}
else
{
lean_object* v___x_5237_; lean_object* v___x_5238_; 
lean_dec_ref(v_xs_5205_);
v___x_5237_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5238_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5237_);
return v___x_5238_;
}
}
}
v___jp_5239_:
{
lean_object* v___x_5242_; lean_object* v_array_5243_; lean_object* v_start_5244_; lean_object* v_stop_5245_; uint8_t v___x_5246_; 
v___x_5242_ = l_Array_toSubarray___redArg(v_perm_5200_, v_lower_5240_, v_upper_5241_);
v_array_5243_ = lean_ctor_get(v___x_5242_, 0);
lean_inc_ref(v_array_5243_);
v_start_5244_ = lean_ctor_get(v___x_5242_, 1);
lean_inc(v_start_5244_);
v_stop_5245_ = lean_ctor_get(v___x_5242_, 2);
lean_inc(v_stop_5245_);
lean_dec_ref(v___x_5242_);
v___x_5246_ = lean_nat_dec_lt(v_start_5244_, v_stop_5245_);
if (v___x_5246_ == 0)
{
lean_dec(v_stop_5245_);
lean_dec(v_start_5244_);
lean_dec_ref(v_array_5243_);
lean_dec(v_j_5204_);
lean_dec(v_i_5203_);
return v_xs_5205_;
}
else
{
lean_object* v___x_5247_; uint8_t v___x_5248_; 
v___x_5247_ = lean_array_get_size(v_array_5243_);
v___x_5248_ = lean_nat_dec_le(v_stop_5245_, v___x_5247_);
if (v___x_5248_ == 0)
{
lean_dec(v_stop_5245_);
v___y_5230_ = v_start_5244_;
v___y_5231_ = v_array_5243_;
v___y_5232_ = v___x_5247_;
goto v___jp_5229_;
}
else
{
v___y_5230_ = v_start_5244_;
v___y_5231_ = v_array_5243_;
v___y_5232_ = v_stop_5245_;
goto v___jp_5229_;
}
}
}
}
}
v___jp_5206_:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; 
v___x_5209_ = l_Array_toSubarray___redArg(v_varyingArgs_5202_, v_lower_5207_, v_upper_5208_);
v___x_5210_ = l_Subarray_copy___redArg(v___x_5209_);
v___x_5211_ = l_Array_append___redArg(v_xs_5205_, v___x_5210_);
lean_dec_ref(v___x_5210_);
return v___x_5211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5258_, lean_object* v_fixedArgs_5259_, lean_object* v_varyingArgs_5260_, lean_object* v_i_5261_, lean_object* v_j_5262_, lean_object* v_xs_5263_){
_start:
{
lean_object* v_res_5264_; 
v_res_5264_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5258_, v_fixedArgs_5259_, v_varyingArgs_5260_, v_i_5261_, v_j_5262_, v_xs_5263_);
lean_dec_ref(v_fixedArgs_5259_);
return v_res_5264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5265_, lean_object* v_perm_5266_, lean_object* v_fixedArgs_5267_, lean_object* v_varyingArgs_5268_, lean_object* v_i_5269_, lean_object* v_j_5270_, lean_object* v_xs_5271_){
_start:
{
lean_object* v___x_5272_; 
v___x_5272_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5266_, v_fixedArgs_5267_, v_varyingArgs_5268_, v_i_5269_, v_j_5270_, v_xs_5271_);
return v___x_5272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5273_, lean_object* v_perm_5274_, lean_object* v_fixedArgs_5275_, lean_object* v_varyingArgs_5276_, lean_object* v_i_5277_, lean_object* v_j_5278_, lean_object* v_xs_5279_){
_start:
{
lean_object* v_res_5280_; 
v_res_5280_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5273_, v_perm_5274_, v_fixedArgs_5275_, v_varyingArgs_5276_, v_i_5277_, v_j_5278_, v_xs_5279_);
lean_dec_ref(v_fixedArgs_5275_);
return v_res_5280_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5283_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5284_ = lean_unsigned_to_nat(2u);
v___x_5285_ = lean_unsigned_to_nat(416u);
v___x_5286_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5287_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5288_ = l_mkPanicMessageWithDecl(v___x_5287_, v___x_5286_, v___x_5285_, v___x_5284_, v___x_5283_);
return v___x_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5289_, lean_object* v_fixedArgs_5290_, lean_object* v_varyingArgs_5291_){
_start:
{
lean_object* v___x_5292_; lean_object* v___x_5293_; uint8_t v___x_5294_; 
v___x_5292_ = lean_array_get_size(v_fixedArgs_5290_);
v___x_5293_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5289_);
v___x_5294_ = lean_nat_dec_eq(v___x_5292_, v___x_5293_);
lean_dec(v___x_5293_);
if (v___x_5294_ == 0)
{
lean_object* v___x_5295_; lean_object* v___x_5296_; 
lean_dec_ref(v_varyingArgs_5291_);
lean_dec_ref(v_perm_5289_);
v___x_5295_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5296_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5295_);
return v___x_5296_;
}
else
{
lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5297_ = lean_unsigned_to_nat(0u);
v___x_5298_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5299_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5289_, v_fixedArgs_5290_, v_varyingArgs_5291_, v___x_5297_, v___x_5297_, v___x_5298_);
return v___x_5299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5300_, lean_object* v_fixedArgs_5301_, lean_object* v_varyingArgs_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5300_, v_fixedArgs_5301_, v_varyingArgs_5302_);
lean_dec_ref(v_fixedArgs_5301_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5304_, lean_object* v_perm_5305_, lean_object* v_fixedArgs_5306_, lean_object* v_varyingArgs_5307_){
_start:
{
lean_object* v___x_5308_; 
v___x_5308_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5305_, v_fixedArgs_5306_, v_varyingArgs_5307_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5309_, lean_object* v_perm_5310_, lean_object* v_fixedArgs_5311_, lean_object* v_varyingArgs_5312_){
_start:
{
lean_object* v_res_5313_; 
v_res_5313_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5309_, v_perm_5310_, v_fixedArgs_5311_, v_varyingArgs_5312_);
lean_dec_ref(v_fixedArgs_5311_);
return v_res_5313_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5314_, lean_object* v_x_5315_){
_start:
{
if (lean_obj_tag(v_x_5314_) == 0)
{
if (lean_obj_tag(v_x_5315_) == 0)
{
uint8_t v___x_5316_; 
v___x_5316_ = 1;
return v___x_5316_;
}
else
{
uint8_t v___x_5317_; 
v___x_5317_ = 0;
return v___x_5317_;
}
}
else
{
if (lean_obj_tag(v_x_5315_) == 0)
{
uint8_t v___x_5318_; 
v___x_5318_ = 0;
return v___x_5318_;
}
else
{
lean_object* v_val_5319_; lean_object* v_val_5320_; uint8_t v___x_5321_; 
v_val_5319_ = lean_ctor_get(v_x_5314_, 0);
v_val_5320_ = lean_ctor_get(v_x_5315_, 0);
v___x_5321_ = lean_nat_dec_eq(v_val_5319_, v_val_5320_);
return v___x_5321_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5322_, lean_object* v_x_5323_){
_start:
{
uint8_t v_res_5324_; lean_object* v_r_5325_; 
v_res_5324_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5322_, v_x_5323_);
lean_dec(v_x_5323_);
lean_dec(v_x_5322_);
v_r_5325_ = lean_box(v_res_5324_);
return v_r_5325_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5326_, lean_object* v_ys_5327_, lean_object* v_x_5328_){
_start:
{
lean_object* v_zero_5329_; uint8_t v_isZero_5330_; 
v_zero_5329_ = lean_unsigned_to_nat(0u);
v_isZero_5330_ = lean_nat_dec_eq(v_x_5328_, v_zero_5329_);
if (v_isZero_5330_ == 1)
{
lean_dec(v_x_5328_);
return v_isZero_5330_;
}
else
{
lean_object* v_one_5331_; lean_object* v_n_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; uint8_t v___x_5335_; 
v_one_5331_ = lean_unsigned_to_nat(1u);
v_n_5332_ = lean_nat_sub(v_x_5328_, v_one_5331_);
lean_dec(v_x_5328_);
v___x_5333_ = lean_array_fget_borrowed(v_xs_5326_, v_n_5332_);
v___x_5334_ = lean_array_fget_borrowed(v_ys_5327_, v_n_5332_);
v___x_5335_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5333_, v___x_5334_);
if (v___x_5335_ == 0)
{
lean_dec(v_n_5332_);
return v___x_5335_;
}
else
{
v_x_5328_ = v_n_5332_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5337_, lean_object* v_ys_5338_, lean_object* v_x_5339_){
_start:
{
uint8_t v_res_5340_; lean_object* v_r_5341_; 
v_res_5340_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5337_, v_ys_5338_, v_x_5339_);
lean_dec_ref(v_ys_5338_);
lean_dec_ref(v_xs_5337_);
v_r_5341_ = lean_box(v_res_5340_);
return v_r_5341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5342_, size_t v_i_5343_, lean_object* v_bs_5344_){
_start:
{
uint8_t v___x_5345_; 
v___x_5345_ = lean_usize_dec_lt(v_i_5343_, v_sz_5342_);
if (v___x_5345_ == 0)
{
return v_bs_5344_;
}
else
{
lean_object* v_v_5346_; lean_object* v___x_5347_; lean_object* v_bs_x27_5348_; lean_object* v___x_5349_; size_t v___x_5350_; size_t v___x_5351_; lean_object* v___x_5352_; 
v_v_5346_ = lean_array_uget(v_bs_5344_, v_i_5343_);
v___x_5347_ = lean_unsigned_to_nat(0u);
v_bs_x27_5348_ = lean_array_uset(v_bs_5344_, v_i_5343_, v___x_5347_);
v___x_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5349_, 0, v_v_5346_);
v___x_5350_ = ((size_t)1ULL);
v___x_5351_ = lean_usize_add(v_i_5343_, v___x_5350_);
v___x_5352_ = lean_array_uset(v_bs_x27_5348_, v_i_5343_, v___x_5349_);
v_i_5343_ = v___x_5351_;
v_bs_5344_ = v___x_5352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5354_, lean_object* v_i_5355_, lean_object* v_bs_5356_){
_start:
{
size_t v_sz_boxed_5357_; size_t v_i_boxed_5358_; lean_object* v_res_5359_; 
v_sz_boxed_5357_ = lean_unbox_usize(v_sz_5354_);
lean_dec(v_sz_5354_);
v_i_boxed_5358_ = lean_unbox_usize(v_i_5355_);
lean_dec(v_i_5355_);
v_res_5359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5357_, v_i_boxed_5358_, v_bs_5356_);
return v_res_5359_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5360_, lean_object* v_as_5361_, size_t v_i_5362_, size_t v_stop_5363_){
_start:
{
uint8_t v___x_5364_; 
v___x_5364_ = lean_usize_dec_eq(v_i_5362_, v_stop_5363_);
if (v___x_5364_ == 0)
{
lean_object* v_numFixed_5365_; uint8_t v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; size_t v_sz_5369_; size_t v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; uint8_t v___x_5378_; 
v_numFixed_5365_ = lean_ctor_get(v_fixedParamPerms_5360_, 0);
v___x_5366_ = 1;
v___x_5367_ = lean_array_uget_borrowed(v_as_5361_, v_i_5362_);
lean_inc(v_numFixed_5365_);
v___x_5368_ = l_Array_range(v_numFixed_5365_);
v_sz_5369_ = lean_array_size(v___x_5368_);
v___x_5370_ = ((size_t)0ULL);
v___x_5371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5369_, v___x_5370_, v___x_5368_);
v___x_5372_ = lean_array_get_size(v___x_5367_);
v___x_5373_ = lean_nat_sub(v___x_5372_, v_numFixed_5365_);
v___x_5374_ = lean_box(0);
v___x_5375_ = lean_mk_array(v___x_5373_, v___x_5374_);
v___x_5376_ = l_Array_append___redArg(v___x_5371_, v___x_5375_);
lean_dec_ref(v___x_5375_);
v___x_5377_ = lean_array_get_size(v___x_5376_);
v___x_5378_ = lean_nat_dec_eq(v___x_5372_, v___x_5377_);
if (v___x_5378_ == 0)
{
lean_dec_ref(v___x_5376_);
lean_dec_ref(v_fixedParamPerms_5360_);
return v___x_5366_;
}
else
{
uint8_t v___x_5379_; 
v___x_5379_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5367_, v___x_5376_, v___x_5372_);
lean_dec_ref(v___x_5376_);
if (v___x_5379_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5360_);
return v___x_5366_;
}
else
{
size_t v___x_5380_; size_t v___x_5381_; 
v___x_5380_ = ((size_t)1ULL);
v___x_5381_ = lean_usize_add(v_i_5362_, v___x_5380_);
v_i_5362_ = v___x_5381_;
goto _start;
}
}
}
else
{
uint8_t v___x_5383_; 
lean_dec_ref(v_fixedParamPerms_5360_);
v___x_5383_ = 0;
return v___x_5383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5384_, lean_object* v_as_5385_, lean_object* v_i_5386_, lean_object* v_stop_5387_){
_start:
{
size_t v_i_boxed_5388_; size_t v_stop_boxed_5389_; uint8_t v_res_5390_; lean_object* v_r_5391_; 
v_i_boxed_5388_ = lean_unbox_usize(v_i_5386_);
lean_dec(v_i_5386_);
v_stop_boxed_5389_ = lean_unbox_usize(v_stop_5387_);
lean_dec(v_stop_5387_);
v_res_5390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5384_, v_as_5385_, v_i_boxed_5388_, v_stop_boxed_5389_);
lean_dec_ref(v_as_5385_);
v_r_5391_ = lean_box(v_res_5390_);
return v_r_5391_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5392_){
_start:
{
lean_object* v_perms_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; uint8_t v___x_5396_; 
v_perms_5393_ = lean_ctor_get(v_fixedParamPerms_5392_, 1);
lean_inc_ref(v_perms_5393_);
v___x_5394_ = lean_unsigned_to_nat(0u);
v___x_5395_ = lean_array_get_size(v_perms_5393_);
v___x_5396_ = lean_nat_dec_lt(v___x_5394_, v___x_5395_);
if (v___x_5396_ == 0)
{
uint8_t v___x_5397_; 
lean_dec_ref(v_perms_5393_);
lean_dec_ref(v_fixedParamPerms_5392_);
v___x_5397_ = 1;
return v___x_5397_;
}
else
{
if (v___x_5396_ == 0)
{
lean_dec_ref(v_perms_5393_);
lean_dec_ref(v_fixedParamPerms_5392_);
return v___x_5396_;
}
else
{
size_t v___x_5398_; size_t v___x_5399_; uint8_t v___x_5400_; 
v___x_5398_ = ((size_t)0ULL);
v___x_5399_ = lean_usize_of_nat(v___x_5395_);
v___x_5400_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5392_, v_perms_5393_, v___x_5398_, v___x_5399_);
lean_dec_ref(v_perms_5393_);
if (v___x_5400_ == 0)
{
return v___x_5396_;
}
else
{
uint8_t v___x_5401_; 
v___x_5401_ = 0;
return v___x_5401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5402_){
_start:
{
uint8_t v_res_5403_; lean_object* v_r_5404_; 
v_res_5403_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5402_);
v_r_5404_ = lean_box(v_res_5403_);
return v_r_5404_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5405_, lean_object* v_ys_5406_, lean_object* v_hsz_5407_, lean_object* v_x_5408_, lean_object* v_x_5409_){
_start:
{
uint8_t v___x_5410_; 
v___x_5410_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5405_, v_ys_5406_, v_x_5408_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5411_, lean_object* v_ys_5412_, lean_object* v_hsz_5413_, lean_object* v_x_5414_, lean_object* v_x_5415_){
_start:
{
uint8_t v_res_5416_; lean_object* v_r_5417_; 
v_res_5416_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5411_, v_ys_5412_, v_hsz_5413_, v_x_5414_, v_x_5415_);
lean_dec_ref(v_ys_5412_);
lean_dec_ref(v_xs_5411_);
v_r_5417_ = lean_box(v_res_5416_);
return v_r_5417_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5418_);
lean_ctor_set(v___x_5419_, 1, v___x_5418_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5420_){
_start:
{
lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___f_5423_; lean_object* v___f_5424_; lean_object* v___f_5425_; lean_object* v___f_5426_; lean_object* v___f_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
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
lean_ctor_set(v___x_5433_, 0, v___x_5431_);
lean_ctor_set(v___x_5433_, 1, v___x_5432_);
v___x_5434_ = l_instInhabitedOfMonad___redArg(v___x_5430_, v___x_5433_);
v___x_5435_ = lean_panic_fn_borrowed(v___x_5434_, v_msg_5420_);
lean_dec(v___x_5434_);
return v___x_5435_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5436_; lean_object* v___x_5437_; 
v___x_5436_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5436_);
return v___x_5437_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5438_){
_start:
{
lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___f_5441_; lean_object* v___f_5442_; lean_object* v___f_5443_; lean_object* v___f_5444_; lean_object* v___f_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; 
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
v___x_5450_ = l_instInhabitedOfMonad___redArg(v___x_5448_, v___x_5449_);
v___x_5451_ = lean_panic_fn_borrowed(v___x_5450_, v_msg_5438_);
lean_dec(v___x_5450_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5452_, lean_object* v___x_5453_, lean_object* v___x_5454_, lean_object* v_as_5455_, size_t v_sz_5456_, size_t v_i_5457_, lean_object* v_b_5458_){
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
lean_object* v_fst_5465_; lean_object* v_snd_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5491_; 
v_fst_5465_ = lean_ctor_get(v_b_5458_, 0);
v_snd_5466_ = lean_ctor_get(v_b_5458_, 1);
v_isSharedCheck_5491_ = !lean_is_exclusive(v_b_5458_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5468_ = v_b_5458_;
v_isShared_5469_ = v_isSharedCheck_5491_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_snd_5466_);
lean_inc(v_fst_5465_);
lean_dec(v_b_5458_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5491_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5470_; lean_object* v_a_5471_; lean_object* v___x_5472_; 
v___x_5470_ = lean_box(0);
v_a_5471_ = lean_array_uget_borrowed(v_as_5455_, v_i_5457_);
v___x_5472_ = lean_array_get_borrowed(v___x_5470_, v___x_5452_, v_a_5471_);
if (lean_obj_tag(v___x_5472_) == 1)
{
lean_object* v_val_5473_; uint8_t v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; uint8_t v___x_5477_; 
v_val_5473_ = lean_ctor_get(v___x_5472_, 0);
v___x_5474_ = 0;
v___x_5475_ = lean_box(v___x_5474_);
v___x_5476_ = lean_array_get(v___x_5475_, v_fst_5465_, v_val_5473_);
lean_dec(v___x_5475_);
v___x_5477_ = lean_unbox(v___x_5476_);
lean_dec(v___x_5476_);
if (v___x_5477_ == 0)
{
uint8_t v_changed_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5483_; 
lean_dec(v_snd_5466_);
v_changed_5478_ = lean_nat_dec_eq(v___x_5453_, v___x_5454_);
v___x_5479_ = lean_box(v_changed_5478_);
v___x_5480_ = lean_array_set(v_fst_5465_, v_val_5473_, v___x_5479_);
v___x_5481_ = lean_box(v_changed_5478_);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 1, v___x_5481_);
lean_ctor_set(v___x_5468_, 0, v___x_5480_);
v___x_5483_ = v___x_5468_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5480_);
lean_ctor_set(v_reuseFailAlloc_5484_, 1, v___x_5481_);
v___x_5483_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
v_a_5460_ = v___x_5483_;
goto v___jp_5459_;
}
}
else
{
lean_object* v___x_5486_; 
if (v_isShared_5469_ == 0)
{
v___x_5486_ = v___x_5468_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_fst_5465_);
lean_ctor_set(v_reuseFailAlloc_5487_, 1, v_snd_5466_);
v___x_5486_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
v_a_5460_ = v___x_5486_;
goto v___jp_5459_;
}
}
}
else
{
lean_object* v___x_5489_; 
if (v_isShared_5469_ == 0)
{
v___x_5489_ = v___x_5468_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_fst_5465_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v_snd_5466_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
v_a_5460_ = v___x_5489_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5492_, lean_object* v___x_5493_, lean_object* v___x_5494_, lean_object* v_as_5495_, lean_object* v_sz_5496_, lean_object* v_i_5497_, lean_object* v_b_5498_){
_start:
{
size_t v_sz_boxed_5499_; size_t v_i_boxed_5500_; lean_object* v_res_5501_; 
v_sz_boxed_5499_ = lean_unbox_usize(v_sz_5496_);
lean_dec(v_sz_5496_);
v_i_boxed_5500_ = lean_unbox_usize(v_i_5497_);
lean_dec(v_i_5497_);
v_res_5501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5492_, v___x_5493_, v___x_5494_, v_as_5495_, v_sz_boxed_5499_, v_i_boxed_5500_, v_b_5498_);
lean_dec_ref(v_as_5495_);
lean_dec(v___x_5494_);
lean_dec(v___x_5493_);
lean_dec_ref(v___x_5492_);
return v_res_5501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5502_, lean_object* v___x_5503_, lean_object* v_fixedParamPerms_5504_, lean_object* v_next_5505_, lean_object* v___x_5506_, lean_object* v___x_5507_, lean_object* v_a_5508_, lean_object* v_b_5509_){
_start:
{
lean_object* v_a_5511_; uint8_t v___x_5515_; 
v___x_5515_ = lean_nat_dec_lt(v_a_5508_, v_upperBound_5502_);
if (v___x_5515_ == 0)
{
lean_dec(v_a_5508_);
return v_b_5509_;
}
else
{
lean_object* v_fst_5516_; lean_object* v_snd_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5552_; 
v_fst_5516_ = lean_ctor_get(v_b_5509_, 0);
v_snd_5517_ = lean_ctor_get(v_b_5509_, 1);
v_isSharedCheck_5552_ = !lean_is_exclusive(v_b_5509_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5519_ = v_b_5509_;
v_isShared_5520_ = v_isSharedCheck_5552_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_snd_5517_);
lean_inc(v_fst_5516_);
lean_dec(v_b_5509_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5552_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; 
v___x_5521_ = lean_array_fget_borrowed(v___x_5503_, v_a_5508_);
if (lean_obj_tag(v___x_5521_) == 1)
{
lean_object* v_val_5522_; uint8_t v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; uint8_t v___x_5526_; 
v_val_5522_ = lean_ctor_get(v___x_5521_, 0);
v___x_5523_ = 0;
v___x_5524_ = lean_box(v___x_5523_);
v___x_5525_ = lean_array_get(v___x_5524_, v_fst_5516_, v_val_5522_);
lean_dec(v___x_5524_);
v___x_5526_ = lean_unbox(v___x_5525_);
lean_dec(v___x_5525_);
if (v___x_5526_ == 0)
{
lean_object* v___x_5528_; 
if (v_isShared_5520_ == 0)
{
v___x_5528_ = v___x_5519_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_fst_5516_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_snd_5517_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
v_a_5511_ = v___x_5528_;
goto v___jp_5510_;
}
}
else
{
lean_object* v_revDeps_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5535_; 
v_revDeps_5530_ = lean_ctor_get(v_fixedParamPerms_5504_, 2);
v___x_5531_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5532_ = lean_array_get_borrowed(v___x_5531_, v_revDeps_5530_, v_next_5505_);
v___x_5533_ = lean_array_get_borrowed(v___x_5531_, v___x_5532_, v_a_5508_);
if (v_isShared_5520_ == 0)
{
v___x_5535_ = v___x_5519_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_fst_5516_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_snd_5517_);
v___x_5535_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
size_t v_sz_5536_; size_t v___x_5537_; lean_object* v___x_5538_; lean_object* v_fst_5539_; lean_object* v_snd_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
v_sz_5536_ = lean_array_size(v___x_5533_);
v___x_5537_ = ((size_t)0ULL);
v___x_5538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5503_, v___x_5506_, v___x_5507_, v___x_5533_, v_sz_5536_, v___x_5537_, v___x_5535_);
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
v_a_5511_ = v___x_5545_;
goto v___jp_5510_;
}
}
}
}
}
else
{
lean_object* v___x_5550_; 
if (v_isShared_5520_ == 0)
{
v___x_5550_ = v___x_5519_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_fst_5516_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v_snd_5517_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
v_a_5511_ = v___x_5550_;
goto v___jp_5510_;
}
}
}
}
v___jp_5510_:
{
lean_object* v___x_5512_; lean_object* v___x_5513_; 
v___x_5512_ = lean_unsigned_to_nat(1u);
v___x_5513_ = lean_nat_add(v_a_5508_, v___x_5512_);
lean_dec(v_a_5508_);
v_a_5508_ = v___x_5513_;
v_b_5509_ = v_a_5511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5553_, lean_object* v___x_5554_, lean_object* v_fixedParamPerms_5555_, lean_object* v_next_5556_, lean_object* v___x_5557_, lean_object* v___x_5558_, lean_object* v_a_5559_, lean_object* v_b_5560_){
_start:
{
lean_object* v_res_5561_; 
v_res_5561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5553_, v___x_5554_, v_fixedParamPerms_5555_, v_next_5556_, v___x_5557_, v___x_5558_, v_a_5559_, v_b_5560_);
lean_dec(v___x_5558_);
lean_dec(v___x_5557_);
lean_dec(v_next_5556_);
lean_dec_ref(v_fixedParamPerms_5555_);
lean_dec_ref(v___x_5554_);
lean_dec(v_upperBound_5553_);
return v_res_5561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(lean_object* v_upperBound_5562_, lean_object* v___x_5563_, lean_object* v_fixedParamPerms_5564_, lean_object* v___x_5565_, lean_object* v___x_5566_, lean_object* v_a_5567_, lean_object* v_b_5568_){
_start:
{
uint8_t v___x_5569_; 
v___x_5569_ = lean_nat_dec_lt(v_a_5567_, v_upperBound_5562_);
if (v___x_5569_ == 0)
{
lean_dec(v_a_5567_);
return v_b_5568_;
}
else
{
lean_object* v_fst_5570_; lean_object* v_snd_5571_; lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5594_; 
v_fst_5570_ = lean_ctor_get(v_b_5568_, 0);
v_snd_5571_ = lean_ctor_get(v_b_5568_, 1);
v_isSharedCheck_5594_ = !lean_is_exclusive(v_b_5568_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5573_ = v_b_5568_;
v_isShared_5574_ = v_isSharedCheck_5594_;
goto v_resetjp_5572_;
}
else
{
lean_inc(v_snd_5571_);
lean_inc(v_fst_5570_);
lean_dec(v_b_5568_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5594_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5579_; 
v___x_5575_ = lean_array_fget_borrowed(v___x_5563_, v_a_5567_);
v___x_5576_ = lean_array_get_size(v___x_5575_);
v___x_5577_ = lean_unsigned_to_nat(0u);
if (v_isShared_5574_ == 0)
{
v___x_5579_ = v___x_5573_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_fst_5570_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_snd_5571_);
v___x_5579_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
lean_object* v___x_5580_; lean_object* v_fst_5581_; lean_object* v_snd_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5592_; 
v___x_5580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5576_, v___x_5575_, v_fixedParamPerms_5564_, v_a_5567_, v___x_5565_, v___x_5566_, v___x_5577_, v___x_5579_);
v_fst_5581_ = lean_ctor_get(v___x_5580_, 0);
v_snd_5582_ = lean_ctor_get(v___x_5580_, 1);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5584_ = v___x_5580_;
v_isShared_5585_ = v_isSharedCheck_5592_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_snd_5582_);
lean_inc(v_fst_5581_);
lean_dec(v___x_5580_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5592_;
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
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_fst_5581_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v_snd_5582_);
v___x_5587_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5588_ = lean_unsigned_to_nat(1u);
v___x_5589_ = lean_nat_add(v_a_5567_, v___x_5588_);
lean_dec(v_a_5567_);
v_a_5567_ = v___x_5589_;
v_b_5568_ = v___x_5587_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg___boxed(lean_object* v_upperBound_5595_, lean_object* v___x_5596_, lean_object* v_fixedParamPerms_5597_, lean_object* v___x_5598_, lean_object* v___x_5599_, lean_object* v_a_5600_, lean_object* v_b_5601_){
_start:
{
lean_object* v_res_5602_; 
v_res_5602_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(v_upperBound_5595_, v___x_5596_, v_fixedParamPerms_5597_, v___x_5598_, v___x_5599_, v_a_5600_, v_b_5601_);
lean_dec(v___x_5599_);
lean_dec(v___x_5598_);
lean_dec_ref(v_fixedParamPerms_5597_);
lean_dec_ref(v___x_5596_);
lean_dec(v_upperBound_5595_);
return v_res_5602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5603_, lean_object* v___x_5604_, lean_object* v___x_5605_, lean_object* v___x_5606_, lean_object* v_fixedParamPerms_5607_, lean_object* v_a_5608_, lean_object* v_b_5609_){
_start:
{
uint8_t v___x_5610_; 
v___x_5610_ = lean_nat_dec_lt(v_a_5608_, v_upperBound_5603_);
if (v___x_5610_ == 0)
{
return v_b_5609_;
}
else
{
lean_object* v_fst_5611_; lean_object* v_snd_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5635_; 
v_fst_5611_ = lean_ctor_get(v_b_5609_, 0);
v_snd_5612_ = lean_ctor_get(v_b_5609_, 1);
v_isSharedCheck_5635_ = !lean_is_exclusive(v_b_5609_);
if (v_isSharedCheck_5635_ == 0)
{
v___x_5614_ = v_b_5609_;
v_isShared_5615_ = v_isSharedCheck_5635_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_snd_5612_);
lean_inc(v_fst_5611_);
lean_dec(v_b_5609_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5635_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5620_; 
v___x_5616_ = lean_array_fget_borrowed(v___x_5604_, v_a_5608_);
v___x_5617_ = lean_array_get_size(v___x_5616_);
v___x_5618_ = lean_unsigned_to_nat(0u);
if (v_isShared_5615_ == 0)
{
v___x_5620_ = v___x_5614_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_fst_5611_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v_snd_5612_);
v___x_5620_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
lean_object* v___x_5621_; lean_object* v_fst_5622_; lean_object* v_snd_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5633_; 
v___x_5621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5617_, v___x_5616_, v_fixedParamPerms_5607_, v_a_5608_, v___x_5605_, v___x_5606_, v___x_5618_, v___x_5620_);
v_fst_5622_ = lean_ctor_get(v___x_5621_, 0);
v_snd_5623_ = lean_ctor_get(v___x_5621_, 1);
v_isSharedCheck_5633_ = !lean_is_exclusive(v___x_5621_);
if (v_isSharedCheck_5633_ == 0)
{
v___x_5625_ = v___x_5621_;
v_isShared_5626_ = v_isSharedCheck_5633_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_snd_5623_);
lean_inc(v_fst_5622_);
lean_dec(v___x_5621_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5633_;
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
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_fst_5622_);
lean_ctor_set(v_reuseFailAlloc_5632_, 1, v_snd_5623_);
v___x_5628_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5629_ = lean_unsigned_to_nat(1u);
v___x_5630_ = lean_nat_add(v_a_5608_, v___x_5629_);
v___x_5631_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(v_upperBound_5603_, v___x_5604_, v_fixedParamPerms_5607_, v___x_5605_, v___x_5606_, v___x_5630_, v___x_5628_);
return v___x_5631_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5636_, lean_object* v___x_5637_, lean_object* v___x_5638_, lean_object* v___x_5639_, lean_object* v_fixedParamPerms_5640_, lean_object* v_a_5641_, lean_object* v_b_5642_){
_start:
{
lean_object* v_res_5643_; 
v_res_5643_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5636_, v___x_5637_, v___x_5638_, v___x_5639_, v_fixedParamPerms_5640_, v_a_5641_, v_b_5642_);
lean_dec(v_a_5641_);
lean_dec_ref(v_fixedParamPerms_5640_);
lean_dec(v___x_5639_);
lean_dec(v___x_5638_);
lean_dec_ref(v___x_5637_);
lean_dec(v_upperBound_5636_);
return v_res_5643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5644_, lean_object* v___x_5645_, lean_object* v___x_5646_, lean_object* v_fixedParamPerms_5647_, lean_object* v_a_5648_){
_start:
{
lean_object* v_snd_5649_; uint8_t v___x_5650_; 
v_snd_5649_ = lean_ctor_get(v_a_5648_, 1);
v___x_5650_ = lean_unbox(v_snd_5649_);
if (v___x_5650_ == 0)
{
lean_object* v_fst_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
lean_inc(v_snd_5649_);
v_fst_5651_ = lean_ctor_get(v_a_5648_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v_a_5648_);
if (v_isSharedCheck_5658_ == 0)
{
lean_object* v_unused_5659_; 
v_unused_5659_ = lean_ctor_get(v_a_5648_, 1);
lean_dec(v_unused_5659_);
v___x_5653_ = v_a_5648_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_fst_5651_);
lean_dec(v_a_5648_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_fst_5651_);
lean_ctor_set(v_reuseFailAlloc_5657_, 1, v_snd_5649_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
else
{
lean_object* v_fst_5660_; lean_object* v___x_5662_; uint8_t v_isShared_5663_; uint8_t v_isSharedCheck_5681_; 
v_fst_5660_ = lean_ctor_get(v_a_5648_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v_a_5648_);
if (v_isSharedCheck_5681_ == 0)
{
lean_object* v_unused_5682_; 
v_unused_5682_ = lean_ctor_get(v_a_5648_, 1);
lean_dec(v_unused_5682_);
v___x_5662_ = v_a_5648_;
v_isShared_5663_ = v_isSharedCheck_5681_;
goto v_resetjp_5661_;
}
else
{
lean_inc(v_fst_5660_);
lean_dec(v_a_5648_);
v___x_5662_ = lean_box(0);
v_isShared_5663_ = v_isSharedCheck_5681_;
goto v_resetjp_5661_;
}
v_resetjp_5661_:
{
uint8_t v_changed_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5668_; 
v_changed_5664_ = 0;
v___x_5665_ = lean_unsigned_to_nat(0u);
v___x_5666_ = lean_box(v_changed_5664_);
if (v_isShared_5663_ == 0)
{
lean_ctor_set(v___x_5662_, 1, v___x_5666_);
v___x_5668_ = v___x_5662_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_fst_5660_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v___x_5666_);
v___x_5668_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
lean_object* v___x_5669_; lean_object* v_fst_5670_; lean_object* v_snd_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5679_; 
v___x_5669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5644_, v___x_5645_, v___x_5646_, v___x_5644_, v_fixedParamPerms_5647_, v___x_5665_, v___x_5668_);
v_fst_5670_ = lean_ctor_get(v___x_5669_, 0);
v_snd_5671_ = lean_ctor_get(v___x_5669_, 1);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5673_ = v___x_5669_;
v_isShared_5674_ = v_isSharedCheck_5679_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_snd_5671_);
lean_inc(v_fst_5670_);
lean_dec(v___x_5669_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5679_;
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
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_fst_5670_);
lean_ctor_set(v_reuseFailAlloc_5678_, 1, v_snd_5671_);
v___x_5676_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
v_a_5648_ = v___x_5676_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5683_, lean_object* v___x_5684_, lean_object* v___x_5685_, lean_object* v_fixedParamPerms_5686_, lean_object* v_a_5687_){
_start:
{
lean_object* v_res_5688_; 
v_res_5688_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5683_, v___x_5684_, v___x_5685_, v_fixedParamPerms_5686_, v_a_5687_);
lean_dec_ref(v_fixedParamPerms_5686_);
lean_dec(v___x_5685_);
lean_dec_ref(v___x_5684_);
lean_dec(v___x_5683_);
return v_res_5688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5689_, lean_object* v_a_5690_, lean_object* v_b_5691_){
_start:
{
lean_object* v_a_5693_; uint8_t v___x_5697_; 
v___x_5697_ = lean_nat_dec_lt(v_a_5690_, v_upperBound_5689_);
if (v___x_5697_ == 0)
{
lean_dec(v_a_5690_);
return v_b_5691_;
}
else
{
lean_object* v_snd_5698_; lean_object* v_snd_5699_; lean_object* v_snd_5700_; lean_object* v_snd_5701_; lean_object* v_fst_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5814_; 
v_snd_5698_ = lean_ctor_get(v_b_5691_, 1);
lean_inc(v_snd_5698_);
v_snd_5699_ = lean_ctor_get(v_snd_5698_, 1);
lean_inc(v_snd_5699_);
v_snd_5700_ = lean_ctor_get(v_snd_5699_, 1);
lean_inc(v_snd_5700_);
v_snd_5701_ = lean_ctor_get(v_snd_5700_, 1);
lean_inc(v_snd_5701_);
v_fst_5702_ = lean_ctor_get(v_b_5691_, 0);
v_isSharedCheck_5814_ = !lean_is_exclusive(v_b_5691_);
if (v_isSharedCheck_5814_ == 0)
{
lean_object* v_unused_5815_; 
v_unused_5815_ = lean_ctor_get(v_b_5691_, 1);
lean_dec(v_unused_5815_);
v___x_5704_ = v_b_5691_;
v_isShared_5705_ = v_isSharedCheck_5814_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_fst_5702_);
lean_dec(v_b_5691_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5814_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v_fst_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5812_; 
v_fst_5706_ = lean_ctor_get(v_snd_5698_, 0);
v_isSharedCheck_5812_ = !lean_is_exclusive(v_snd_5698_);
if (v_isSharedCheck_5812_ == 0)
{
lean_object* v_unused_5813_; 
v_unused_5813_ = lean_ctor_get(v_snd_5698_, 1);
lean_dec(v_unused_5813_);
v___x_5708_ = v_snd_5698_;
v_isShared_5709_ = v_isSharedCheck_5812_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_fst_5706_);
lean_dec(v_snd_5698_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5812_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v_fst_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5810_; 
v_fst_5710_ = lean_ctor_get(v_snd_5699_, 0);
v_isSharedCheck_5810_ = !lean_is_exclusive(v_snd_5699_);
if (v_isSharedCheck_5810_ == 0)
{
lean_object* v_unused_5811_; 
v_unused_5811_ = lean_ctor_get(v_snd_5699_, 1);
lean_dec(v_unused_5811_);
v___x_5712_ = v_snd_5699_;
v_isShared_5713_ = v_isSharedCheck_5810_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_fst_5710_);
lean_dec(v_snd_5699_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5810_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v_fst_5714_; lean_object* v___x_5716_; uint8_t v_isShared_5717_; uint8_t v_isSharedCheck_5808_; 
v_fst_5714_ = lean_ctor_get(v_snd_5700_, 0);
v_isSharedCheck_5808_ = !lean_is_exclusive(v_snd_5700_);
if (v_isSharedCheck_5808_ == 0)
{
lean_object* v_unused_5809_; 
v_unused_5809_ = lean_ctor_get(v_snd_5700_, 1);
lean_dec(v_unused_5809_);
v___x_5716_ = v_snd_5700_;
v_isShared_5717_ = v_isSharedCheck_5808_;
goto v_resetjp_5715_;
}
else
{
lean_inc(v_fst_5714_);
lean_dec(v_snd_5700_);
v___x_5716_ = lean_box(0);
v_isShared_5717_ = v_isSharedCheck_5808_;
goto v_resetjp_5715_;
}
v_resetjp_5715_:
{
lean_object* v_array_5718_; lean_object* v_start_5719_; lean_object* v_stop_5720_; uint8_t v___x_5721_; 
v_array_5718_ = lean_ctor_get(v_snd_5701_, 0);
v_start_5719_ = lean_ctor_get(v_snd_5701_, 1);
v_stop_5720_ = lean_ctor_get(v_snd_5701_, 2);
v___x_5721_ = lean_nat_dec_lt(v_start_5719_, v_stop_5720_);
if (v___x_5721_ == 0)
{
lean_object* v___x_5723_; 
lean_dec(v_a_5690_);
if (v_isShared_5717_ == 0)
{
v___x_5723_ = v___x_5716_;
goto v_reusejp_5722_;
}
else
{
lean_object* v_reuseFailAlloc_5733_; 
v_reuseFailAlloc_5733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5733_, 0, v_fst_5714_);
lean_ctor_set(v_reuseFailAlloc_5733_, 1, v_snd_5701_);
v___x_5723_ = v_reuseFailAlloc_5733_;
goto v_reusejp_5722_;
}
v_reusejp_5722_:
{
lean_object* v___x_5725_; 
if (v_isShared_5713_ == 0)
{
lean_ctor_set(v___x_5712_, 1, v___x_5723_);
v___x_5725_ = v___x_5712_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_fst_5710_);
lean_ctor_set(v_reuseFailAlloc_5732_, 1, v___x_5723_);
v___x_5725_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
lean_object* v___x_5727_; 
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 1, v___x_5725_);
v___x_5727_ = v___x_5708_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5731_; 
v_reuseFailAlloc_5731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_fst_5706_);
lean_ctor_set(v_reuseFailAlloc_5731_, 1, v___x_5725_);
v___x_5727_ = v_reuseFailAlloc_5731_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
lean_object* v___x_5729_; 
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 1, v___x_5727_);
v___x_5729_ = v___x_5704_;
goto v_reusejp_5728_;
}
else
{
lean_object* v_reuseFailAlloc_5730_; 
v_reuseFailAlloc_5730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5730_, 0, v_fst_5702_);
lean_ctor_set(v_reuseFailAlloc_5730_, 1, v___x_5727_);
v___x_5729_ = v_reuseFailAlloc_5730_;
goto v_reusejp_5728_;
}
v_reusejp_5728_:
{
return v___x_5729_;
}
}
}
}
}
else
{
lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5804_; 
lean_inc(v_stop_5720_);
lean_inc(v_start_5719_);
lean_inc_ref(v_array_5718_);
v_isSharedCheck_5804_ = !lean_is_exclusive(v_snd_5701_);
if (v_isSharedCheck_5804_ == 0)
{
lean_object* v_unused_5805_; lean_object* v_unused_5806_; lean_object* v_unused_5807_; 
v_unused_5805_ = lean_ctor_get(v_snd_5701_, 2);
lean_dec(v_unused_5805_);
v_unused_5806_ = lean_ctor_get(v_snd_5701_, 1);
lean_dec(v_unused_5806_);
v_unused_5807_ = lean_ctor_get(v_snd_5701_, 0);
lean_dec(v_unused_5807_);
v___x_5735_ = v_snd_5701_;
v_isShared_5736_ = v_isSharedCheck_5804_;
goto v_resetjp_5734_;
}
else
{
lean_dec(v_snd_5701_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5804_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v_array_5737_; lean_object* v_start_5738_; lean_object* v_stop_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5744_; 
v_array_5737_ = lean_ctor_get(v_fst_5714_, 0);
v_start_5738_ = lean_ctor_get(v_fst_5714_, 1);
v_stop_5739_ = lean_ctor_get(v_fst_5714_, 2);
v___x_5740_ = lean_array_fget(v_array_5718_, v_start_5719_);
v___x_5741_ = lean_unsigned_to_nat(1u);
v___x_5742_ = lean_nat_add(v_start_5719_, v___x_5741_);
lean_dec(v_start_5719_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___x_5742_);
v___x_5744_ = v___x_5735_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_array_5718_);
lean_ctor_set(v_reuseFailAlloc_5803_, 1, v___x_5742_);
lean_ctor_set(v_reuseFailAlloc_5803_, 2, v_stop_5720_);
v___x_5744_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
uint8_t v___x_5745_; 
v___x_5745_ = lean_nat_dec_lt(v_start_5738_, v_stop_5739_);
if (v___x_5745_ == 0)
{
lean_object* v___x_5747_; 
lean_dec(v___x_5740_);
lean_dec(v_a_5690_);
if (v_isShared_5717_ == 0)
{
lean_ctor_set(v___x_5716_, 1, v___x_5744_);
v___x_5747_ = v___x_5716_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_fst_5714_);
lean_ctor_set(v_reuseFailAlloc_5757_, 1, v___x_5744_);
v___x_5747_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
lean_object* v___x_5749_; 
if (v_isShared_5713_ == 0)
{
lean_ctor_set(v___x_5712_, 1, v___x_5747_);
v___x_5749_ = v___x_5712_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_fst_5710_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v___x_5747_);
v___x_5749_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
lean_object* v___x_5751_; 
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 1, v___x_5749_);
v___x_5751_ = v___x_5708_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_fst_5706_);
lean_ctor_set(v_reuseFailAlloc_5755_, 1, v___x_5749_);
v___x_5751_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
lean_object* v___x_5753_; 
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 1, v___x_5751_);
v___x_5753_ = v___x_5704_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_fst_5702_);
lean_ctor_set(v_reuseFailAlloc_5754_, 1, v___x_5751_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
else
{
lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5799_; 
lean_inc(v_stop_5739_);
lean_inc(v_start_5738_);
lean_inc_ref(v_array_5737_);
v_isSharedCheck_5799_ = !lean_is_exclusive(v_fst_5714_);
if (v_isSharedCheck_5799_ == 0)
{
lean_object* v_unused_5800_; lean_object* v_unused_5801_; lean_object* v_unused_5802_; 
v_unused_5800_ = lean_ctor_get(v_fst_5714_, 2);
lean_dec(v_unused_5800_);
v_unused_5801_ = lean_ctor_get(v_fst_5714_, 1);
lean_dec(v_unused_5801_);
v_unused_5802_ = lean_ctor_get(v_fst_5714_, 0);
lean_dec(v_unused_5802_);
v___x_5759_ = v_fst_5714_;
v_isShared_5760_ = v_isSharedCheck_5799_;
goto v_resetjp_5758_;
}
else
{
lean_dec(v_fst_5714_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5799_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5764_; 
v___x_5761_ = lean_array_fget(v_array_5737_, v_start_5738_);
v___x_5762_ = lean_nat_add(v_start_5738_, v___x_5741_);
lean_dec(v_start_5738_);
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 1, v___x_5762_);
v___x_5764_ = v___x_5759_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_array_5737_);
lean_ctor_set(v_reuseFailAlloc_5798_, 1, v___x_5762_);
lean_ctor_set(v_reuseFailAlloc_5798_, 2, v_stop_5739_);
v___x_5764_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
uint8_t v___x_5765_; 
v___x_5765_ = lean_unbox(v___x_5761_);
lean_dec(v___x_5761_);
if (v___x_5765_ == 0)
{
lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5771_; 
v___x_5766_ = lean_array_get_size(v_fst_5710_);
v___x_5767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5767_, 0, v___x_5766_);
v___x_5768_ = lean_array_push(v_fst_5702_, v___x_5767_);
v___x_5769_ = lean_array_push(v_fst_5710_, v___x_5740_);
if (v_isShared_5717_ == 0)
{
lean_ctor_set(v___x_5716_, 1, v___x_5744_);
lean_ctor_set(v___x_5716_, 0, v___x_5764_);
v___x_5771_ = v___x_5716_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v___x_5764_);
lean_ctor_set(v_reuseFailAlloc_5781_, 1, v___x_5744_);
v___x_5771_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
lean_object* v___x_5773_; 
if (v_isShared_5713_ == 0)
{
lean_ctor_set(v___x_5712_, 1, v___x_5771_);
lean_ctor_set(v___x_5712_, 0, v___x_5769_);
v___x_5773_ = v___x_5712_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v___x_5769_);
lean_ctor_set(v_reuseFailAlloc_5780_, 1, v___x_5771_);
v___x_5773_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
lean_object* v___x_5775_; 
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 1, v___x_5773_);
v___x_5775_ = v___x_5708_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_fst_5706_);
lean_ctor_set(v_reuseFailAlloc_5779_, 1, v___x_5773_);
v___x_5775_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
lean_object* v___x_5777_; 
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 1, v___x_5775_);
lean_ctor_set(v___x_5704_, 0, v___x_5768_);
v___x_5777_ = v___x_5704_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v___x_5768_);
lean_ctor_set(v_reuseFailAlloc_5778_, 1, v___x_5775_);
v___x_5777_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
v_a_5693_ = v___x_5777_;
goto v___jp_5692_;
}
}
}
}
}
else
{
lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5787_; 
v___x_5782_ = lean_box(0);
v___x_5783_ = lean_array_push(v_fst_5702_, v___x_5782_);
v___x_5784_ = l_Lean_Expr_fvarId_x21(v___x_5740_);
lean_dec(v___x_5740_);
v___x_5785_ = lean_array_push(v_fst_5706_, v___x_5784_);
if (v_isShared_5717_ == 0)
{
lean_ctor_set(v___x_5716_, 1, v___x_5744_);
lean_ctor_set(v___x_5716_, 0, v___x_5764_);
v___x_5787_ = v___x_5716_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5764_);
lean_ctor_set(v_reuseFailAlloc_5797_, 1, v___x_5744_);
v___x_5787_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
lean_object* v___x_5789_; 
if (v_isShared_5713_ == 0)
{
lean_ctor_set(v___x_5712_, 1, v___x_5787_);
v___x_5789_ = v___x_5712_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v_fst_5710_);
lean_ctor_set(v_reuseFailAlloc_5796_, 1, v___x_5787_);
v___x_5789_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
lean_object* v___x_5791_; 
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 1, v___x_5789_);
lean_ctor_set(v___x_5708_, 0, v___x_5785_);
v___x_5791_ = v___x_5708_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v___x_5785_);
lean_ctor_set(v_reuseFailAlloc_5795_, 1, v___x_5789_);
v___x_5791_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
lean_object* v___x_5793_; 
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 1, v___x_5791_);
lean_ctor_set(v___x_5704_, 0, v___x_5783_);
v___x_5793_ = v___x_5704_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5783_);
lean_ctor_set(v_reuseFailAlloc_5794_, 1, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
v_a_5693_ = v___x_5793_;
goto v___jp_5692_;
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
v___jp_5692_:
{
lean_object* v___x_5694_; lean_object* v___x_5695_; 
v___x_5694_ = lean_unsigned_to_nat(1u);
v___x_5695_ = lean_nat_add(v_a_5690_, v___x_5694_);
lean_dec(v_a_5690_);
v_a_5690_ = v___x_5695_;
v_b_5691_ = v_a_5693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5816_, lean_object* v_a_5817_, lean_object* v_b_5818_){
_start:
{
lean_object* v_res_5819_; 
v_res_5819_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5816_, v_a_5817_, v_b_5818_);
lean_dec(v_upperBound_5816_);
return v_res_5819_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5820_, size_t v_i_5821_, size_t v_stop_5822_){
_start:
{
uint8_t v___x_5823_; 
v___x_5823_ = lean_usize_dec_eq(v_i_5821_, v_stop_5822_);
if (v___x_5823_ == 0)
{
lean_object* v___x_5824_; uint8_t v___x_5825_; 
v___x_5824_ = lean_array_uget_borrowed(v_as_5820_, v_i_5821_);
v___x_5825_ = l_Lean_Expr_isFVar(v___x_5824_);
if (v___x_5825_ == 0)
{
uint8_t v___x_5826_; 
v___x_5826_ = 1;
return v___x_5826_;
}
else
{
size_t v___x_5827_; size_t v___x_5828_; 
v___x_5827_ = ((size_t)1ULL);
v___x_5828_ = lean_usize_add(v_i_5821_, v___x_5827_);
v_i_5821_ = v___x_5828_;
goto _start;
}
}
else
{
uint8_t v___x_5830_; 
v___x_5830_ = 0;
return v___x_5830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5831_, lean_object* v_i_5832_, lean_object* v_stop_5833_){
_start:
{
size_t v_i_boxed_5834_; size_t v_stop_boxed_5835_; uint8_t v_res_5836_; lean_object* v_r_5837_; 
v_i_boxed_5834_ = lean_unbox_usize(v_i_5832_);
lean_dec(v_i_5832_);
v_stop_boxed_5835_ = lean_unbox_usize(v_stop_5833_);
lean_dec(v_stop_5833_);
v_res_5836_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5831_, v_i_boxed_5834_, v_stop_boxed_5835_);
lean_dec_ref(v_as_5831_);
v_r_5837_ = lean_box(v_res_5836_);
return v_r_5837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5838_, size_t v_sz_5839_, size_t v_i_5840_, lean_object* v_bs_5841_){
_start:
{
uint8_t v___x_5842_; 
v___x_5842_ = lean_usize_dec_lt(v_i_5840_, v_sz_5839_);
if (v___x_5842_ == 0)
{
return v_bs_5841_;
}
else
{
lean_object* v_v_5843_; lean_object* v___x_5844_; lean_object* v_bs_x27_5845_; lean_object* v___y_5847_; 
v_v_5843_ = lean_array_uget(v_bs_5841_, v_i_5840_);
v___x_5844_ = lean_unsigned_to_nat(0u);
v_bs_x27_5845_ = lean_array_uset(v_bs_5841_, v_i_5840_, v___x_5844_);
if (lean_obj_tag(v_v_5843_) == 0)
{
v___y_5847_ = v_v_5843_;
goto v___jp_5846_;
}
else
{
lean_object* v_val_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; 
v_val_5852_ = lean_ctor_get(v_v_5843_, 0);
lean_inc(v_val_5852_);
lean_dec_ref_known(v_v_5843_, 1);
v___x_5853_ = lean_box(0);
v___x_5854_ = lean_array_get_borrowed(v___x_5853_, v___x_5838_, v_val_5852_);
lean_dec(v_val_5852_);
lean_inc(v___x_5854_);
v___y_5847_ = v___x_5854_;
goto v___jp_5846_;
}
v___jp_5846_:
{
size_t v___x_5848_; size_t v___x_5849_; lean_object* v___x_5850_; 
v___x_5848_ = ((size_t)1ULL);
v___x_5849_ = lean_usize_add(v_i_5840_, v___x_5848_);
v___x_5850_ = lean_array_uset(v_bs_x27_5845_, v_i_5840_, v___y_5847_);
v_i_5840_ = v___x_5849_;
v_bs_5841_ = v___x_5850_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5855_, lean_object* v_sz_5856_, lean_object* v_i_5857_, lean_object* v_bs_5858_){
_start:
{
size_t v_sz_boxed_5859_; size_t v_i_boxed_5860_; lean_object* v_res_5861_; 
v_sz_boxed_5859_ = lean_unbox_usize(v_sz_5856_);
lean_dec(v_sz_5856_);
v_i_boxed_5860_ = lean_unbox_usize(v_i_5857_);
lean_dec(v_i_5857_);
v_res_5861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5855_, v_sz_boxed_5859_, v_i_boxed_5860_, v_bs_5858_);
lean_dec_ref(v___x_5855_);
return v_res_5861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5862_, size_t v_sz_5863_, size_t v_i_5864_, lean_object* v_bs_5865_){
_start:
{
uint8_t v___x_5866_; 
v___x_5866_ = lean_usize_dec_lt(v_i_5864_, v_sz_5863_);
if (v___x_5866_ == 0)
{
return v_bs_5865_;
}
else
{
lean_object* v_v_5867_; lean_object* v___x_5868_; lean_object* v_bs_x27_5869_; size_t v_sz_5870_; size_t v___x_5871_; lean_object* v___x_5872_; size_t v___x_5873_; size_t v___x_5874_; lean_object* v___x_5875_; 
v_v_5867_ = lean_array_uget(v_bs_5865_, v_i_5864_);
v___x_5868_ = lean_unsigned_to_nat(0u);
v_bs_x27_5869_ = lean_array_uset(v_bs_5865_, v_i_5864_, v___x_5868_);
v_sz_5870_ = lean_array_size(v_v_5867_);
v___x_5871_ = ((size_t)0ULL);
v___x_5872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5862_, v_sz_5870_, v___x_5871_, v_v_5867_);
v___x_5873_ = ((size_t)1ULL);
v___x_5874_ = lean_usize_add(v_i_5864_, v___x_5873_);
v___x_5875_ = lean_array_uset(v_bs_x27_5869_, v_i_5864_, v___x_5872_);
v_i_5864_ = v___x_5874_;
v_bs_5865_ = v___x_5875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5877_, lean_object* v_sz_5878_, lean_object* v_i_5879_, lean_object* v_bs_5880_){
_start:
{
size_t v_sz_boxed_5881_; size_t v_i_boxed_5882_; lean_object* v_res_5883_; 
v_sz_boxed_5881_ = lean_unbox_usize(v_sz_5878_);
lean_dec(v_sz_5878_);
v_i_boxed_5882_ = lean_unbox_usize(v_i_5879_);
lean_dec(v_i_5879_);
v_res_5883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5877_, v_sz_boxed_5881_, v_i_boxed_5882_, v_bs_5880_);
lean_dec_ref(v___x_5877_);
return v_res_5883_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
v___x_5886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5887_ = lean_unsigned_to_nat(6u);
v___x_5888_ = lean_unsigned_to_nat(463u);
v___x_5889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5890_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5891_ = l_mkPanicMessageWithDecl(v___x_5890_, v___x_5889_, v___x_5888_, v___x_5887_, v___x_5886_);
return v___x_5891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5892_, lean_object* v___x_5893_, lean_object* v___x_5894_, lean_object* v_as_5895_, size_t v_sz_5896_, size_t v_i_5897_, lean_object* v_b_5898_){
_start:
{
lean_object* v_a_5900_; uint8_t v___x_5904_; 
v___x_5904_ = lean_usize_dec_lt(v_i_5897_, v_sz_5896_);
if (v___x_5904_ == 0)
{
return v_b_5898_;
}
else
{
lean_object* v_a_5905_; lean_object* v___x_5906_; uint8_t v___x_5907_; 
v_a_5905_ = lean_array_uget_borrowed(v_as_5895_, v_i_5897_);
v___x_5906_ = lean_array_get_size(v___x_5892_);
v___x_5907_ = lean_nat_dec_lt(v_a_5905_, v___x_5906_);
if (v___x_5907_ == 0)
{
lean_object* v___x_5908_; lean_object* v___x_5909_; 
lean_dec_ref(v_b_5898_);
v___x_5908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5909_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5908_);
if (lean_obj_tag(v___x_5909_) == 0)
{
lean_object* v_a_5910_; 
v_a_5910_ = lean_ctor_get(v___x_5909_, 0);
lean_inc(v_a_5910_);
lean_dec_ref_known(v___x_5909_, 1);
return v_a_5910_;
}
else
{
lean_object* v_a_5911_; 
v_a_5911_ = lean_ctor_get(v___x_5909_, 0);
lean_inc(v_a_5911_);
lean_dec_ref_known(v___x_5909_, 1);
v_a_5900_ = v_a_5911_;
goto v___jp_5899_;
}
}
else
{
lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5912_ = lean_box(0);
v___x_5913_ = lean_array_get_borrowed(v___x_5912_, v___x_5892_, v_a_5905_);
if (lean_obj_tag(v___x_5913_) == 1)
{
lean_object* v_val_5914_; uint8_t v_changed_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v_val_5914_ = lean_ctor_get(v___x_5913_, 0);
v_changed_5915_ = lean_nat_dec_eq(v___x_5893_, v___x_5894_);
v___x_5916_ = lean_box(v_changed_5915_);
v___x_5917_ = lean_array_set(v_b_5898_, v_val_5914_, v___x_5916_);
v_a_5900_ = v___x_5917_;
goto v___jp_5899_;
}
else
{
v_a_5900_ = v_b_5898_;
goto v___jp_5899_;
}
}
}
v___jp_5899_:
{
size_t v___x_5901_; size_t v___x_5902_; 
v___x_5901_ = ((size_t)1ULL);
v___x_5902_ = lean_usize_add(v_i_5897_, v___x_5901_);
v_i_5897_ = v___x_5902_;
v_b_5898_ = v_a_5900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5918_, lean_object* v___x_5919_, lean_object* v___x_5920_, lean_object* v_as_5921_, lean_object* v_sz_5922_, lean_object* v_i_5923_, lean_object* v_b_5924_){
_start:
{
size_t v_sz_boxed_5925_; size_t v_i_boxed_5926_; lean_object* v_res_5927_; 
v_sz_boxed_5925_ = lean_unbox_usize(v_sz_5922_);
lean_dec(v_sz_5922_);
v_i_boxed_5926_ = lean_unbox_usize(v_i_5923_);
lean_dec(v_i_5923_);
v_res_5927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5918_, v___x_5919_, v___x_5920_, v_as_5921_, v_sz_boxed_5925_, v_i_boxed_5926_, v_b_5924_);
lean_dec_ref(v_as_5921_);
lean_dec(v___x_5920_);
lean_dec(v___x_5919_);
lean_dec_ref(v___x_5918_);
return v_res_5927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5928_, lean_object* v___x_5929_, lean_object* v___x_5930_, lean_object* v_a_5931_, lean_object* v_b_5932_){
_start:
{
uint8_t v___x_5933_; 
v___x_5933_ = lean_nat_dec_lt(v_a_5931_, v_upperBound_5928_);
if (v___x_5933_ == 0)
{
lean_dec(v_a_5931_);
return v_b_5932_;
}
else
{
lean_object* v_snd_5934_; lean_object* v_snd_5935_; lean_object* v_fst_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_6002_; 
v_snd_5934_ = lean_ctor_get(v_b_5932_, 1);
lean_inc(v_snd_5934_);
v_snd_5935_ = lean_ctor_get(v_snd_5934_, 1);
lean_inc(v_snd_5935_);
v_fst_5936_ = lean_ctor_get(v_b_5932_, 0);
v_isSharedCheck_6002_ = !lean_is_exclusive(v_b_5932_);
if (v_isSharedCheck_6002_ == 0)
{
lean_object* v_unused_6003_; 
v_unused_6003_ = lean_ctor_get(v_b_5932_, 1);
lean_dec(v_unused_6003_);
v___x_5938_ = v_b_5932_;
v_isShared_5939_ = v_isSharedCheck_6002_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_fst_5936_);
lean_dec(v_b_5932_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_6002_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v_fst_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_6000_; 
v_fst_5940_ = lean_ctor_get(v_snd_5934_, 0);
v_isSharedCheck_6000_ = !lean_is_exclusive(v_snd_5934_);
if (v_isSharedCheck_6000_ == 0)
{
lean_object* v_unused_6001_; 
v_unused_6001_ = lean_ctor_get(v_snd_5934_, 1);
lean_dec(v_unused_6001_);
v___x_5942_ = v_snd_5934_;
v_isShared_5943_ = v_isSharedCheck_6000_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_fst_5940_);
lean_dec(v_snd_5934_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_6000_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v_array_5944_; lean_object* v_start_5945_; lean_object* v_stop_5946_; uint8_t v___x_5947_; 
v_array_5944_ = lean_ctor_get(v_snd_5935_, 0);
v_start_5945_ = lean_ctor_get(v_snd_5935_, 1);
v_stop_5946_ = lean_ctor_get(v_snd_5935_, 2);
v___x_5947_ = lean_nat_dec_lt(v_start_5945_, v_stop_5946_);
if (v___x_5947_ == 0)
{
lean_object* v___x_5949_; 
lean_dec(v_a_5931_);
if (v_isShared_5943_ == 0)
{
v___x_5949_ = v___x_5942_;
goto v_reusejp_5948_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v_fst_5940_);
lean_ctor_set(v_reuseFailAlloc_5953_, 1, v_snd_5935_);
v___x_5949_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5948_;
}
v_reusejp_5948_:
{
lean_object* v___x_5951_; 
if (v_isShared_5939_ == 0)
{
lean_ctor_set(v___x_5938_, 1, v___x_5949_);
v___x_5951_ = v___x_5938_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_fst_5936_);
lean_ctor_set(v_reuseFailAlloc_5952_, 1, v___x_5949_);
v___x_5951_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
return v___x_5951_;
}
}
}
else
{
lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_5996_; 
lean_inc(v_stop_5946_);
lean_inc(v_start_5945_);
lean_inc_ref(v_array_5944_);
v_isSharedCheck_5996_ = !lean_is_exclusive(v_snd_5935_);
if (v_isSharedCheck_5996_ == 0)
{
lean_object* v_unused_5997_; lean_object* v_unused_5998_; lean_object* v_unused_5999_; 
v_unused_5997_ = lean_ctor_get(v_snd_5935_, 2);
lean_dec(v_unused_5997_);
v_unused_5998_ = lean_ctor_get(v_snd_5935_, 1);
lean_dec(v_unused_5998_);
v_unused_5999_ = lean_ctor_get(v_snd_5935_, 0);
lean_dec(v_unused_5999_);
v___x_5955_ = v_snd_5935_;
v_isShared_5956_ = v_isSharedCheck_5996_;
goto v_resetjp_5954_;
}
else
{
lean_dec(v_snd_5935_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_5996_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v_array_5957_; lean_object* v_start_5958_; lean_object* v_stop_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5964_; 
v_array_5957_ = lean_ctor_get(v_fst_5940_, 0);
v_start_5958_ = lean_ctor_get(v_fst_5940_, 1);
v_stop_5959_ = lean_ctor_get(v_fst_5940_, 2);
v___x_5960_ = lean_array_fget(v_array_5944_, v_start_5945_);
v___x_5961_ = lean_unsigned_to_nat(1u);
v___x_5962_ = lean_nat_add(v_start_5945_, v___x_5961_);
lean_dec(v_start_5945_);
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 1, v___x_5962_);
v___x_5964_ = v___x_5955_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v_array_5944_);
lean_ctor_set(v_reuseFailAlloc_5995_, 1, v___x_5962_);
lean_ctor_set(v_reuseFailAlloc_5995_, 2, v_stop_5946_);
v___x_5964_ = v_reuseFailAlloc_5995_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
uint8_t v___x_5965_; 
v___x_5965_ = lean_nat_dec_lt(v_start_5958_, v_stop_5959_);
if (v___x_5965_ == 0)
{
lean_object* v___x_5967_; 
lean_dec(v___x_5960_);
lean_dec(v_a_5931_);
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v___x_5964_);
v___x_5967_ = v___x_5942_;
goto v_reusejp_5966_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_fst_5940_);
lean_ctor_set(v_reuseFailAlloc_5971_, 1, v___x_5964_);
v___x_5967_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5966_;
}
v_reusejp_5966_:
{
lean_object* v___x_5969_; 
if (v_isShared_5939_ == 0)
{
lean_ctor_set(v___x_5938_, 1, v___x_5967_);
v___x_5969_ = v___x_5938_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_fst_5936_);
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
lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5991_; 
lean_inc(v_stop_5959_);
lean_inc(v_start_5958_);
lean_inc_ref(v_array_5957_);
v_isSharedCheck_5991_ = !lean_is_exclusive(v_fst_5940_);
if (v_isSharedCheck_5991_ == 0)
{
lean_object* v_unused_5992_; lean_object* v_unused_5993_; lean_object* v_unused_5994_; 
v_unused_5992_ = lean_ctor_get(v_fst_5940_, 2);
lean_dec(v_unused_5992_);
v_unused_5993_ = lean_ctor_get(v_fst_5940_, 1);
lean_dec(v_unused_5993_);
v_unused_5994_ = lean_ctor_get(v_fst_5940_, 0);
lean_dec(v_unused_5994_);
v___x_5973_ = v_fst_5940_;
v_isShared_5974_ = v_isSharedCheck_5991_;
goto v_resetjp_5972_;
}
else
{
lean_dec(v_fst_5940_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5991_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5978_; 
v___x_5975_ = lean_array_fget(v_array_5957_, v_start_5958_);
v___x_5976_ = lean_nat_add(v_start_5958_, v___x_5961_);
lean_dec(v_start_5958_);
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 1, v___x_5976_);
v___x_5978_ = v___x_5973_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_array_5957_);
lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5976_);
lean_ctor_set(v_reuseFailAlloc_5990_, 2, v_stop_5959_);
v___x_5978_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
size_t v_sz_5979_; size_t v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5983_; 
v_sz_5979_ = lean_array_size(v___x_5975_);
v___x_5980_ = ((size_t)0ULL);
v___x_5981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5960_, v___x_5929_, v___x_5930_, v___x_5975_, v_sz_5979_, v___x_5980_, v_fst_5936_);
lean_dec(v___x_5975_);
lean_dec(v___x_5960_);
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v___x_5964_);
lean_ctor_set(v___x_5942_, 0, v___x_5978_);
v___x_5983_ = v___x_5942_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5978_);
lean_ctor_set(v_reuseFailAlloc_5989_, 1, v___x_5964_);
v___x_5983_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
lean_object* v___x_5985_; 
if (v_isShared_5939_ == 0)
{
lean_ctor_set(v___x_5938_, 1, v___x_5983_);
lean_ctor_set(v___x_5938_, 0, v___x_5981_);
v___x_5985_ = v___x_5938_;
goto v_reusejp_5984_;
}
else
{
lean_object* v_reuseFailAlloc_5988_; 
v_reuseFailAlloc_5988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5988_, 0, v___x_5981_);
lean_ctor_set(v_reuseFailAlloc_5988_, 1, v___x_5983_);
v___x_5985_ = v_reuseFailAlloc_5988_;
goto v_reusejp_5984_;
}
v_reusejp_5984_:
{
lean_object* v___x_5986_; 
v___x_5986_ = lean_nat_add(v_a_5931_, v___x_5961_);
lean_dec(v_a_5931_);
v_a_5931_ = v___x_5986_;
v_b_5932_ = v___x_5985_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6004_, lean_object* v___x_6005_, lean_object* v___x_6006_, lean_object* v_a_6007_, lean_object* v_b_6008_){
_start:
{
lean_object* v_res_6009_; 
v_res_6009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6004_, v___x_6005_, v___x_6006_, v_a_6007_, v_b_6008_);
lean_dec(v___x_6006_);
lean_dec(v___x_6005_);
lean_dec(v_upperBound_6004_);
return v_res_6009_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; 
v___x_6011_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6012_ = lean_unsigned_to_nat(2u);
v___x_6013_ = lean_unsigned_to_nat(457u);
v___x_6014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6015_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6016_ = l_mkPanicMessageWithDecl(v___x_6015_, v___x_6014_, v___x_6013_, v___x_6012_, v___x_6011_);
return v___x_6016_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6018_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6019_ = lean_unsigned_to_nat(2u);
v___x_6020_ = lean_unsigned_to_nat(458u);
v___x_6021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6022_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6023_ = l_mkPanicMessageWithDecl(v___x_6022_, v___x_6021_, v___x_6020_, v___x_6019_, v___x_6018_);
return v___x_6023_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; 
v___x_6025_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6026_ = lean_unsigned_to_nat(2u);
v___x_6027_ = lean_unsigned_to_nat(456u);
v___x_6028_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6029_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6030_ = l_mkPanicMessageWithDecl(v___x_6029_, v___x_6028_, v___x_6027_, v___x_6026_, v___x_6025_);
return v___x_6030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6031_, lean_object* v_xs_6032_, lean_object* v_toErase_6033_){
_start:
{
lean_object* v___x_6034_; lean_object* v___x_6035_; uint8_t v___x_6119_; 
v___x_6034_ = lean_unsigned_to_nat(0u);
v___x_6035_ = lean_array_get_size(v_xs_6032_);
v___x_6119_ = lean_nat_dec_lt(v___x_6034_, v___x_6035_);
if (v___x_6119_ == 0)
{
goto v___jp_6036_;
}
else
{
if (v___x_6119_ == 0)
{
goto v___jp_6036_;
}
else
{
size_t v___x_6120_; size_t v___x_6121_; uint8_t v___x_6122_; 
v___x_6120_ = ((size_t)0ULL);
v___x_6121_ = lean_usize_of_nat(v___x_6035_);
v___x_6122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6032_, v___x_6120_, v___x_6121_);
if (v___x_6122_ == 0)
{
goto v___jp_6036_;
}
else
{
lean_object* v___x_6123_; lean_object* v___x_6124_; 
lean_dec_ref(v_toErase_6033_);
lean_dec_ref(v_xs_6032_);
lean_dec_ref(v_fixedParamPerms_6031_);
v___x_6123_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6124_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6123_);
return v___x_6124_;
}
}
}
v___jp_6036_:
{
lean_object* v_numFixed_6037_; lean_object* v_perms_6038_; lean_object* v_revDeps_6039_; uint8_t v___x_6040_; 
v_numFixed_6037_ = lean_ctor_get(v_fixedParamPerms_6031_, 0);
v_perms_6038_ = lean_ctor_get(v_fixedParamPerms_6031_, 1);
lean_inc_ref(v_perms_6038_);
v_revDeps_6039_ = lean_ctor_get(v_fixedParamPerms_6031_, 2);
lean_inc_ref(v_revDeps_6039_);
v___x_6040_ = lean_nat_dec_eq(v_numFixed_6037_, v___x_6035_);
if (v___x_6040_ == 0)
{
lean_object* v___x_6041_; lean_object* v___x_6042_; 
lean_dec_ref(v_revDeps_6039_);
lean_dec_ref(v_perms_6038_);
lean_dec_ref(v_toErase_6033_);
lean_dec_ref(v_xs_6032_);
lean_dec_ref(v_fixedParamPerms_6031_);
v___x_6041_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6042_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6041_);
return v___x_6042_;
}
else
{
lean_object* v___x_6043_; lean_object* v___x_6044_; uint8_t v_changed_6045_; 
v___x_6043_ = lean_array_get_size(v_toErase_6033_);
v___x_6044_ = lean_array_get_size(v_perms_6038_);
v_changed_6045_ = lean_nat_dec_eq(v___x_6043_, v___x_6044_);
if (v_changed_6045_ == 0)
{
lean_object* v___x_6046_; lean_object* v___x_6047_; 
lean_dec_ref(v_revDeps_6039_);
lean_dec_ref(v_perms_6038_);
lean_dec_ref(v_toErase_6033_);
lean_dec_ref(v_xs_6032_);
lean_dec_ref(v_fixedParamPerms_6031_);
v___x_6046_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6047_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6046_);
return v___x_6047_;
}
else
{
uint8_t v_changed_6048_; lean_object* v___x_6049_; lean_object* v_mask_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v_fst_6056_; lean_object* v___x_6058_; uint8_t v_isShared_6059_; uint8_t v_isSharedCheck_6117_; 
v_changed_6048_ = 0;
v___x_6049_ = lean_box(v_changed_6048_);
lean_inc(v_numFixed_6037_);
v_mask_6050_ = lean_mk_array(v_numFixed_6037_, v___x_6049_);
v___x_6051_ = l_Array_toSubarray___redArg(v_toErase_6033_, v___x_6034_, v___x_6043_);
lean_inc_ref(v_perms_6038_);
v___x_6052_ = l_Array_toSubarray___redArg(v_perms_6038_, v___x_6034_, v___x_6044_);
v___x_6053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6051_);
lean_ctor_set(v___x_6053_, 1, v___x_6052_);
v___x_6054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6054_, 0, v_mask_6050_);
lean_ctor_set(v___x_6054_, 1, v___x_6053_);
v___x_6055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6043_, v___x_6043_, v___x_6044_, v___x_6034_, v___x_6054_);
v_fst_6056_ = lean_ctor_get(v___x_6055_, 0);
v_isSharedCheck_6117_ = !lean_is_exclusive(v___x_6055_);
if (v_isSharedCheck_6117_ == 0)
{
lean_object* v_unused_6118_; 
v_unused_6118_ = lean_ctor_get(v___x_6055_, 1);
lean_dec(v_unused_6118_);
v___x_6058_ = v___x_6055_;
v_isShared_6059_ = v_isSharedCheck_6117_;
goto v_resetjp_6057_;
}
else
{
lean_inc(v_fst_6056_);
lean_dec(v___x_6055_);
v___x_6058_ = lean_box(0);
v_isShared_6059_ = v_isSharedCheck_6117_;
goto v_resetjp_6057_;
}
v_resetjp_6057_:
{
lean_object* v___x_6060_; lean_object* v___x_6062_; 
v___x_6060_ = lean_box(v_changed_6045_);
if (v_isShared_6059_ == 0)
{
lean_ctor_set(v___x_6058_, 1, v___x_6060_);
v___x_6062_ = v___x_6058_;
goto v_reusejp_6061_;
}
else
{
lean_object* v_reuseFailAlloc_6116_; 
v_reuseFailAlloc_6116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_fst_6056_);
lean_ctor_set(v_reuseFailAlloc_6116_, 1, v___x_6060_);
v___x_6062_ = v_reuseFailAlloc_6116_;
goto v_reusejp_6061_;
}
v_reusejp_6061_:
{
lean_object* v___x_6063_; lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6112_; 
v___x_6063_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6044_, v_perms_6038_, v___x_6043_, v_fixedParamPerms_6031_, v___x_6062_);
v_isSharedCheck_6112_ = !lean_is_exclusive(v_fixedParamPerms_6031_);
if (v_isSharedCheck_6112_ == 0)
{
lean_object* v_unused_6113_; lean_object* v_unused_6114_; lean_object* v_unused_6115_; 
v_unused_6113_ = lean_ctor_get(v_fixedParamPerms_6031_, 2);
lean_dec(v_unused_6113_);
v_unused_6114_ = lean_ctor_get(v_fixedParamPerms_6031_, 1);
lean_dec(v_unused_6114_);
v_unused_6115_ = lean_ctor_get(v_fixedParamPerms_6031_, 0);
lean_dec(v_unused_6115_);
v___x_6065_ = v_fixedParamPerms_6031_;
v_isShared_6066_ = v_isSharedCheck_6112_;
goto v_resetjp_6064_;
}
else
{
lean_dec(v_fixedParamPerms_6031_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6112_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v_fst_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6110_; 
v_fst_6067_ = lean_ctor_get(v___x_6063_, 0);
v_isSharedCheck_6110_ = !lean_is_exclusive(v___x_6063_);
if (v_isSharedCheck_6110_ == 0)
{
lean_object* v_unused_6111_; 
v_unused_6111_ = lean_ctor_get(v___x_6063_, 1);
lean_dec(v_unused_6111_);
v___x_6069_ = v___x_6063_;
v_isShared_6070_ = v_isSharedCheck_6110_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_fst_6067_);
lean_dec(v___x_6063_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6110_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6076_; 
v___x_6071_ = lean_array_get_size(v_fst_6067_);
v___x_6072_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6073_ = l_Array_toSubarray___redArg(v_fst_6067_, v___x_6034_, v___x_6071_);
v___x_6074_ = l_Array_toSubarray___redArg(v_xs_6032_, v___x_6034_, v___x_6035_);
if (v_isShared_6070_ == 0)
{
lean_ctor_set(v___x_6069_, 1, v___x_6074_);
lean_ctor_set(v___x_6069_, 0, v___x_6073_);
v___x_6076_ = v___x_6069_;
goto v_reusejp_6075_;
}
else
{
lean_object* v_reuseFailAlloc_6109_; 
v_reuseFailAlloc_6109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6109_, 0, v___x_6073_);
lean_ctor_set(v_reuseFailAlloc_6109_, 1, v___x_6074_);
v___x_6076_ = v_reuseFailAlloc_6109_;
goto v_reusejp_6075_;
}
v_reusejp_6075_:
{
lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v_snd_6081_; lean_object* v_snd_6082_; lean_object* v_fst_6083_; lean_object* v_fst_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6107_; 
v___x_6077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6072_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6072_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6079_, 0, v___x_6072_);
lean_ctor_set(v___x_6079_, 1, v___x_6078_);
v___x_6080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6071_, v___x_6034_, v___x_6079_);
v_snd_6081_ = lean_ctor_get(v___x_6080_, 1);
lean_inc(v_snd_6081_);
v_snd_6082_ = lean_ctor_get(v_snd_6081_, 1);
lean_inc(v_snd_6082_);
v_fst_6083_ = lean_ctor_get(v___x_6080_, 0);
lean_inc(v_fst_6083_);
lean_dec_ref(v___x_6080_);
v_fst_6084_ = lean_ctor_get(v_snd_6081_, 0);
v_isSharedCheck_6107_ = !lean_is_exclusive(v_snd_6081_);
if (v_isSharedCheck_6107_ == 0)
{
lean_object* v_unused_6108_; 
v_unused_6108_ = lean_ctor_get(v_snd_6081_, 1);
lean_dec(v_unused_6108_);
v___x_6086_ = v_snd_6081_;
v_isShared_6087_ = v_isSharedCheck_6107_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_fst_6084_);
lean_dec(v_snd_6081_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6107_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v_fst_6088_; lean_object* v___x_6090_; uint8_t v_isShared_6091_; uint8_t v_isSharedCheck_6105_; 
v_fst_6088_ = lean_ctor_get(v_snd_6082_, 0);
v_isSharedCheck_6105_ = !lean_is_exclusive(v_snd_6082_);
if (v_isSharedCheck_6105_ == 0)
{
lean_object* v_unused_6106_; 
v_unused_6106_ = lean_ctor_get(v_snd_6082_, 1);
lean_dec(v_unused_6106_);
v___x_6090_ = v_snd_6082_;
v_isShared_6091_ = v_isSharedCheck_6105_;
goto v_resetjp_6089_;
}
else
{
lean_inc(v_fst_6088_);
lean_dec(v_snd_6082_);
v___x_6090_ = lean_box(0);
v_isShared_6091_ = v_isSharedCheck_6105_;
goto v_resetjp_6089_;
}
v_resetjp_6089_:
{
lean_object* v___x_6092_; size_t v_sz_6093_; size_t v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6097_; 
v___x_6092_ = lean_array_get_size(v_fst_6088_);
v_sz_6093_ = lean_array_size(v_perms_6038_);
v___x_6094_ = ((size_t)0ULL);
v___x_6095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6083_, v_sz_6093_, v___x_6094_, v_perms_6038_);
lean_dec(v_fst_6083_);
if (v_isShared_6066_ == 0)
{
lean_ctor_set(v___x_6065_, 1, v___x_6095_);
lean_ctor_set(v___x_6065_, 0, v___x_6092_);
v___x_6097_ = v___x_6065_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6104_; 
v_reuseFailAlloc_6104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6104_, 0, v___x_6092_);
lean_ctor_set(v_reuseFailAlloc_6104_, 1, v___x_6095_);
lean_ctor_set(v_reuseFailAlloc_6104_, 2, v_revDeps_6039_);
v___x_6097_ = v_reuseFailAlloc_6104_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
lean_object* v___x_6099_; 
if (v_isShared_6091_ == 0)
{
lean_ctor_set(v___x_6090_, 1, v_fst_6084_);
v___x_6099_ = v___x_6090_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6103_; 
v_reuseFailAlloc_6103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6103_, 0, v_fst_6088_);
lean_ctor_set(v_reuseFailAlloc_6103_, 1, v_fst_6084_);
v___x_6099_ = v_reuseFailAlloc_6103_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
lean_object* v___x_6101_; 
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 1, v___x_6099_);
lean_ctor_set(v___x_6086_, 0, v___x_6097_);
v___x_6101_ = v___x_6086_;
goto v_reusejp_6100_;
}
else
{
lean_object* v_reuseFailAlloc_6102_; 
v_reuseFailAlloc_6102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6102_, 0, v___x_6097_);
lean_ctor_set(v_reuseFailAlloc_6102_, 1, v___x_6099_);
v___x_6101_ = v_reuseFailAlloc_6102_;
goto v_reusejp_6100_;
}
v_reusejp_6100_:
{
return v___x_6101_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6125_, lean_object* v___x_6126_, lean_object* v_fixedParamPerms_6127_, lean_object* v_next_6128_, lean_object* v___x_6129_, lean_object* v___x_6130_, lean_object* v_inst_6131_, lean_object* v_R_6132_, lean_object* v_a_6133_, lean_object* v_b_6134_, lean_object* v_c_6135_){
_start:
{
lean_object* v___x_6136_; 
v___x_6136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6125_, v___x_6126_, v_fixedParamPerms_6127_, v_next_6128_, v___x_6129_, v___x_6130_, v_a_6133_, v_b_6134_);
return v___x_6136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6137_, lean_object* v___x_6138_, lean_object* v_fixedParamPerms_6139_, lean_object* v_next_6140_, lean_object* v___x_6141_, lean_object* v___x_6142_, lean_object* v_inst_6143_, lean_object* v_R_6144_, lean_object* v_a_6145_, lean_object* v_b_6146_, lean_object* v_c_6147_){
_start:
{
lean_object* v_res_6148_; 
v_res_6148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6137_, v___x_6138_, v_fixedParamPerms_6139_, v_next_6140_, v___x_6141_, v___x_6142_, v_inst_6143_, v_R_6144_, v_a_6145_, v_b_6146_, v_c_6147_);
lean_dec(v___x_6142_);
lean_dec(v___x_6141_);
lean_dec(v_next_6140_);
lean_dec_ref(v_fixedParamPerms_6139_);
lean_dec_ref(v___x_6138_);
lean_dec(v_upperBound_6137_);
return v_res_6148_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6149_, lean_object* v___x_6150_, lean_object* v___x_6151_, lean_object* v___x_6152_, lean_object* v_fixedParamPerms_6153_, lean_object* v_inst_6154_, lean_object* v_R_6155_, lean_object* v_a_6156_, lean_object* v_b_6157_, lean_object* v_c_6158_){
_start:
{
lean_object* v___x_6159_; 
v___x_6159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6149_, v___x_6150_, v___x_6151_, v___x_6152_, v_fixedParamPerms_6153_, v_a_6156_, v_b_6157_);
return v___x_6159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6160_, lean_object* v___x_6161_, lean_object* v___x_6162_, lean_object* v___x_6163_, lean_object* v_fixedParamPerms_6164_, lean_object* v_inst_6165_, lean_object* v_R_6166_, lean_object* v_a_6167_, lean_object* v_b_6168_, lean_object* v_c_6169_){
_start:
{
lean_object* v_res_6170_; 
v_res_6170_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6160_, v___x_6161_, v___x_6162_, v___x_6163_, v_fixedParamPerms_6164_, v_inst_6165_, v_R_6166_, v_a_6167_, v_b_6168_, v_c_6169_);
lean_dec(v_a_6167_);
lean_dec_ref(v_fixedParamPerms_6164_);
lean_dec(v___x_6163_);
lean_dec(v___x_6162_);
lean_dec_ref(v___x_6161_);
lean_dec(v_upperBound_6160_);
return v_res_6170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6171_, lean_object* v___x_6172_, lean_object* v___x_6173_, lean_object* v_fixedParamPerms_6174_, lean_object* v_inst_6175_, lean_object* v_a_6176_){
_start:
{
lean_object* v___x_6177_; 
v___x_6177_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6171_, v___x_6172_, v___x_6173_, v_fixedParamPerms_6174_, v_a_6176_);
return v___x_6177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6178_, lean_object* v___x_6179_, lean_object* v___x_6180_, lean_object* v_fixedParamPerms_6181_, lean_object* v_inst_6182_, lean_object* v_a_6183_){
_start:
{
lean_object* v_res_6184_; 
v_res_6184_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6178_, v___x_6179_, v___x_6180_, v_fixedParamPerms_6181_, v_inst_6182_, v_a_6183_);
lean_dec_ref(v_fixedParamPerms_6181_);
lean_dec(v___x_6180_);
lean_dec_ref(v___x_6179_);
lean_dec(v___x_6178_);
return v_res_6184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6185_, lean_object* v_inst_6186_, lean_object* v_R_6187_, lean_object* v_a_6188_, lean_object* v_b_6189_, lean_object* v_c_6190_){
_start:
{
lean_object* v___x_6191_; 
v___x_6191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6185_, v_a_6188_, v_b_6189_);
return v___x_6191_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6192_, lean_object* v_inst_6193_, lean_object* v_R_6194_, lean_object* v_a_6195_, lean_object* v_b_6196_, lean_object* v_c_6197_){
_start:
{
lean_object* v_res_6198_; 
v_res_6198_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6192_, v_inst_6193_, v_R_6194_, v_a_6195_, v_b_6196_, v_c_6197_);
lean_dec(v_upperBound_6192_);
return v_res_6198_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6199_, lean_object* v___x_6200_, lean_object* v___x_6201_, lean_object* v_inst_6202_, lean_object* v_R_6203_, lean_object* v_a_6204_, lean_object* v_b_6205_, lean_object* v_c_6206_){
_start:
{
lean_object* v___x_6207_; 
v___x_6207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6199_, v___x_6200_, v___x_6201_, v_a_6204_, v_b_6205_);
return v___x_6207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6208_, lean_object* v___x_6209_, lean_object* v___x_6210_, lean_object* v_inst_6211_, lean_object* v_R_6212_, lean_object* v_a_6213_, lean_object* v_b_6214_, lean_object* v_c_6215_){
_start:
{
lean_object* v_res_6216_; 
v_res_6216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6208_, v___x_6209_, v___x_6210_, v_inst_6211_, v_R_6212_, v_a_6213_, v_b_6214_, v_c_6215_);
lean_dec(v___x_6210_);
lean_dec(v___x_6209_);
lean_dec(v_upperBound_6208_);
return v_res_6216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7(lean_object* v_upperBound_6217_, lean_object* v___x_6218_, lean_object* v_fixedParamPerms_6219_, lean_object* v___x_6220_, lean_object* v___x_6221_, lean_object* v_inst_6222_, lean_object* v_R_6223_, lean_object* v_a_6224_, lean_object* v_b_6225_, lean_object* v_c_6226_){
_start:
{
lean_object* v___x_6227_; 
v___x_6227_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(v_upperBound_6217_, v___x_6218_, v_fixedParamPerms_6219_, v___x_6220_, v___x_6221_, v_a_6224_, v_b_6225_);
return v___x_6227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___boxed(lean_object* v_upperBound_6228_, lean_object* v___x_6229_, lean_object* v_fixedParamPerms_6230_, lean_object* v___x_6231_, lean_object* v___x_6232_, lean_object* v_inst_6233_, lean_object* v_R_6234_, lean_object* v_a_6235_, lean_object* v_b_6236_, lean_object* v_c_6237_){
_start:
{
lean_object* v_res_6238_; 
v_res_6238_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7(v_upperBound_6228_, v___x_6229_, v_fixedParamPerms_6230_, v___x_6231_, v___x_6232_, v_inst_6233_, v_R_6234_, v_a_6235_, v_b_6236_, v_c_6237_);
lean_dec(v___x_6232_);
lean_dec(v___x_6231_);
lean_dec_ref(v_fixedParamPerms_6230_);
lean_dec_ref(v___x_6229_);
lean_dec(v_upperBound_6228_);
return v_res_6238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6296_; uint8_t v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; 
v___x_6296_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6297_ = 0;
v___x_6298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6299_ = l_Lean_registerTraceClass(v___x_6296_, v___x_6297_, v___x_6298_);
return v___x_6299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6300_){
_start:
{
lean_object* v_res_6301_; 
v_res_6301_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6301_;
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
