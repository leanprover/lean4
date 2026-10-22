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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_value;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__1(lean_object* v_x_1185_, lean_object* v_e_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_e_1186_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__1___boxed(lean_object* v_x_1193_, lean_object* v_e_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__1(v_x_1193_, v_e_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v_x_1193_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
return v_x_1201_;
}
else
{
lean_object* v_key_1203_; lean_object* v_value_1204_; lean_object* v_tail_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1228_; 
v_key_1203_ = lean_ctor_get(v_x_1202_, 0);
v_value_1204_ = lean_ctor_get(v_x_1202_, 1);
v_tail_1205_ = lean_ctor_get(v_x_1202_, 2);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_x_1202_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1207_ = v_x_1202_;
v_isShared_1208_ = v_isSharedCheck_1228_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_tail_1205_);
lean_inc(v_value_1204_);
lean_inc(v_key_1203_);
lean_dec(v_x_1202_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1228_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; uint64_t v___x_1212_; uint64_t v_fold_1213_; uint64_t v___x_1214_; uint64_t v___x_1215_; uint64_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1209_ = lean_array_get_size(v_x_1201_);
v___x_1210_ = l_Lean_ExprStructEq_hash(v_key_1203_);
v___x_1211_ = 32ULL;
v___x_1212_ = lean_uint64_shift_right(v___x_1210_, v___x_1211_);
v_fold_1213_ = lean_uint64_xor(v___x_1210_, v___x_1212_);
v___x_1214_ = 16ULL;
v___x_1215_ = lean_uint64_shift_right(v_fold_1213_, v___x_1214_);
v___x_1216_ = lean_uint64_xor(v_fold_1213_, v___x_1215_);
v___x_1217_ = lean_uint64_to_usize(v___x_1216_);
v___x_1218_ = lean_usize_of_nat(v___x_1209_);
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_sub(v___x_1218_, v___x_1219_);
v___x_1221_ = lean_usize_land(v___x_1217_, v___x_1220_);
v___x_1222_ = lean_array_uget_borrowed(v_x_1201_, v___x_1221_);
lean_inc(v___x_1222_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 2, v___x_1222_);
v___x_1224_ = v___x_1207_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_key_1203_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_value_1204_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_array_uset(v_x_1201_, v___x_1221_, v___x_1224_);
v_x_1201_ = v___x_1225_;
v_x_1202_ = v_tail_1205_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(lean_object* v_i_1229_, lean_object* v_source_1230_, lean_object* v_target_1231_){
_start:
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = lean_array_get_size(v_source_1230_);
v___x_1233_ = lean_nat_dec_lt(v_i_1229_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec_ref(v_source_1230_);
lean_dec(v_i_1229_);
return v_target_1231_;
}
else
{
lean_object* v_es_1234_; lean_object* v___x_1235_; lean_object* v_source_1236_; lean_object* v_target_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_es_1234_ = lean_array_fget(v_source_1230_, v_i_1229_);
v___x_1235_ = lean_box(0);
v_source_1236_ = lean_array_fset(v_source_1230_, v_i_1229_, v___x_1235_);
v_target_1237_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_target_1231_, v_es_1234_);
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_add(v_i_1229_, v___x_1238_);
lean_dec(v_i_1229_);
v_i_1229_ = v___x_1239_;
v_source_1230_ = v_source_1236_;
v_target_1231_ = v_target_1237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(lean_object* v_data_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_nbuckets_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1242_ = lean_array_get_size(v_data_1241_);
v___x_1243_ = lean_unsigned_to_nat(2u);
v_nbuckets_1244_ = lean_nat_mul(v___x_1242_, v___x_1243_);
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = lean_box(0);
v___x_1247_ = lean_mk_array(v_nbuckets_1244_, v___x_1246_);
v___x_1248_ = lean_array_propagate_mark(v_data_1241_, v___x_1247_);
v___x_1249_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1245_, v_data_1241_, v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(lean_object* v_a_1250_, lean_object* v_b_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_dec(v_b_1251_);
lean_dec_ref(v_a_1250_);
return v_x_1252_;
}
else
{
lean_object* v_key_1253_; lean_object* v_value_1254_; lean_object* v_tail_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1267_; 
v_key_1253_ = lean_ctor_get(v_x_1252_, 0);
v_value_1254_ = lean_ctor_get(v_x_1252_, 1);
v_tail_1255_ = lean_ctor_get(v_x_1252_, 2);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_x_1252_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1257_ = v_x_1252_;
v_isShared_1258_ = v_isSharedCheck_1267_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_tail_1255_);
lean_inc(v_value_1254_);
lean_inc(v_key_1253_);
lean_dec(v_x_1252_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1267_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
uint8_t v___x_1259_; 
v___x_1259_ = l_Lean_ExprStructEq_beq(v_key_1253_, v_a_1250_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1250_, v_b_1251_, v_tail_1255_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 2, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_key_1253_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_value_1254_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
else
{
lean_object* v___x_1265_; 
lean_dec(v_value_1254_);
lean_dec(v_key_1253_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_b_1251_);
lean_ctor_set(v___x_1257_, 0, v_a_1250_);
v___x_1265_ = v___x_1257_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1250_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_b_1251_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_tail_1255_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(lean_object* v_a_1268_, lean_object* v_x_1269_){
_start:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
uint8_t v___x_1270_; 
v___x_1270_ = 0;
return v___x_1270_;
}
else
{
lean_object* v_key_1271_; lean_object* v_tail_1272_; uint8_t v___x_1273_; 
v_key_1271_ = lean_ctor_get(v_x_1269_, 0);
v_tail_1272_ = lean_ctor_get(v_x_1269_, 2);
v___x_1273_ = l_Lean_ExprStructEq_beq(v_key_1271_, v_a_1268_);
if (v___x_1273_ == 0)
{
v_x_1269_ = v_tail_1272_;
goto _start;
}
else
{
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg___boxed(lean_object* v_a_1275_, lean_object* v_x_1276_){
_start:
{
uint8_t v_res_1277_; lean_object* v_r_1278_; 
v_res_1277_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1275_, v_x_1276_);
lean_dec(v_x_1276_);
lean_dec_ref(v_a_1275_);
v_r_1278_ = lean_box(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(lean_object* v_m_1279_, lean_object* v_a_1280_, lean_object* v_b_1281_){
_start:
{
lean_object* v_size_1282_; lean_object* v_buckets_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1326_; 
v_size_1282_ = lean_ctor_get(v_m_1279_, 0);
v_buckets_1283_ = lean_ctor_get(v_m_1279_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_m_1279_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1285_ = v_m_1279_;
v_isShared_1286_ = v_isSharedCheck_1326_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_buckets_1283_);
lean_inc(v_size_1282_);
lean_dec(v_m_1279_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1326_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; uint64_t v___x_1288_; uint64_t v___x_1289_; uint64_t v___x_1290_; uint64_t v_fold_1291_; uint64_t v___x_1292_; uint64_t v___x_1293_; uint64_t v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; lean_object* v_bkt_1300_; uint8_t v___x_1301_; 
v___x_1287_ = lean_array_get_size(v_buckets_1283_);
v___x_1288_ = l_Lean_ExprStructEq_hash(v_a_1280_);
v___x_1289_ = 32ULL;
v___x_1290_ = lean_uint64_shift_right(v___x_1288_, v___x_1289_);
v_fold_1291_ = lean_uint64_xor(v___x_1288_, v___x_1290_);
v___x_1292_ = 16ULL;
v___x_1293_ = lean_uint64_shift_right(v_fold_1291_, v___x_1292_);
v___x_1294_ = lean_uint64_xor(v_fold_1291_, v___x_1293_);
v___x_1295_ = lean_uint64_to_usize(v___x_1294_);
v___x_1296_ = lean_usize_of_nat(v___x_1287_);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_sub(v___x_1296_, v___x_1297_);
v___x_1299_ = lean_usize_land(v___x_1295_, v___x_1298_);
v_bkt_1300_ = lean_array_uget_borrowed(v_buckets_1283_, v___x_1299_);
v___x_1301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_1280_, v_bkt_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v_size_x27_1303_; lean_object* v___x_1304_; lean_object* v_buckets_x27_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1302_ = lean_unsigned_to_nat(1u);
v_size_x27_1303_ = lean_nat_add(v_size_1282_, v___x_1302_);
lean_dec(v_size_1282_);
lean_inc(v_bkt_1300_);
v___x_1304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1304_, 0, v_a_1280_);
lean_ctor_set(v___x_1304_, 1, v_b_1281_);
lean_ctor_set(v___x_1304_, 2, v_bkt_1300_);
v_buckets_x27_1305_ = lean_array_uset(v_buckets_1283_, v___x_1299_, v___x_1304_);
v___x_1306_ = lean_unsigned_to_nat(4u);
v___x_1307_ = lean_nat_mul(v_size_x27_1303_, v___x_1306_);
v___x_1308_ = lean_unsigned_to_nat(3u);
v___x_1309_ = lean_nat_div(v___x_1307_, v___x_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_array_get_size(v_buckets_x27_1305_);
v___x_1311_ = lean_nat_dec_le(v___x_1309_, v___x_1310_);
lean_dec(v___x_1309_);
if (v___x_1311_ == 0)
{
lean_object* v_val_1312_; lean_object* v___x_1314_; 
v_val_1312_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_buckets_x27_1305_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_val_1312_);
lean_ctor_set(v___x_1285_, 0, v_size_x27_1303_);
v___x_1314_ = v___x_1285_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_size_x27_1303_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_val_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
else
{
lean_object* v___x_1317_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_buckets_x27_1305_);
lean_ctor_set(v___x_1285_, 0, v_size_x27_1303_);
v___x_1317_ = v___x_1285_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_size_x27_1303_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_buckets_x27_1305_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v___x_1319_; lean_object* v_buckets_x27_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_inc(v_bkt_1300_);
v___x_1319_ = lean_box(0);
v_buckets_x27_1320_ = lean_array_uset(v_buckets_1283_, v___x_1299_, v___x_1319_);
v___x_1321_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_1280_, v_b_1281_, v_bkt_1300_);
v___x_1322_ = lean_array_uset(v_buckets_x27_1320_, v___x_1299_, v___x_1321_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1322_);
v___x_1324_ = v___x_1285_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_size_1282_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(lean_object* v_a_1327_, lean_object* v_e_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1331_ = lean_st_ref_take(v_a_1327_);
v___x_1332_ = lean_box(0);
v___x_1333_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1331_, v_e_1328_, v_a_1329_);
v___x_1334_ = lean_st_ref_put(v_a_1327_, v___x_1333_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed(lean_object* v_a_1335_, lean_object* v_e_1336_, lean_object* v_a_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2(v_a_1335_, v_e_1336_, v_a_1337_);
lean_dec(v_a_1335_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(lean_object* v_k_1340_, lean_object* v___y_1341_, lean_object* v_b_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1341_);
v___x_1348_ = lean_apply_7(v_k_1340_, v_b_1342_, v___y_1341_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, lean_box(0));
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed(lean_object* v_k_1349_, lean_object* v___y_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0(v_k_1349_, v___y_1350_, v_b_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(lean_object* v_name_1358_, uint8_t v_bi_1359_, lean_object* v_type_1360_, lean_object* v_k_1361_, uint8_t v_kind_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___f_1369_; lean_object* v___x_1370_; 
lean_inc(v___y_1363_);
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1369_, 0, v_k_1361_);
lean_closure_set(v___f_1369_, 1, v___y_1363_);
v___x_1370_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1358_, v_bi_1359_, v_type_1360_, v___f_1369_, v_kind_1362_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1370_) == 0)
{
return v___x_1370_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___boxed(lean_object* v_name_1379_, lean_object* v_bi_1380_, lean_object* v_type_1381_, lean_object* v_k_1382_, lean_object* v_kind_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v_bi_boxed_1390_; uint8_t v_kind_boxed_1391_; lean_object* v_res_1392_; 
v_bi_boxed_1390_ = lean_unbox(v_bi_1380_);
v_kind_boxed_1391_ = lean_unbox(v_kind_1383_);
v_res_1392_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_1379_, v_bi_boxed_1390_, v_type_1381_, v_k_1382_, v_kind_boxed_1391_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__2(lean_object* v___x_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1393_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__2___boxed(lean_object* v___x_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__2(v___x_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(lean_object* v_name_1407_, lean_object* v_type_1408_, lean_object* v_val_1409_, lean_object* v_k_1410_, uint8_t v_nondep_1411_, uint8_t v_kind_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___f_1419_; lean_object* v___x_1420_; 
lean_inc(v___y_1413_);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1419_, 0, v_k_1410_);
lean_closure_set(v___f_1419_, 1, v___y_1413_);
v___x_1420_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1407_, v_type_1408_, v_val_1409_, v___f_1419_, v_nondep_1411_, v_kind_1412_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
if (lean_obj_tag(v___x_1420_) == 0)
{
return v___x_1420_;
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg___boxed(lean_object* v_name_1429_, lean_object* v_type_1430_, lean_object* v_val_1431_, lean_object* v_k_1432_, lean_object* v_nondep_1433_, lean_object* v_kind_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v_nondep_boxed_1441_; uint8_t v_kind_boxed_1442_; lean_object* v_res_1443_; 
v_nondep_boxed_1441_ = lean_unbox(v_nondep_1433_);
v_kind_boxed_1442_ = lean_unbox(v_kind_1434_);
v_res_1443_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_1429_, v_type_1430_, v_val_1431_, v_k_1432_, v_nondep_boxed_1441_, v_kind_boxed_1442_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___redArg(lean_object* v_a_1444_, lean_object* v_x_1445_){
_start:
{
if (lean_obj_tag(v_x_1445_) == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_box(0);
return v___x_1446_;
}
else
{
lean_object* v_key_1447_; lean_object* v_value_1448_; lean_object* v_tail_1449_; uint8_t v___x_1450_; 
v_key_1447_ = lean_ctor_get(v_x_1445_, 0);
v_value_1448_ = lean_ctor_get(v_x_1445_, 1);
v_tail_1449_ = lean_ctor_get(v_x_1445_, 2);
v___x_1450_ = l_Lean_ExprStructEq_beq(v_key_1447_, v_a_1444_);
if (v___x_1450_ == 0)
{
v_x_1445_ = v_tail_1449_;
goto _start;
}
else
{
lean_object* v___x_1452_; 
lean_inc(v_value_1448_);
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v_value_1448_);
return v___x_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___redArg___boxed(lean_object* v_a_1453_, lean_object* v_x_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___redArg(v_a_1453_, v_x_1454_);
lean_dec(v_x_1454_);
lean_dec_ref(v_a_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___redArg(lean_object* v_m_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_buckets_1458_; lean_object* v___x_1459_; uint64_t v___x_1460_; uint64_t v___x_1461_; uint64_t v___x_1462_; uint64_t v_fold_1463_; uint64_t v___x_1464_; uint64_t v___x_1465_; uint64_t v___x_1466_; size_t v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_buckets_1458_ = lean_ctor_get(v_m_1456_, 1);
v___x_1459_ = lean_array_get_size(v_buckets_1458_);
v___x_1460_ = l_Lean_ExprStructEq_hash(v_a_1457_);
v___x_1461_ = 32ULL;
v___x_1462_ = lean_uint64_shift_right(v___x_1460_, v___x_1461_);
v_fold_1463_ = lean_uint64_xor(v___x_1460_, v___x_1462_);
v___x_1464_ = 16ULL;
v___x_1465_ = lean_uint64_shift_right(v_fold_1463_, v___x_1464_);
v___x_1466_ = lean_uint64_xor(v_fold_1463_, v___x_1465_);
v___x_1467_ = lean_uint64_to_usize(v___x_1466_);
v___x_1468_ = lean_usize_of_nat(v___x_1459_);
v___x_1469_ = ((size_t)1ULL);
v___x_1470_ = lean_usize_sub(v___x_1468_, v___x_1469_);
v___x_1471_ = lean_usize_land(v___x_1467_, v___x_1470_);
v___x_1472_ = lean_array_uget_borrowed(v_buckets_1458_, v___x_1471_);
v___x_1473_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___redArg(v_a_1457_, v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_m_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___redArg(v_m_1474_, v_a_1475_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_m_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_object* v_00_u03b1_1477_, lean_object* v_x_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_apply_1(v_x_1478_, lean_box(0));
v___x_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_x_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(v_00_u03b1_1486_, v_x_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = l_Lean_maxRecDepthErrorMessage;
v___x_1500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__3);
v___x_1502_ = l_Lean_MessageData_ofFormat(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__4);
v___x_1504_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__2));
v___x_1505_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(lean_object* v_ref_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___closed__5);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_ref_1506_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1511_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(lean_object* v_x_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___y_1522_; lean_object* v_toCold_1531_; lean_object* v_currRecDepth_1532_; lean_object* v_ref_1533_; uint16_t v_optionFlags_1534_; uint8_t v_suppressElabErrors_1535_; uint8_t v_isRecordingDeps_1536_; lean_object* v_maxRecDepth_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_toCold_1531_ = lean_ctor_get(v___y_1518_, 0);
v_currRecDepth_1532_ = lean_ctor_get(v___y_1518_, 1);
v_ref_1533_ = lean_ctor_get(v___y_1518_, 2);
v_optionFlags_1534_ = lean_ctor_get_uint16(v___y_1518_, sizeof(void*)*3);
v_suppressElabErrors_1535_ = lean_ctor_get_uint8(v___y_1518_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1536_ = lean_ctor_get_uint8(v___y_1518_, sizeof(void*)*3 + 3);
v_maxRecDepth_1542_ = lean_ctor_get(v_toCold_1531_, 3);
v___x_1543_ = lean_unsigned_to_nat(0u);
v___x_1544_ = lean_nat_dec_eq(v_maxRecDepth_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_nat_dec_eq(v_currRecDepth_1532_, v_maxRecDepth_1542_);
if (v___x_1545_ == 0)
{
goto v___jp_1537_;
}
else
{
lean_object* v___x_1546_; 
lean_dec_ref(v_x_1514_);
lean_inc(v_ref_1533_);
v___x_1546_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1533_);
v___y_1522_ = v___x_1546_;
goto v___jp_1521_;
}
}
else
{
goto v___jp_1537_;
}
v___jp_1521_:
{
if (lean_obj_tag(v___y_1522_) == 0)
{
return v___y_1522_;
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v_a_1523_ = lean_ctor_get(v___y_1522_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___y_1522_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___y_1522_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___y_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
v___jp_1537_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_nat_add(v_currRecDepth_1532_, v___x_1538_);
lean_inc(v_ref_1533_);
lean_inc_ref(v_toCold_1531_);
v___x_1540_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1540_, 0, v_toCold_1531_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
lean_ctor_set(v___x_1540_, 2, v_ref_1533_);
lean_ctor_set_uint16(v___x_1540_, sizeof(void*)*3, v_optionFlags_1534_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*3 + 2, v_suppressElabErrors_1535_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*3 + 3, v_isRecordingDeps_1536_);
lean_inc(v___y_1519_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
v___x_1541_ = lean_apply_6(v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___x_1540_, v___y_1519_, lean_box(0));
v___y_1522_ = v___x_1541_;
goto v___jp_1521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_1555_, lean_object* v_pre_1556_, lean_object* v_post_1557_, lean_object* v_usedLetOnly_1558_, lean_object* v_skipConstInApp_1559_, lean_object* v_skipInstances_1560_, lean_object* v_postApp_1561_, lean_object* v_body_1562_, lean_object* v_x_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v_usedLetOnly_boxed_1570_; uint8_t v_skipConstInApp_boxed_1571_; uint8_t v_skipInstances_boxed_1572_; lean_object* v_res_1573_; 
v_usedLetOnly_boxed_1570_ = lean_unbox(v_usedLetOnly_1558_);
v_skipConstInApp_boxed_1571_ = lean_unbox(v_skipConstInApp_1559_);
v_skipInstances_boxed_1572_ = lean_unbox(v_skipInstances_1560_);
v_res_1573_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_1555_, v_pre_1556_, v_post_1557_, v_usedLetOnly_boxed_1570_, v_skipConstInApp_boxed_1571_, v_skipInstances_boxed_1572_, v_postApp_1561_, v_body_1562_, v_x_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1577_, lean_object* v_pre_1578_, lean_object* v_post_1579_, uint8_t v_usedLetOnly_1580_, uint8_t v_skipConstInApp_1581_, uint8_t v_skipInstances_1582_, lean_object* v_postApp_1583_, lean_object* v_body_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_array_push(v_fvars_1577_, v_x_1585_);
v___x_1593_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1578_, v_post_1579_, v_usedLetOnly_1580_, v_skipConstInApp_1581_, v_skipInstances_1582_, v_postApp_1583_, v___x_1592_, v_body_1584_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1594_, lean_object* v_pre_1595_, lean_object* v_post_1596_, lean_object* v_usedLetOnly_1597_, lean_object* v_skipConstInApp_1598_, lean_object* v_skipInstances_1599_, lean_object* v_postApp_1600_, lean_object* v_body_1601_, lean_object* v_x_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v_usedLetOnly_boxed_1609_; uint8_t v_skipConstInApp_boxed_1610_; uint8_t v_skipInstances_boxed_1611_; lean_object* v_res_1612_; 
v_usedLetOnly_boxed_1609_ = lean_unbox(v_usedLetOnly_1597_);
v_skipConstInApp_boxed_1610_ = lean_unbox(v_skipConstInApp_1598_);
v_skipInstances_boxed_1611_ = lean_unbox(v_skipInstances_1599_);
v_res_1612_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1594_, v_pre_1595_, v_post_1596_, v_usedLetOnly_boxed_1609_, v_skipConstInApp_boxed_1610_, v_skipInstances_boxed_1611_, v_postApp_1600_, v_body_1601_, v_x_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_pre_1613_, lean_object* v_post_1614_, uint8_t v_usedLetOnly_1615_, uint8_t v_skipConstInApp_1616_, uint8_t v_skipInstances_1617_, lean_object* v_postApp_1618_, lean_object* v_e_1619_, lean_object* v_a_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
lean_inc_ref(v_post_1614_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
lean_inc_ref(v_e_1619_);
v___x_1626_ = lean_apply_6(v_post_1614_, v_e_1619_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, lean_box(0));
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1645_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1645_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1645_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
switch(lean_obj_tag(v_a_1627_))
{
case 0:
{
lean_object* v_e_1631_; lean_object* v___x_1633_; 
lean_dec_ref(v_e_1619_);
lean_dec_ref(v_postApp_1618_);
lean_dec_ref(v_post_1614_);
lean_dec_ref(v_pre_1613_);
v_e_1631_ = lean_ctor_get(v_a_1627_, 0);
lean_inc_ref(v_e_1631_);
lean_dec_ref_known(v_a_1627_, 1);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v_e_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_e_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
case 1:
{
lean_object* v_e_1635_; lean_object* v___x_1636_; 
lean_del_object(v___x_1629_);
lean_dec_ref(v_e_1619_);
v_e_1635_ = lean_ctor_get(v_a_1627_, 0);
lean_inc_ref(v_e_1635_);
lean_dec_ref_known(v_a_1627_, 1);
v___x_1636_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1613_, v_post_1614_, v_usedLetOnly_1615_, v_skipConstInApp_1616_, v_skipInstances_1617_, v_postApp_1618_, v_e_1635_, v_a_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
return v___x_1636_;
}
default: 
{
lean_object* v_e_x3f_1637_; 
lean_dec_ref(v_postApp_1618_);
lean_dec_ref(v_post_1614_);
lean_dec_ref(v_pre_1613_);
v_e_x3f_1637_ = lean_ctor_get(v_a_1627_, 0);
lean_inc(v_e_x3f_1637_);
lean_dec_ref_known(v_a_1627_, 1);
if (lean_obj_tag(v_e_x3f_1637_) == 0)
{
lean_object* v___x_1639_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v_e_1619_);
v___x_1639_ = v___x_1629_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_e_1619_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v_val_1641_; lean_object* v___x_1643_; 
lean_dec_ref(v_e_1619_);
v_val_1641_ = lean_ctor_get(v_e_x3f_1637_, 0);
lean_inc(v_val_1641_);
lean_dec_ref_known(v_e_x3f_1637_, 1);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v_val_1641_);
v___x_1643_ = v___x_1629_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_val_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v_e_1619_);
lean_dec_ref(v_postApp_1618_);
lean_dec_ref(v_post_1614_);
lean_dec_ref(v_pre_1613_);
v_a_1646_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1626_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1626_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1654_, lean_object* v_post_1655_, uint8_t v_usedLetOnly_1656_, uint8_t v_skipConstInApp_1657_, uint8_t v_skipInstances_1658_, lean_object* v_postApp_1659_, lean_object* v_fvars_1660_, lean_object* v_e_1661_, lean_object* v_a_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
if (lean_obj_tag(v_e_1661_) == 6)
{
lean_object* v_binderName_1668_; lean_object* v_binderType_1669_; lean_object* v_body_1670_; uint8_t v_binderInfo_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___f_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_binderName_1668_ = lean_ctor_get(v_e_1661_, 0);
lean_inc(v_binderName_1668_);
v_binderType_1669_ = lean_ctor_get(v_e_1661_, 1);
lean_inc_ref(v_binderType_1669_);
v_body_1670_ = lean_ctor_get(v_e_1661_, 2);
lean_inc_ref(v_body_1670_);
v_binderInfo_1671_ = lean_ctor_get_uint8(v_e_1661_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1661_, 3);
v___x_1672_ = lean_box(v_usedLetOnly_1656_);
v___x_1673_ = lean_box(v_skipConstInApp_1657_);
v___x_1674_ = lean_box(v_skipInstances_1658_);
lean_inc_ref(v_postApp_1659_);
lean_inc_ref(v_post_1655_);
lean_inc_ref(v_pre_1654_);
lean_inc_ref(v_fvars_1660_);
v___f_1675_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1675_, 0, v_fvars_1660_);
lean_closure_set(v___f_1675_, 1, v_pre_1654_);
lean_closure_set(v___f_1675_, 2, v_post_1655_);
lean_closure_set(v___f_1675_, 3, v___x_1672_);
lean_closure_set(v___f_1675_, 4, v___x_1673_);
lean_closure_set(v___f_1675_, 5, v___x_1674_);
lean_closure_set(v___f_1675_, 6, v_postApp_1659_);
lean_closure_set(v___f_1675_, 7, v_body_1670_);
v___x_1676_ = lean_expr_instantiate_rev(v_binderType_1669_, v_fvars_1660_);
lean_dec_ref(v_fvars_1660_);
lean_dec_ref(v_binderType_1669_);
v___x_1677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1654_, v_post_1655_, v_usedLetOnly_1656_, v_skipConstInApp_1657_, v_skipInstances_1658_, v_postApp_1659_, v___x_1676_, v_a_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v___x_1679_ = 0;
v___x_1680_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1668_, v_binderInfo_1671_, v_a_1678_, v___f_1675_, v___x_1679_, v_a_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1680_;
}
else
{
lean_dec_ref(v___f_1675_);
lean_dec(v_binderName_1668_);
return v___x_1677_;
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_expr_instantiate_rev(v_e_1661_, v_fvars_1660_);
lean_dec_ref(v_e_1661_);
lean_inc_ref(v_postApp_1659_);
lean_inc_ref(v_post_1655_);
lean_inc_ref(v_pre_1654_);
v___x_1682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1654_, v_post_1655_, v_usedLetOnly_1656_, v_skipConstInApp_1657_, v_skipInstances_1658_, v_postApp_1659_, v___x_1681_, v_a_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; uint8_t v___x_1684_; uint8_t v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
v___x_1684_ = 0;
v___x_1685_ = 1;
v___x_1686_ = 1;
v___x_1687_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1660_, v_a_1683_, v___x_1684_, v_usedLetOnly_1656_, v___x_1684_, v___x_1685_, v___x_1686_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec_ref(v_fvars_1660_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1654_, v_post_1655_, v_usedLetOnly_1656_, v_skipConstInApp_1657_, v_skipInstances_1658_, v_postApp_1659_, v_a_1688_, v_a_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1689_;
}
else
{
lean_dec_ref(v_postApp_1659_);
lean_dec_ref(v_post_1655_);
lean_dec_ref(v_pre_1654_);
return v___x_1687_;
}
}
else
{
lean_dec_ref(v_fvars_1660_);
lean_dec_ref(v_postApp_1659_);
lean_dec_ref(v_post_1655_);
lean_dec_ref(v_pre_1654_);
return v___x_1682_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1690_, lean_object* v_pre_1691_, lean_object* v_post_1692_, uint8_t v_usedLetOnly_1693_, uint8_t v_skipConstInApp_1694_, uint8_t v_skipInstances_1695_, lean_object* v_postApp_1696_, lean_object* v_body_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_array_push(v_fvars_1690_, v_x_1698_);
v___x_1706_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1691_, v_post_1692_, v_usedLetOnly_1693_, v_skipConstInApp_1694_, v_skipInstances_1695_, v_postApp_1696_, v___x_1705_, v_body_1697_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1707_, lean_object* v_pre_1708_, lean_object* v_post_1709_, lean_object* v_usedLetOnly_1710_, lean_object* v_skipConstInApp_1711_, lean_object* v_skipInstances_1712_, lean_object* v_postApp_1713_, lean_object* v_body_1714_, lean_object* v_x_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v_usedLetOnly_boxed_1722_; uint8_t v_skipConstInApp_boxed_1723_; uint8_t v_skipInstances_boxed_1724_; lean_object* v_res_1725_; 
v_usedLetOnly_boxed_1722_ = lean_unbox(v_usedLetOnly_1710_);
v_skipConstInApp_boxed_1723_ = lean_unbox(v_skipConstInApp_1711_);
v_skipInstances_boxed_1724_ = lean_unbox(v_skipInstances_1712_);
v_res_1725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1707_, v_pre_1708_, v_post_1709_, v_usedLetOnly_boxed_1722_, v_skipConstInApp_boxed_1723_, v_skipInstances_boxed_1724_, v_postApp_1713_, v_body_1714_, v_x_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1726_, lean_object* v_post_1727_, uint8_t v_usedLetOnly_1728_, uint8_t v_skipConstInApp_1729_, uint8_t v_skipInstances_1730_, lean_object* v_postApp_1731_, lean_object* v_fvars_1732_, lean_object* v_e_1733_, lean_object* v_a_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
if (lean_obj_tag(v_e_1733_) == 8)
{
lean_object* v_declName_1740_; lean_object* v_type_1741_; lean_object* v_value_1742_; lean_object* v_body_1743_; uint8_t v_nondep_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___f_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_declName_1740_ = lean_ctor_get(v_e_1733_, 0);
lean_inc(v_declName_1740_);
v_type_1741_ = lean_ctor_get(v_e_1733_, 1);
lean_inc_ref(v_type_1741_);
v_value_1742_ = lean_ctor_get(v_e_1733_, 2);
lean_inc_ref(v_value_1742_);
v_body_1743_ = lean_ctor_get(v_e_1733_, 3);
lean_inc_ref(v_body_1743_);
v_nondep_1744_ = lean_ctor_get_uint8(v_e_1733_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1733_, 4);
v___x_1745_ = lean_box(v_usedLetOnly_1728_);
v___x_1746_ = lean_box(v_skipConstInApp_1729_);
v___x_1747_ = lean_box(v_skipInstances_1730_);
lean_inc_ref_n(v_postApp_1731_, 2);
lean_inc_ref_n(v_post_1727_, 2);
lean_inc_ref_n(v_pre_1726_, 2);
lean_inc_ref(v_fvars_1732_);
v___f_1748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1748_, 0, v_fvars_1732_);
lean_closure_set(v___f_1748_, 1, v_pre_1726_);
lean_closure_set(v___f_1748_, 2, v_post_1727_);
lean_closure_set(v___f_1748_, 3, v___x_1745_);
lean_closure_set(v___f_1748_, 4, v___x_1746_);
lean_closure_set(v___f_1748_, 5, v___x_1747_);
lean_closure_set(v___f_1748_, 6, v_postApp_1731_);
lean_closure_set(v___f_1748_, 7, v_body_1743_);
v___x_1749_ = lean_expr_instantiate_rev(v_type_1741_, v_fvars_1732_);
lean_dec_ref(v_type_1741_);
v___x_1750_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1726_, v_post_1727_, v_usedLetOnly_1728_, v_skipConstInApp_1729_, v_skipInstances_1730_, v_postApp_1731_, v___x_1749_, v_a_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = lean_expr_instantiate_rev(v_value_1742_, v_fvars_1732_);
lean_dec_ref(v_fvars_1732_);
lean_dec_ref(v_value_1742_);
v___x_1753_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1726_, v_post_1727_, v_usedLetOnly_1728_, v_skipConstInApp_1729_, v_skipInstances_1730_, v_postApp_1731_, v___x_1752_, v_a_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = 0;
v___x_1756_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1740_, v_a_1751_, v_a_1754_, v___f_1748_, v_nondep_1744_, v___x_1755_, v_a_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1756_;
}
else
{
lean_dec(v_a_1751_);
lean_dec_ref(v___f_1748_);
lean_dec(v_declName_1740_);
return v___x_1753_;
}
}
else
{
lean_dec_ref(v___f_1748_);
lean_dec_ref(v_value_1742_);
lean_dec(v_declName_1740_);
lean_dec_ref(v_fvars_1732_);
lean_dec_ref(v_postApp_1731_);
lean_dec_ref(v_post_1727_);
lean_dec_ref(v_pre_1726_);
return v___x_1750_;
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_expr_instantiate_rev(v_e_1733_, v_fvars_1732_);
lean_dec_ref(v_e_1733_);
lean_inc_ref(v_postApp_1731_);
lean_inc_ref(v_post_1727_);
lean_inc_ref(v_pre_1726_);
v___x_1758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1726_, v_post_1727_, v_usedLetOnly_1728_, v_skipConstInApp_1729_, v_skipInstances_1730_, v_postApp_1731_, v___x_1757_, v_a_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; uint8_t v___x_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = 0;
v___x_1761_ = 1;
v___x_1762_ = l_Lean_Meta_mkLetFVars(v_fvars_1732_, v_a_1759_, v_usedLetOnly_1728_, v___x_1760_, v___x_1761_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v_fvars_1732_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1726_, v_post_1727_, v_usedLetOnly_1728_, v_skipConstInApp_1729_, v_skipInstances_1730_, v_postApp_1731_, v_a_1763_, v_a_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1764_;
}
else
{
lean_dec_ref(v_postApp_1731_);
lean_dec_ref(v_post_1727_);
lean_dec_ref(v_pre_1726_);
return v___x_1762_;
}
}
else
{
lean_dec_ref(v_fvars_1732_);
lean_dec_ref(v_postApp_1731_);
lean_dec_ref(v_post_1727_);
lean_dec_ref(v_pre_1726_);
return v___x_1758_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1765_; lean_object* v_dummy_1766_; 
v___x_1765_ = lean_box(0);
v_dummy_1766_ = l_Lean_Expr_sort___override(v___x_1765_);
return v_dummy_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1767_, lean_object* v_post_1768_, uint8_t v_usedLetOnly_1769_, uint8_t v_skipConstInApp_1770_, uint8_t v_skipInstances_1771_, lean_object* v_postApp_1772_, size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_bs_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v___x_1782_; 
v___x_1782_ = lean_usize_dec_lt(v_i_1774_, v_sz_1773_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; 
lean_dec_ref(v_postApp_1772_);
lean_dec_ref(v_post_1768_);
lean_dec_ref(v_pre_1767_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_bs_1775_);
return v___x_1783_;
}
else
{
lean_object* v_v_1784_; lean_object* v___x_1785_; lean_object* v_bs_x27_1786_; lean_object* v___x_1787_; 
v_v_1784_ = lean_array_uget(v_bs_1775_, v_i_1774_);
v___x_1785_ = lean_unsigned_to_nat(0u);
v_bs_x27_1786_ = lean_array_uset(v_bs_1775_, v_i_1774_, v___x_1785_);
lean_inc_ref(v_postApp_1772_);
lean_inc_ref(v_post_1768_);
lean_inc_ref(v_pre_1767_);
v___x_1787_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1767_, v_post_1768_, v_usedLetOnly_1769_, v_skipConstInApp_1770_, v_skipInstances_1771_, v_postApp_1772_, v_v_1784_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; size_t v___x_1789_; size_t v___x_1790_; lean_object* v___x_1791_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___x_1789_ = ((size_t)1ULL);
v___x_1790_ = lean_usize_add(v_i_1774_, v___x_1789_);
v___x_1791_ = lean_array_uset(v_bs_x27_1786_, v_i_1774_, v_a_1788_);
v_i_1774_ = v___x_1790_;
v_bs_1775_ = v___x_1791_;
goto _start;
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v_bs_x27_1786_);
lean_dec_ref(v_postApp_1772_);
lean_dec_ref(v_post_1768_);
lean_dec_ref(v_pre_1767_);
v_a_1793_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1787_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1787_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__0(lean_object* v_pre_1801_, lean_object* v_post_1802_, uint8_t v_usedLetOnly_1803_, uint8_t v_skipConstInApp_1804_, uint8_t v_skipInstances_1805_, lean_object* v_postApp_1806_, lean_object* v___x_1807_, lean_object* v___y_1808_, lean_object* v_b_1809_, lean_object* v_a_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1801_, v_post_1802_, v_usedLetOnly_1803_, v_skipConstInApp_1804_, v_skipInstances_1805_, v_postApp_1806_, v___x_1807_, v___y_1808_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1826_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1826_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1821_ = lean_array_fset(v_b_1809_, v_a_1810_, v_a_1817_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1822_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec_ref(v_b_1809_);
v_a_1827_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1816_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1816_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__0___boxed(lean_object* v_pre_1835_, lean_object* v_post_1836_, lean_object* v_usedLetOnly_1837_, lean_object* v_skipConstInApp_1838_, lean_object* v_skipInstances_1839_, lean_object* v_postApp_1840_, lean_object* v___x_1841_, lean_object* v___y_1842_, lean_object* v_b_1843_, lean_object* v_a_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
uint8_t v_usedLetOnly_boxed_1850_; uint8_t v_skipConstInApp_boxed_1851_; uint8_t v_skipInstances_boxed_1852_; lean_object* v_res_1853_; 
v_usedLetOnly_boxed_1850_ = lean_unbox(v_usedLetOnly_1837_);
v_skipConstInApp_boxed_1851_ = lean_unbox(v_skipConstInApp_1838_);
v_skipInstances_boxed_1852_ = lean_unbox(v_skipInstances_1839_);
v_res_1853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__0(v_pre_1835_, v_post_1836_, v_usedLetOnly_boxed_1850_, v_skipConstInApp_boxed_1851_, v_skipInstances_boxed_1852_, v_postApp_1840_, v___x_1841_, v___y_1842_, v_b_1843_, v_a_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v_a_1844_);
lean_dec(v___y_1842_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_upperBound_1854_, lean_object* v___x_1855_, lean_object* v_pre_1856_, lean_object* v_post_1857_, uint8_t v_usedLetOnly_1858_, uint8_t v_skipConstInApp_1859_, uint8_t v_skipInstances_1860_, lean_object* v_postApp_1861_, lean_object* v_a_1862_, lean_object* v_b_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v___y_1871_; uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_lt(v_a_1862_, v_upperBound_1854_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
lean_dec(v_a_1862_);
lean_dec_ref(v_postApp_1861_);
lean_dec_ref(v_post_1857_);
lean_dec_ref(v_pre_1856_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v_b_1863_);
return v___x_1895_;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1896_ = lean_array_fget_borrowed(v_b_1863_, v_a_1862_);
v___x_1897_ = lean_array_get_size(v___x_1855_);
v___x_1898_ = lean_nat_dec_lt(v_a_1862_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___f_1902_; 
lean_inc(v___x_1896_);
v___x_1899_ = lean_box(v_usedLetOnly_1858_);
v___x_1900_ = lean_box(v_skipConstInApp_1859_);
v___x_1901_ = lean_box(v_skipInstances_1860_);
lean_inc(v_a_1862_);
lean_inc(v___y_1864_);
lean_inc_ref(v_postApp_1861_);
lean_inc_ref(v_post_1857_);
lean_inc_ref(v_pre_1856_);
v___f_1902_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1902_, 0, v_pre_1856_);
lean_closure_set(v___f_1902_, 1, v_post_1857_);
lean_closure_set(v___f_1902_, 2, v___x_1899_);
lean_closure_set(v___f_1902_, 3, v___x_1900_);
lean_closure_set(v___f_1902_, 4, v___x_1901_);
lean_closure_set(v___f_1902_, 5, v_postApp_1861_);
lean_closure_set(v___f_1902_, 6, v___x_1896_);
lean_closure_set(v___f_1902_, 7, v___y_1864_);
lean_closure_set(v___f_1902_, 8, v_b_1863_);
lean_closure_set(v___f_1902_, 9, v_a_1862_);
v___y_1871_ = v___f_1902_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1903_; uint8_t v_isInstance_1904_; 
v___x_1903_ = lean_array_fget_borrowed(v___x_1855_, v_a_1862_);
v_isInstance_1904_ = lean_ctor_get_uint8(v___x_1903_, sizeof(void*)*1 + 4);
if (v_isInstance_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___f_1908_; 
lean_inc(v___x_1896_);
v___x_1905_ = lean_box(v_usedLetOnly_1858_);
v___x_1906_ = lean_box(v_skipConstInApp_1859_);
v___x_1907_ = lean_box(v_skipInstances_1860_);
lean_inc(v_a_1862_);
lean_inc(v___y_1864_);
lean_inc_ref(v_postApp_1861_);
lean_inc_ref(v_post_1857_);
lean_inc_ref(v_pre_1856_);
v___f_1908_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_1908_, 0, v_pre_1856_);
lean_closure_set(v___f_1908_, 1, v_post_1857_);
lean_closure_set(v___f_1908_, 2, v___x_1905_);
lean_closure_set(v___f_1908_, 3, v___x_1906_);
lean_closure_set(v___f_1908_, 4, v___x_1907_);
lean_closure_set(v___f_1908_, 5, v_postApp_1861_);
lean_closure_set(v___f_1908_, 6, v___x_1896_);
lean_closure_set(v___f_1908_, 7, v___y_1864_);
lean_closure_set(v___f_1908_, 8, v_b_1863_);
lean_closure_set(v___f_1908_, 9, v_a_1862_);
v___y_1871_ = v___f_1908_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1909_; lean_object* v___f_1910_; 
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_b_1863_);
v___f_1910_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1910_, 0, v___x_1909_);
v___y_1871_ = v___f_1910_;
goto v___jp_1870_;
}
}
}
v___jp_1870_:
{
lean_object* v___x_1872_; 
lean_inc(v___y_1868_);
lean_inc_ref(v___y_1867_);
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
v___x_1872_ = lean_apply_5(v___y_1871_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, lean_box(0));
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1885_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1885_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1885_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
if (lean_obj_tag(v_a_1873_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; 
lean_dec(v_a_1862_);
lean_dec_ref(v_postApp_1861_);
lean_dec_ref(v_post_1857_);
lean_dec_ref(v_pre_1856_);
v_a_1877_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v_a_1873_, 1);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v_a_1877_);
v___x_1879_ = v___x_1875_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_del_object(v___x_1875_);
v_a_1881_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v_a_1873_, 1);
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = lean_nat_add(v_a_1862_, v___x_1882_);
lean_dec(v_a_1862_);
v_a_1862_ = v___x_1883_;
v_b_1863_ = v_a_1881_;
goto _start;
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1862_);
lean_dec_ref(v_postApp_1861_);
lean_dec_ref(v_post_1857_);
lean_dec_ref(v_pre_1856_);
v_a_1886_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1872_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1872_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1911_, lean_object* v_pre_1912_, lean_object* v_post_1913_, uint8_t v_usedLetOnly_1914_, uint8_t v_skipConstInApp_1915_, lean_object* v_postApp_1916_, lean_object* v___y_1917_, lean_object* v_x_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_f_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; 
if (lean_obj_tag(v_x_1918_) == 5)
{
lean_object* v_fn_1980_; lean_object* v_arg_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_fn_1980_ = lean_ctor_get(v_x_1918_, 0);
lean_inc_ref(v_fn_1980_);
v_arg_1981_ = lean_ctor_get(v_x_1918_, 1);
lean_inc_ref(v_arg_1981_);
lean_dec_ref_known(v_x_1918_, 2);
v___x_1982_ = lean_array_set(v_x_1919_, v_x_1920_, v_arg_1981_);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_sub(v_x_1920_, v___x_1983_);
lean_dec(v_x_1920_);
v_x_1918_ = v_fn_1980_;
v_x_1919_ = v___x_1982_;
v_x_1920_ = v___x_1984_;
goto _start;
}
else
{
lean_dec(v_x_1920_);
if (v_skipConstInApp_1915_ == 0)
{
goto v___jp_1977_;
}
else
{
uint8_t v___x_1986_; 
v___x_1986_ = l_Lean_Expr_isConst(v_x_1918_);
if (v___x_1986_ == 0)
{
goto v___jp_1977_;
}
else
{
v_f_1928_ = v_x_1918_;
v___y_1929_ = v___y_1921_;
v___y_1930_ = v___y_1922_;
v___y_1931_ = v___y_1923_;
v___y_1932_ = v___y_1924_;
v___y_1933_ = v___y_1925_;
goto v___jp_1927_;
}
}
}
v___jp_1927_:
{
if (v_skipInstances_1911_ == 0)
{
size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v_sz_1934_ = lean_array_size(v_x_1919_);
v___x_1935_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_1916_);
lean_inc_ref(v_post_1913_);
lean_inc_ref(v_pre_1912_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1912_, v_post_1913_, v_usedLetOnly_1914_, v_skipConstInApp_1915_, v_skipInstances_1911_, v_postApp_1916_, v_sz_1934_, v___x_1935_, v_x_1919_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = l_Lean_mkAppN(v_f_1928_, v_a_1937_);
lean_dec(v_a_1937_);
lean_inc_ref(v_postApp_1916_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1932_);
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
v___x_1939_ = lean_apply_7(v_postApp_1916_, v___y_1917_, v___x_1938_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, lean_box(0));
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1941_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1912_, v_post_1913_, v_usedLetOnly_1914_, v_skipConstInApp_1915_, v_skipInstances_1911_, v_postApp_1916_, v_a_1940_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
return v___x_1941_;
}
else
{
lean_dec_ref(v_postApp_1916_);
lean_dec_ref(v_post_1913_);
lean_dec_ref(v_pre_1912_);
return v___x_1939_;
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_f_1928_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_postApp_1916_);
lean_dec_ref(v_post_1913_);
lean_dec_ref(v_pre_1912_);
v_a_1942_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1936_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1936_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = lean_array_get_size(v_x_1919_);
lean_inc_ref(v_f_1928_);
v___x_1951_ = l_Lean_Meta_getFunInfoNArgs(v_f_1928_, v___x_1950_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v_paramInfo_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v_paramInfo_1953_ = lean_ctor_get(v_a_1952_, 0);
lean_inc_ref(v_paramInfo_1953_);
lean_dec(v_a_1952_);
v___x_1954_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_1916_);
lean_inc_ref(v_post_1913_);
lean_inc_ref(v_pre_1912_);
v___x_1955_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v___x_1950_, v_paramInfo_1953_, v_pre_1912_, v_post_1913_, v_usedLetOnly_1914_, v_skipConstInApp_1915_, v_skipInstances_1911_, v_postApp_1916_, v___x_1954_, v_x_1919_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec_ref(v_paramInfo_1953_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l_Lean_mkAppN(v_f_1928_, v_a_1956_);
lean_dec(v_a_1956_);
lean_inc_ref(v_postApp_1916_);
lean_inc(v___y_1933_);
lean_inc_ref(v___y_1932_);
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
v___x_1958_ = lean_apply_7(v_postApp_1916_, v___y_1917_, v___x_1957_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, lean_box(0));
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1960_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1912_, v_post_1913_, v_usedLetOnly_1914_, v_skipConstInApp_1915_, v_skipInstances_1911_, v_postApp_1916_, v_a_1959_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
return v___x_1960_;
}
else
{
lean_dec_ref(v_postApp_1916_);
lean_dec_ref(v_post_1913_);
lean_dec_ref(v_pre_1912_);
return v___x_1958_;
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_f_1928_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_postApp_1916_);
lean_dec_ref(v_post_1913_);
lean_dec_ref(v_pre_1912_);
v_a_1961_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1955_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1955_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v_f_1928_);
lean_dec_ref(v_x_1919_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_postApp_1916_);
lean_dec_ref(v_post_1913_);
lean_dec_ref(v_pre_1912_);
v_a_1969_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1951_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1951_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
v___jp_1977_:
{
lean_object* v___x_1978_; 
lean_inc_ref(v_postApp_1916_);
lean_inc_ref(v_post_1913_);
lean_inc_ref(v_pre_1912_);
v___x_1978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1912_, v_post_1913_, v_usedLetOnly_1914_, v_skipConstInApp_1915_, v_skipInstances_1911_, v_postApp_1916_, v_x_1918_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v_f_1928_ = v_a_1979_;
v___y_1929_ = v___y_1921_;
v___y_1930_ = v___y_1922_;
v___y_1931_ = v___y_1923_;
v___y_1932_ = v___y_1924_;
v___y_1933_ = v___y_1925_;
goto v___jp_1927_;
}
else
{
lean_dec_ref(v_x_1919_);
lean_dec_ref(v___y_1917_);
lean_dec_ref(v_postApp_1916_);
lean_dec_ref(v_post_1913_);
lean_dec_ref(v_pre_1912_);
return v___x_1978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1987_, lean_object* v_pre_1988_, lean_object* v_e_1989_, lean_object* v_post_1990_, uint8_t v_usedLetOnly_1991_, uint8_t v_skipConstInApp_1992_, uint8_t v_skipInstances_1993_, lean_object* v_postApp_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Core_checkSystem(v___x_1987_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2002_; 
lean_dec_ref_known(v___x_2001_, 1);
lean_inc_ref(v_pre_1988_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
lean_inc_ref(v_e_1989_);
v___x_2002_ = lean_apply_6(v_pre_1988_, v_e_1989_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, lean_box(0));
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2051_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2051_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2051_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___y_2008_; 
switch(lean_obj_tag(v_a_2003_))
{
case 0:
{
lean_object* v_e_2043_; lean_object* v___x_2045_; 
lean_dec_ref(v_postApp_1994_);
lean_dec_ref(v_post_1990_);
lean_dec_ref(v_e_1989_);
lean_dec_ref(v_pre_1988_);
v_e_2043_ = lean_ctor_get(v_a_2003_, 0);
lean_inc_ref(v_e_2043_);
lean_dec_ref_known(v_a_2003_, 1);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v_e_2043_);
v___x_2045_ = v___x_2005_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_e_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
case 1:
{
lean_object* v_e_2047_; lean_object* v___x_2048_; 
lean_del_object(v___x_2005_);
lean_dec_ref(v_e_1989_);
v_e_2047_ = lean_ctor_get(v_a_2003_, 0);
lean_inc_ref(v_e_2047_);
lean_dec_ref_known(v_a_2003_, 1);
v___x_2048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v_e_2047_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2048_;
}
default: 
{
lean_object* v_e_x3f_2049_; 
lean_del_object(v___x_2005_);
v_e_x3f_2049_ = lean_ctor_get(v_a_2003_, 0);
lean_inc(v_e_x3f_2049_);
lean_dec_ref_known(v_a_2003_, 1);
if (lean_obj_tag(v_e_x3f_2049_) == 0)
{
v___y_2008_ = v_e_1989_;
goto v___jp_2007_;
}
else
{
lean_object* v_val_2050_; 
lean_dec_ref(v_e_1989_);
v_val_2050_ = lean_ctor_get(v_e_x3f_2049_, 0);
lean_inc(v_val_2050_);
lean_dec_ref_known(v_e_x3f_2049_, 1);
v___y_2008_ = v_val_2050_;
goto v___jp_2007_;
}
}
}
v___jp_2007_:
{
switch(lean_obj_tag(v___y_2008_))
{
case 7:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2010_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v___x_2009_, v___y_2008_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2010_;
}
case 6:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2012_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v___x_2011_, v___y_2008_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2012_;
}
case 8:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_2014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v___x_2013_, v___y_2008_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2014_;
}
case 5:
{
lean_object* v_dummy_2015_; lean_object* v_nargs_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_dummy_2015_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2016_ = l_Lean_Expr_getAppNumArgs(v___y_2008_);
lean_inc(v_nargs_2016_);
v___x_2017_ = lean_mk_array(v_nargs_2016_, v_dummy_2015_);
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_sub(v_nargs_2016_, v___x_2018_);
lean_dec(v_nargs_2016_);
lean_inc_ref(v___y_2008_);
v___x_2020_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1993_, v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_postApp_1994_, v___y_2008_, v___y_2008_, v___x_2017_, v___x_2019_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2020_;
}
case 10:
{
lean_object* v_data_2021_; lean_object* v_expr_2022_; lean_object* v___x_2023_; 
v_data_2021_ = lean_ctor_get(v___y_2008_, 0);
v_expr_2022_ = lean_ctor_get(v___y_2008_, 1);
lean_inc_ref(v_expr_2022_);
lean_inc_ref(v_postApp_1994_);
lean_inc_ref(v_post_1990_);
lean_inc_ref(v_pre_1988_);
v___x_2023_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v_expr_2022_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; size_t v___x_2025_; size_t v___x_2026_; uint8_t v___x_2027_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = lean_ptr_addr(v_expr_2022_);
v___x_2026_ = lean_ptr_addr(v_a_2024_);
v___x_2027_ = lean_usize_dec_eq(v___x_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_inc(v_data_2021_);
lean_dec_ref_known(v___y_2008_, 2);
v___x_2028_ = l_Lean_Expr_mdata___override(v_data_2021_, v_a_2024_);
v___x_2029_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v___x_2028_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; 
lean_dec(v_a_2024_);
v___x_2030_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v___y_2008_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2030_;
}
}
else
{
lean_dec_ref_known(v___y_2008_, 2);
lean_dec_ref(v_postApp_1994_);
lean_dec_ref(v_post_1990_);
lean_dec_ref(v_pre_1988_);
return v___x_2023_;
}
}
case 11:
{
lean_object* v_typeName_2031_; lean_object* v_idx_2032_; lean_object* v_struct_2033_; lean_object* v___x_2034_; 
v_typeName_2031_ = lean_ctor_get(v___y_2008_, 0);
v_idx_2032_ = lean_ctor_get(v___y_2008_, 1);
v_struct_2033_ = lean_ctor_get(v___y_2008_, 2);
lean_inc_ref(v_struct_2033_);
lean_inc_ref(v_postApp_1994_);
lean_inc_ref(v_post_1990_);
lean_inc_ref(v_pre_1988_);
v___x_2034_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v_struct_2033_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; size_t v___x_2036_; size_t v___x_2037_; uint8_t v___x_2038_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = lean_ptr_addr(v_struct_2033_);
v___x_2037_ = lean_ptr_addr(v_a_2035_);
v___x_2038_ = lean_usize_dec_eq(v___x_2036_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_inc(v_idx_2032_);
lean_inc(v_typeName_2031_);
lean_dec_ref_known(v___y_2008_, 3);
v___x_2039_ = l_Lean_Expr_proj___override(v_typeName_2031_, v_idx_2032_, v_a_2035_);
v___x_2040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v___x_2039_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; 
lean_dec(v_a_2035_);
v___x_2041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v___y_2008_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2041_;
}
}
else
{
lean_dec_ref_known(v___y_2008_, 3);
lean_dec_ref(v_postApp_1994_);
lean_dec_ref(v_post_1990_);
lean_dec_ref(v_pre_1988_);
return v___x_2034_;
}
}
default: 
{
lean_object* v___x_2042_; 
v___x_2042_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_1988_, v_post_1990_, v_usedLetOnly_1991_, v_skipConstInApp_1992_, v_skipInstances_1993_, v_postApp_1994_, v___y_2008_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2042_;
}
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_postApp_1994_);
lean_dec_ref(v_post_1990_);
lean_dec_ref(v_e_1989_);
lean_dec_ref(v_pre_1988_);
v_a_2052_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2002_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2002_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref(v_postApp_1994_);
lean_dec_ref(v_post_1990_);
lean_dec_ref(v_e_1989_);
lean_dec_ref(v_pre_1988_);
v_a_2060_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2001_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2001_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2068_, lean_object* v_pre_2069_, lean_object* v_e_2070_, lean_object* v_post_2071_, lean_object* v_usedLetOnly_2072_, lean_object* v_skipConstInApp_2073_, lean_object* v_skipInstances_2074_, lean_object* v_postApp_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v_usedLetOnly_boxed_2082_; uint8_t v_skipConstInApp_boxed_2083_; uint8_t v_skipInstances_boxed_2084_; lean_object* v_res_2085_; 
v_usedLetOnly_boxed_2082_ = lean_unbox(v_usedLetOnly_2072_);
v_skipConstInApp_boxed_2083_ = lean_unbox(v_skipConstInApp_2073_);
v_skipInstances_boxed_2084_ = lean_unbox(v_skipInstances_2074_);
v_res_2085_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2068_, v_pre_2069_, v_e_2070_, v_post_2071_, v_usedLetOnly_boxed_2082_, v_skipConstInApp_boxed_2083_, v_skipInstances_boxed_2084_, v_postApp_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2086_, lean_object* v_post_2087_, uint8_t v_usedLetOnly_2088_, uint8_t v_skipConstInApp_2089_, uint8_t v_skipInstances_2090_, lean_object* v_postApp_2091_, lean_object* v_e_2092_, lean_object* v_a_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_inc(v_a_2093_);
v___x_2099_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2099_, 0, lean_box(0));
lean_closure_set(v___x_2099_, 1, lean_box(0));
lean_closure_set(v___x_2099_, 2, v_a_2093_);
v___x_2100_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2099_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2135_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2135_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2135_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___redArg(v_a_2101_, v_e_2092_);
lean_dec(v_a_2101_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___f_2110_; lean_object* v___x_2111_; 
lean_del_object(v___x_2103_);
v___x_2106_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2107_ = lean_box(v_usedLetOnly_2088_);
v___x_2108_ = lean_box(v_skipConstInApp_2089_);
v___x_2109_ = lean_box(v_skipInstances_2090_);
lean_inc_ref(v_e_2092_);
v___f_2110_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 14, 8);
lean_closure_set(v___f_2110_, 0, v___x_2106_);
lean_closure_set(v___f_2110_, 1, v_pre_2086_);
lean_closure_set(v___f_2110_, 2, v_e_2092_);
lean_closure_set(v___f_2110_, 3, v_post_2087_);
lean_closure_set(v___f_2110_, 4, v___x_2107_);
lean_closure_set(v___f_2110_, 5, v___x_2108_);
lean_closure_set(v___f_2110_, 6, v___x_2109_);
lean_closure_set(v___f_2110_, 7, v_postApp_2091_);
v___x_2111_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2110_, v_a_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___f_2113_; lean_object* v___x_2114_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_n(v_a_2112_, 2);
lean_dec_ref_known(v___x_2111_, 1);
lean_inc(v_a_2093_);
v___f_2113_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2113_, 0, v_a_2093_);
lean_closure_set(v___f_2113_, 1, v_e_2092_);
lean_closure_set(v___f_2113_, 2, v_a_2112_);
v___x_2114_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2113_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v___x_2114_, 0);
lean_dec(v_unused_2122_);
v___x_2116_ = v___x_2114_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_dec(v___x_2114_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v_a_2112_);
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2112_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_a_2112_);
v_a_2123_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2114_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2114_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_dec_ref(v_e_2092_);
return v___x_2111_;
}
}
else
{
lean_object* v_val_2131_; lean_object* v___x_2133_; 
lean_dec_ref(v_e_2092_);
lean_dec_ref(v_postApp_2091_);
lean_dec_ref(v_post_2087_);
lean_dec_ref(v_pre_2086_);
v_val_2131_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_val_2131_);
lean_dec_ref_known(v___x_2105_, 1);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v_val_2131_);
v___x_2133_ = v___x_2103_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_val_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_e_2092_);
lean_dec_ref(v_postApp_2091_);
lean_dec_ref(v_post_2087_);
lean_dec_ref(v_pre_2086_);
v_a_2136_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2100_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2100_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2144_, lean_object* v_post_2145_, uint8_t v_usedLetOnly_2146_, uint8_t v_skipConstInApp_2147_, uint8_t v_skipInstances_2148_, lean_object* v_postApp_2149_, lean_object* v_fvars_2150_, lean_object* v_e_2151_, lean_object* v_a_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
if (lean_obj_tag(v_e_2151_) == 7)
{
lean_object* v_binderName_2158_; lean_object* v_binderType_2159_; lean_object* v_body_2160_; uint8_t v_binderInfo_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_binderName_2158_ = lean_ctor_get(v_e_2151_, 0);
lean_inc(v_binderName_2158_);
v_binderType_2159_ = lean_ctor_get(v_e_2151_, 1);
lean_inc_ref(v_binderType_2159_);
v_body_2160_ = lean_ctor_get(v_e_2151_, 2);
lean_inc_ref(v_body_2160_);
v_binderInfo_2161_ = lean_ctor_get_uint8(v_e_2151_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2151_, 3);
v___x_2162_ = lean_box(v_usedLetOnly_2146_);
v___x_2163_ = lean_box(v_skipConstInApp_2147_);
v___x_2164_ = lean_box(v_skipInstances_2148_);
lean_inc_ref(v_postApp_2149_);
lean_inc_ref(v_post_2145_);
lean_inc_ref(v_pre_2144_);
lean_inc_ref(v_fvars_2150_);
v___f_2165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2165_, 0, v_fvars_2150_);
lean_closure_set(v___f_2165_, 1, v_pre_2144_);
lean_closure_set(v___f_2165_, 2, v_post_2145_);
lean_closure_set(v___f_2165_, 3, v___x_2162_);
lean_closure_set(v___f_2165_, 4, v___x_2163_);
lean_closure_set(v___f_2165_, 5, v___x_2164_);
lean_closure_set(v___f_2165_, 6, v_postApp_2149_);
lean_closure_set(v___f_2165_, 7, v_body_2160_);
v___x_2166_ = lean_expr_instantiate_rev(v_binderType_2159_, v_fvars_2150_);
lean_dec_ref(v_fvars_2150_);
lean_dec_ref(v_binderType_2159_);
v___x_2167_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2144_, v_post_2145_, v_usedLetOnly_2146_, v_skipConstInApp_2147_, v_skipInstances_2148_, v_postApp_2149_, v___x_2166_, v_a_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = 0;
v___x_2170_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2158_, v_binderInfo_2161_, v_a_2168_, v___f_2165_, v___x_2169_, v_a_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
return v___x_2170_;
}
else
{
lean_dec_ref(v___f_2165_);
lean_dec(v_binderName_2158_);
return v___x_2167_;
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_expr_instantiate_rev(v_e_2151_, v_fvars_2150_);
lean_dec_ref(v_e_2151_);
lean_inc_ref(v_postApp_2149_);
lean_inc_ref(v_post_2145_);
lean_inc_ref(v_pre_2144_);
v___x_2172_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2144_, v_post_2145_, v_usedLetOnly_2146_, v_skipConstInApp_2147_, v_skipInstances_2148_, v_postApp_2149_, v___x_2171_, v_a_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; uint8_t v___x_2174_; uint8_t v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = 0;
v___x_2175_ = 1;
v___x_2176_ = 1;
v___x_2177_ = l_Lean_Meta_mkForallFVars(v_fvars_2150_, v_a_2173_, v___x_2174_, v_usedLetOnly_2146_, v___x_2175_, v___x_2176_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec_ref(v_fvars_2150_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_2144_, v_post_2145_, v_usedLetOnly_2146_, v_skipConstInApp_2147_, v_skipInstances_2148_, v_postApp_2149_, v_a_2178_, v_a_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
return v___x_2179_;
}
else
{
lean_dec_ref(v_postApp_2149_);
lean_dec_ref(v_post_2145_);
lean_dec_ref(v_pre_2144_);
return v___x_2177_;
}
}
else
{
lean_dec_ref(v_fvars_2150_);
lean_dec_ref(v_postApp_2149_);
lean_dec_ref(v_post_2145_);
lean_dec_ref(v_pre_2144_);
return v___x_2172_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2180_, lean_object* v_pre_2181_, lean_object* v_post_2182_, uint8_t v_usedLetOnly_2183_, uint8_t v_skipConstInApp_2184_, uint8_t v_skipInstances_2185_, lean_object* v_postApp_2186_, lean_object* v_body_2187_, lean_object* v_x_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = lean_array_push(v_fvars_2180_, v_x_2188_);
v___x_2196_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2181_, v_post_2182_, v_usedLetOnly_2183_, v_skipConstInApp_2184_, v_skipInstances_2185_, v_postApp_2186_, v___x_2195_, v_body_2187_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object* v_pre_2197_, lean_object* v_post_2198_, lean_object* v_usedLetOnly_2199_, lean_object* v_skipConstInApp_2200_, lean_object* v_skipInstances_2201_, lean_object* v_postApp_2202_, lean_object* v_e_2203_, lean_object* v_a_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
uint8_t v_usedLetOnly_boxed_2210_; uint8_t v_skipConstInApp_boxed_2211_; uint8_t v_skipInstances_boxed_2212_; lean_object* v_res_2213_; 
v_usedLetOnly_boxed_2210_ = lean_unbox(v_usedLetOnly_2199_);
v_skipConstInApp_boxed_2211_ = lean_unbox(v_skipConstInApp_2200_);
v_skipInstances_boxed_2212_ = lean_unbox(v_skipInstances_2201_);
v_res_2213_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_pre_2197_, v_post_2198_, v_usedLetOnly_boxed_2210_, v_skipConstInApp_boxed_2211_, v_skipInstances_boxed_2212_, v_postApp_2202_, v_e_2203_, v_a_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v_a_2204_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2214_, lean_object* v_post_2215_, lean_object* v_usedLetOnly_2216_, lean_object* v_skipConstInApp_2217_, lean_object* v_skipInstances_2218_, lean_object* v_postApp_2219_, lean_object* v_sz_2220_, lean_object* v_i_2221_, lean_object* v_bs_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
uint8_t v_usedLetOnly_boxed_2229_; uint8_t v_skipConstInApp_boxed_2230_; uint8_t v_skipInstances_boxed_2231_; size_t v_sz_boxed_2232_; size_t v_i_boxed_2233_; lean_object* v_res_2234_; 
v_usedLetOnly_boxed_2229_ = lean_unbox(v_usedLetOnly_2216_);
v_skipConstInApp_boxed_2230_ = lean_unbox(v_skipConstInApp_2217_);
v_skipInstances_boxed_2231_ = lean_unbox(v_skipInstances_2218_);
v_sz_boxed_2232_ = lean_unbox_usize(v_sz_2220_);
lean_dec(v_sz_2220_);
v_i_boxed_2233_ = lean_unbox_usize(v_i_2221_);
lean_dec(v_i_2221_);
v_res_2234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2214_, v_post_2215_, v_usedLetOnly_boxed_2229_, v_skipConstInApp_boxed_2230_, v_skipInstances_boxed_2231_, v_postApp_2219_, v_sz_boxed_2232_, v_i_boxed_2233_, v_bs_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2235_, lean_object* v_post_2236_, lean_object* v_usedLetOnly_2237_, lean_object* v_skipConstInApp_2238_, lean_object* v_skipInstances_2239_, lean_object* v_postApp_2240_, lean_object* v_e_2241_, lean_object* v_a_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v_usedLetOnly_boxed_2248_; uint8_t v_skipConstInApp_boxed_2249_; uint8_t v_skipInstances_boxed_2250_; lean_object* v_res_2251_; 
v_usedLetOnly_boxed_2248_ = lean_unbox(v_usedLetOnly_2237_);
v_skipConstInApp_boxed_2249_ = lean_unbox(v_skipConstInApp_2238_);
v_skipInstances_boxed_2250_ = lean_unbox(v_skipInstances_2239_);
v_res_2251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2235_, v_post_2236_, v_usedLetOnly_boxed_2248_, v_skipConstInApp_boxed_2249_, v_skipInstances_boxed_2250_, v_postApp_2240_, v_e_2241_, v_a_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v_a_2242_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2252_, lean_object* v_post_2253_, lean_object* v_usedLetOnly_2254_, lean_object* v_skipConstInApp_2255_, lean_object* v_skipInstances_2256_, lean_object* v_postApp_2257_, lean_object* v_fvars_2258_, lean_object* v_e_2259_, lean_object* v_a_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
uint8_t v_usedLetOnly_boxed_2266_; uint8_t v_skipConstInApp_boxed_2267_; uint8_t v_skipInstances_boxed_2268_; lean_object* v_res_2269_; 
v_usedLetOnly_boxed_2266_ = lean_unbox(v_usedLetOnly_2254_);
v_skipConstInApp_boxed_2267_ = lean_unbox(v_skipConstInApp_2255_);
v_skipInstances_boxed_2268_ = lean_unbox(v_skipInstances_2256_);
v_res_2269_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2252_, v_post_2253_, v_usedLetOnly_boxed_2266_, v_skipConstInApp_boxed_2267_, v_skipInstances_boxed_2268_, v_postApp_2257_, v_fvars_2258_, v_e_2259_, v_a_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v_a_2260_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2270_, lean_object* v_post_2271_, lean_object* v_usedLetOnly_2272_, lean_object* v_skipConstInApp_2273_, lean_object* v_skipInstances_2274_, lean_object* v_postApp_2275_, lean_object* v_fvars_2276_, lean_object* v_e_2277_, lean_object* v_a_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v_usedLetOnly_boxed_2284_; uint8_t v_skipConstInApp_boxed_2285_; uint8_t v_skipInstances_boxed_2286_; lean_object* v_res_2287_; 
v_usedLetOnly_boxed_2284_ = lean_unbox(v_usedLetOnly_2272_);
v_skipConstInApp_boxed_2285_ = lean_unbox(v_skipConstInApp_2273_);
v_skipInstances_boxed_2286_ = lean_unbox(v_skipInstances_2274_);
v_res_2287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2270_, v_post_2271_, v_usedLetOnly_boxed_2284_, v_skipConstInApp_boxed_2285_, v_skipInstances_boxed_2286_, v_postApp_2275_, v_fvars_2276_, v_e_2277_, v_a_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v_a_2278_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2288_, lean_object* v_post_2289_, lean_object* v_usedLetOnly_2290_, lean_object* v_skipConstInApp_2291_, lean_object* v_skipInstances_2292_, lean_object* v_postApp_2293_, lean_object* v_fvars_2294_, lean_object* v_e_2295_, lean_object* v_a_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v_usedLetOnly_boxed_2302_; uint8_t v_skipConstInApp_boxed_2303_; uint8_t v_skipInstances_boxed_2304_; lean_object* v_res_2305_; 
v_usedLetOnly_boxed_2302_ = lean_unbox(v_usedLetOnly_2290_);
v_skipConstInApp_boxed_2303_ = lean_unbox(v_skipConstInApp_2291_);
v_skipInstances_boxed_2304_ = lean_unbox(v_skipInstances_2292_);
v_res_2305_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2288_, v_post_2289_, v_usedLetOnly_boxed_2302_, v_skipConstInApp_boxed_2303_, v_skipInstances_boxed_2304_, v_postApp_2293_, v_fvars_2294_, v_e_2295_, v_a_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v_a_2296_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_upperBound_2306_, lean_object* v___x_2307_, lean_object* v_pre_2308_, lean_object* v_post_2309_, lean_object* v_usedLetOnly_2310_, lean_object* v_skipConstInApp_2311_, lean_object* v_skipInstances_2312_, lean_object* v_postApp_2313_, lean_object* v_a_2314_, lean_object* v_b_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
uint8_t v_usedLetOnly_boxed_2322_; uint8_t v_skipConstInApp_boxed_2323_; uint8_t v_skipInstances_boxed_2324_; lean_object* v_res_2325_; 
v_usedLetOnly_boxed_2322_ = lean_unbox(v_usedLetOnly_2310_);
v_skipConstInApp_boxed_2323_ = lean_unbox(v_skipConstInApp_2311_);
v_skipInstances_boxed_2324_ = lean_unbox(v_skipInstances_2312_);
v_res_2325_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_upperBound_2306_, v___x_2307_, v_pre_2308_, v_post_2309_, v_usedLetOnly_boxed_2322_, v_skipConstInApp_boxed_2323_, v_skipInstances_boxed_2324_, v_postApp_2313_, v_a_2314_, v_b_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___x_2307_);
lean_dec(v_upperBound_2306_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2326_, lean_object* v_pre_2327_, lean_object* v_post_2328_, lean_object* v_usedLetOnly_2329_, lean_object* v_skipConstInApp_2330_, lean_object* v_postApp_2331_, lean_object* v___y_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
uint8_t v_skipInstances_boxed_2342_; uint8_t v_usedLetOnly_boxed_2343_; uint8_t v_skipConstInApp_boxed_2344_; lean_object* v_res_2345_; 
v_skipInstances_boxed_2342_ = lean_unbox(v_skipInstances_2326_);
v_usedLetOnly_boxed_2343_ = lean_unbox(v_usedLetOnly_2329_);
v_skipConstInApp_boxed_2344_ = lean_unbox(v_skipConstInApp_2330_);
v_res_2345_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2342_, v_pre_2327_, v_post_2328_, v_usedLetOnly_boxed_2343_, v_skipConstInApp_boxed_2344_, v_postApp_2331_, v___y_2332_, v_x_2333_, v_x_2334_, v_x_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
return v_res_2345_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2348_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2348_, 0, lean_box(0));
lean_closure_set(v___x_2348_, 1, lean_box(0));
lean_closure_set(v___x_2348_, 2, v___x_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2349_, lean_object* v_pre_2350_, lean_object* v_post_2351_, uint8_t v_usedLetOnly_2352_, uint8_t v_skipConstInApp_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___f_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_a_2363_; lean_object* v___x_2364_; 
v___f_2359_ = ((lean_object*)(l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0));
v___x_2360_ = 0;
v___x_2361_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__1);
v___x_2362_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2361_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2350_, v_post_2351_, v_usedLetOnly_2352_, v_skipConstInApp_2353_, v___x_2360_, v___f_2359_, v_input_2349_, v_a_2363_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2366_, 0, lean_box(0));
lean_closure_set(v___x_2366_, 1, lean_box(0));
lean_closure_set(v___x_2366_, 2, v_a_2363_);
v___x_2367_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2366_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v___x_2367_, 0);
lean_dec(v_unused_2375_);
v___x_2369_ = v___x_2367_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_dec(v___x_2367_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v_a_2365_);
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2365_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
else
{
lean_dec(v_a_2363_);
return v___x_2364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2376_, lean_object* v_pre_2377_, lean_object* v_post_2378_, lean_object* v_usedLetOnly_2379_, lean_object* v_skipConstInApp_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v_usedLetOnly_boxed_2386_; uint8_t v_skipConstInApp_boxed_2387_; lean_object* v_res_2388_; 
v_usedLetOnly_boxed_2386_ = lean_unbox(v_usedLetOnly_2379_);
v_skipConstInApp_boxed_2387_ = lean_unbox(v_skipConstInApp_2380_);
v_res_2388_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2376_, v_pre_2377_, v_post_2378_, v_usedLetOnly_boxed_2386_, v_skipConstInApp_boxed_2387_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2389_, lean_object* v_as_2390_, lean_object* v_j_2391_){
_start:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = lean_array_get_size(v_as_2390_);
v___x_2393_ = lean_nat_dec_lt(v_j_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; 
lean_dec(v_j_2391_);
v___x_2394_ = lean_box(0);
return v___x_2394_;
}
else
{
lean_object* v___x_2395_; lean_object* v_declName_2396_; uint8_t v___x_2397_; 
v___x_2395_ = lean_array_fget_borrowed(v_as_2390_, v_j_2391_);
v_declName_2396_ = lean_ctor_get(v___x_2395_, 3);
v___x_2397_ = lean_name_eq(v_declName_2396_, v___x_2389_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_nat_add(v_j_2391_, v___x_2398_);
lean_dec(v_j_2391_);
v_j_2391_ = v___x_2399_;
goto _start;
}
else
{
lean_object* v___x_2401_; 
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v_j_2391_);
return v___x_2401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2402_, lean_object* v_as_2403_, lean_object* v_j_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2402_, v_as_2403_, v_j_2404_);
lean_dec_ref(v_as_2403_);
lean_dec(v___x_2402_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_st_ref_get(v_val_2406_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2421_, lean_object* v_val_2422_, lean_object* v_a_2423_, lean_object* v___x_2424_, lean_object* v_____r_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2436_, lean_object* v_val_2437_, lean_object* v_a_2438_, lean_object* v___x_2439_, lean_object* v_____r_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2436_, v_val_2437_, v_a_2438_, v___x_2439_, v_____r_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v_val_2437_);
lean_dec(v_val_2436_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2447_, lean_object* v_val_2448_, lean_object* v_next_2449_, lean_object* v_next_2450_, lean_object* v___x_2451_, lean_object* v___x_2452_, lean_object* v_upperBound_2453_, lean_object* v_params_2454_, lean_object* v___x_2455_, lean_object* v_a_2456_, uint8_t v_b_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
uint8_t v_a_2464_; uint8_t v___x_2468_; 
v___x_2468_ = lean_nat_dec_lt(v_a_2456_, v_upperBound_2453_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec(v_a_2456_);
lean_dec_ref(v___x_2455_);
lean_dec(v_next_2449_);
v___x_2469_ = lean_box(v_b_2457_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
else
{
uint8_t v___x_2471_; lean_object* v___y_2473_; lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2471_ = lean_nat_dec_eq(v___x_2451_, v___x_2452_);
v___x_2487_ = lean_st_ref_get(v_val_2447_);
v___x_2488_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2450_, v_a_2456_, v___x_2487_);
lean_dec(v___x_2487_);
if (v___x_2488_ == 0)
{
v_a_2464_ = v_b_2457_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2489_; uint8_t v_foApprox_2490_; uint8_t v_ctxApprox_2491_; uint8_t v_quasiPatternApprox_2492_; uint8_t v_constApprox_2493_; uint8_t v_isDefEqStuckEx_2494_; uint8_t v_unificationHints_2495_; uint8_t v_assignSyntheticOpaque_2496_; uint8_t v_offsetCnstrs_2497_; uint8_t v_transparency_2498_; uint8_t v_etaStruct_2499_; uint8_t v_univApprox_2500_; uint8_t v_iota_2501_; uint8_t v_beta_2502_; uint8_t v_proj_2503_; uint8_t v_zeta_2504_; uint8_t v_zetaDelta_2505_; uint8_t v_zetaUnused_2506_; uint8_t v_zetaHave_2507_; uint8_t v_canUnfoldPredicateConfig_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2538_; 
v___x_2489_ = l_Lean_Meta_Context_config(v___y_2458_);
v_foApprox_2490_ = lean_ctor_get_uint8(v___x_2489_, 0);
v_ctxApprox_2491_ = lean_ctor_get_uint8(v___x_2489_, 1);
v_quasiPatternApprox_2492_ = lean_ctor_get_uint8(v___x_2489_, 2);
v_constApprox_2493_ = lean_ctor_get_uint8(v___x_2489_, 3);
v_isDefEqStuckEx_2494_ = lean_ctor_get_uint8(v___x_2489_, 4);
v_unificationHints_2495_ = lean_ctor_get_uint8(v___x_2489_, 5);
v_assignSyntheticOpaque_2496_ = lean_ctor_get_uint8(v___x_2489_, 7);
v_offsetCnstrs_2497_ = lean_ctor_get_uint8(v___x_2489_, 8);
v_transparency_2498_ = lean_ctor_get_uint8(v___x_2489_, 9);
v_etaStruct_2499_ = lean_ctor_get_uint8(v___x_2489_, 10);
v_univApprox_2500_ = lean_ctor_get_uint8(v___x_2489_, 11);
v_iota_2501_ = lean_ctor_get_uint8(v___x_2489_, 12);
v_beta_2502_ = lean_ctor_get_uint8(v___x_2489_, 13);
v_proj_2503_ = lean_ctor_get_uint8(v___x_2489_, 14);
v_zeta_2504_ = lean_ctor_get_uint8(v___x_2489_, 15);
v_zetaDelta_2505_ = lean_ctor_get_uint8(v___x_2489_, 16);
v_zetaUnused_2506_ = lean_ctor_get_uint8(v___x_2489_, 17);
v_zetaHave_2507_ = lean_ctor_get_uint8(v___x_2489_, 18);
v_canUnfoldPredicateConfig_2508_ = lean_ctor_get_uint8(v___x_2489_, 19);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2510_ = v___x_2489_;
v_isShared_2511_ = v_isSharedCheck_2538_;
goto v_resetjp_2509_;
}
else
{
lean_dec(v___x_2489_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2538_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
uint8_t v_trackZetaDelta_2512_; lean_object* v_zetaDeltaSet_2513_; lean_object* v_lctx_2514_; lean_object* v_localInstances_2515_; lean_object* v_defEqCtx_x3f_2516_; lean_object* v_synthPendingDepth_2517_; lean_object* v_customCanUnfoldPredicate_x3f_2518_; uint8_t v_univApprox_2519_; uint8_t v_inTypeClassResolution_2520_; uint8_t v_cacheInferType_2521_; uint8_t v___x_2522_; lean_object* v___x_2524_; 
v_trackZetaDelta_2512_ = lean_ctor_get_uint8(v___y_2458_, sizeof(void*)*7);
v_zetaDeltaSet_2513_ = lean_ctor_get(v___y_2458_, 1);
v_lctx_2514_ = lean_ctor_get(v___y_2458_, 2);
v_localInstances_2515_ = lean_ctor_get(v___y_2458_, 3);
v_defEqCtx_x3f_2516_ = lean_ctor_get(v___y_2458_, 4);
v_synthPendingDepth_2517_ = lean_ctor_get(v___y_2458_, 5);
v_customCanUnfoldPredicate_x3f_2518_ = lean_ctor_get(v___y_2458_, 6);
v_univApprox_2519_ = lean_ctor_get_uint8(v___y_2458_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2520_ = lean_ctor_get_uint8(v___y_2458_, sizeof(void*)*7 + 2);
v_cacheInferType_2521_ = lean_ctor_get_uint8(v___y_2458_, sizeof(void*)*7 + 3);
v___x_2522_ = 0;
if (v_isShared_2511_ == 0)
{
v___x_2524_ = v___x_2510_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 0, v_foApprox_2490_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 1, v_ctxApprox_2491_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 2, v_quasiPatternApprox_2492_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 3, v_constApprox_2493_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 4, v_isDefEqStuckEx_2494_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 5, v_unificationHints_2495_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 7, v_assignSyntheticOpaque_2496_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 8, v_offsetCnstrs_2497_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 9, v_transparency_2498_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 10, v_etaStruct_2499_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 11, v_univApprox_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 12, v_iota_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 13, v_beta_2502_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 14, v_proj_2503_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 15, v_zeta_2504_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 16, v_zetaDelta_2505_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 17, v_zetaUnused_2506_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 18, v_zetaHave_2507_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, 19, v_canUnfoldPredicateConfig_2508_);
v___x_2524_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
uint64_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v_transparency_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; uint8_t v___x_2532_; 
lean_ctor_set_uint8(v___x_2524_, 6, v___x_2522_);
v___x_2525_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2524_);
v___x_2526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set_uint64(v___x_2526_, sizeof(void*)*1, v___x_2525_);
lean_inc(v_customCanUnfoldPredicate_x3f_2518_);
lean_inc(v_synthPendingDepth_2517_);
lean_inc(v_defEqCtx_x3f_2516_);
lean_inc_ref(v_localInstances_2515_);
lean_inc_ref(v_lctx_2514_);
lean_inc(v_zetaDeltaSet_2513_);
lean_inc_ref(v___x_2526_);
v___x_2527_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v_zetaDeltaSet_2513_);
lean_ctor_set(v___x_2527_, 2, v_lctx_2514_);
lean_ctor_set(v___x_2527_, 3, v_localInstances_2515_);
lean_ctor_set(v___x_2527_, 4, v_defEqCtx_x3f_2516_);
lean_ctor_set(v___x_2527_, 5, v_synthPendingDepth_2517_);
lean_ctor_set(v___x_2527_, 6, v_customCanUnfoldPredicate_x3f_2518_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*7, v_trackZetaDelta_2512_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*7 + 1, v_univApprox_2519_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2520_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*7 + 3, v_cacheInferType_2521_);
v___x_2528_ = l_Lean_Meta_Context_config(v___x_2527_);
v_transparency_2529_ = lean_ctor_get_uint8(v___x_2528_, 9);
lean_dec_ref(v___x_2528_);
v___x_2530_ = lean_array_fget_borrowed(v_params_2454_, v_a_2456_);
v___x_2531_ = 2;
v___x_2532_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2529_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec_ref_known(v___x_2527_, 7);
v___x_2533_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2531_, v___x_2526_);
lean_inc(v_customCanUnfoldPredicate_x3f_2518_);
lean_inc(v_synthPendingDepth_2517_);
lean_inc(v_defEqCtx_x3f_2516_);
lean_inc_ref(v_localInstances_2515_);
lean_inc_ref(v_lctx_2514_);
lean_inc(v_zetaDeltaSet_2513_);
v___x_2534_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v_zetaDeltaSet_2513_);
lean_ctor_set(v___x_2534_, 2, v_lctx_2514_);
lean_ctor_set(v___x_2534_, 3, v_localInstances_2515_);
lean_ctor_set(v___x_2534_, 4, v_defEqCtx_x3f_2516_);
lean_ctor_set(v___x_2534_, 5, v_synthPendingDepth_2517_);
lean_ctor_set(v___x_2534_, 6, v_customCanUnfoldPredicate_x3f_2518_);
lean_ctor_set_uint8(v___x_2534_, sizeof(void*)*7, v_trackZetaDelta_2512_);
lean_ctor_set_uint8(v___x_2534_, sizeof(void*)*7 + 1, v_univApprox_2519_);
lean_ctor_set_uint8(v___x_2534_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2520_);
lean_ctor_set_uint8(v___x_2534_, sizeof(void*)*7 + 3, v_cacheInferType_2521_);
lean_inc_ref(v___x_2455_);
lean_inc(v___x_2530_);
v___x_2535_ = l_Lean_Meta_isExprDefEq(v___x_2530_, v___x_2455_, v___x_2534_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec_ref_known(v___x_2534_, 7);
v___y_2473_ = v___x_2535_;
goto v___jp_2472_;
}
else
{
lean_object* v___x_2536_; 
lean_dec_ref_known(v___x_2526_, 1);
lean_inc_ref(v___x_2455_);
lean_inc(v___x_2530_);
v___x_2536_ = l_Lean_Meta_isExprDefEq(v___x_2530_, v___x_2455_, v___x_2527_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec_ref_known(v___x_2527_, 7);
v___y_2473_ = v___x_2536_;
goto v___jp_2472_;
}
}
}
}
v___jp_2472_:
{
if (lean_obj_tag(v___y_2473_) == 0)
{
lean_object* v_a_2474_; uint8_t v___x_2475_; 
v_a_2474_ = lean_ctor_get(v___y_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___y_2473_, 1);
v___x_2475_ = lean_unbox(v_a_2474_);
lean_dec(v_a_2474_);
if (v___x_2475_ == 0)
{
v_a_2464_ = v_b_2457_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_st_ref_take(v_val_2447_);
lean_inc(v_a_2456_);
lean_inc(v_next_2449_);
v___x_2477_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2448_, v_next_2449_, v_next_2450_, v_a_2456_, v___x_2476_);
v___x_2478_ = lean_st_ref_put(v_val_2447_, v___x_2477_);
v_a_2464_ = v___x_2471_;
goto v___jp_2463_;
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_a_2456_);
lean_dec_ref(v___x_2455_);
lean_dec(v_next_2449_);
v_a_2479_ = lean_ctor_get(v___y_2473_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___y_2473_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___y_2473_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___y_2473_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
v___jp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2466_ = lean_nat_add(v_a_2456_, v___x_2465_);
lean_dec(v_a_2456_);
v_a_2456_ = v___x_2466_;
v_b_2457_ = v_a_2464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2539_, lean_object* v_val_2540_, lean_object* v_next_2541_, lean_object* v_next_2542_, lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v_upperBound_2545_, lean_object* v_params_2546_, lean_object* v___x_2547_, lean_object* v_a_2548_, lean_object* v_b_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
uint8_t v_b_boxed_2555_; lean_object* v_res_2556_; 
v_b_boxed_2555_ = lean_unbox(v_b_2549_);
v_res_2556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2539_, v_val_2540_, v_next_2541_, v_next_2542_, v___x_2543_, v___x_2544_, v_upperBound_2545_, v_params_2546_, v___x_2547_, v_a_2548_, v_b_boxed_2555_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v_params_2546_);
lean_dec(v_upperBound_2545_);
lean_dec(v___x_2544_);
lean_dec(v___x_2543_);
lean_dec(v_next_2542_);
lean_dec(v_val_2540_);
lean_dec(v_val_2539_);
return v_res_2556_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2567_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2568_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2569_ = l_Lean_Name_append(v___x_2568_, v___x_2567_);
return v___x_2569_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2572_ = l_Lean_stringToMessageData(v___x_2571_);
return v___x_2572_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2574_ = l_Lean_stringToMessageData(v___x_2573_);
return v___x_2574_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
return v___x_2577_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2580_ = l_Lean_stringToMessageData(v___x_2579_);
return v___x_2580_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2583_ = l_Lean_stringToMessageData(v___x_2582_);
return v___x_2583_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2586_ = l_Lean_stringToMessageData(v___x_2585_);
return v___x_2586_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2589_ = l_Lean_stringToMessageData(v___x_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2590_, lean_object* v_val_2591_, lean_object* v_upperBound_2592_, lean_object* v_args_2593_, lean_object* v_e_2594_, lean_object* v_next_2595_, lean_object* v_params_2596_, lean_object* v___x_2597_, lean_object* v___x_2598_, lean_object* v_a_2599_, lean_object* v_b_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_a_2607_; lean_object* v___y_2612_; uint8_t v___x_2631_; 
v___x_2631_ = lean_nat_dec_lt(v_a_2599_, v_upperBound_2592_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_b_2600_);
return v___x_2632_;
}
else
{
lean_object* v___x_2633_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2633_ = lean_box(0);
v___x_2640_ = l_Lean_instInhabitedExpr;
v___x_2641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2590_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; uint8_t v___x_2643_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2643_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2591_, v_a_2599_, v_a_2642_);
lean_dec(v_a_2642_);
if (v___x_2643_ == 0)
{
v_a_2607_ = v___x_2633_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = lean_array_get_size(v_args_2593_);
v___x_2645_ = lean_nat_dec_lt(v_a_2599_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v_toCold_2646_; lean_object* v_options_2647_; uint8_t v_hasTrace_2648_; 
v_toCold_2646_ = lean_ctor_get(v___y_2603_, 0);
v_options_2647_ = lean_ctor_get(v_toCold_2646_, 2);
v_hasTrace_2648_ = lean_ctor_get_uint8(v_options_2647_, sizeof(void*)*1);
if (v_hasTrace_2648_ == 0)
{
goto v___jp_2636_;
}
else
{
lean_object* v_inheritedTraceOptions_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_inheritedTraceOptions_2649_ = lean_ctor_get(v_toCold_2646_, 11);
v___x_2650_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2651_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2652_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2649_, v_options_2647_, v___x_2651_);
if (v___x_2652_ == 0)
{
goto v___jp_2636_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2653_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2591_);
v___x_2654_ = l_Nat_reprFast(v_val_2591_);
v___x_2655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
v___x_2656_ = l_Lean_MessageData_ofFormat(v___x_2655_);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2653_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
lean_inc(v_a_2599_);
v___x_2660_ = l_Nat_reprFast(v_a_2599_);
v___x_2661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
v___x_2662_ = l_Lean_MessageData_ofFormat(v___x_2661_);
lean_inc_ref(v___x_2662_);
v___x_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2659_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2663_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
lean_inc_ref(v_e_2594_);
v___x_2666_ = l_Lean_MessageData_ofExpr(v_e_2594_);
v___x_2667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v___x_2668_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___x_2662_);
v___x_2671_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2650_, v___x_2670_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
lean_inc(v_a_2599_);
v___x_2673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2590_, v_val_2591_, v_a_2599_, v___x_2633_, v_a_2672_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
v___y_2612_ = v___x_2673_;
goto v___jp_2611_;
}
else
{
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
return v___x_2671_;
}
}
}
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_array_fget_borrowed(v_args_2593_, v_a_2599_);
v___x_2675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2590_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2591_, v_a_2599_, v_next_2595_, v_a_2676_);
lean_dec(v_a_2676_);
if (lean_obj_tag(v___x_2677_) == 1)
{
lean_object* v_val_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2779_; 
v_val_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2779_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_val_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2779_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; uint8_t v_foApprox_2683_; uint8_t v_ctxApprox_2684_; uint8_t v_quasiPatternApprox_2685_; uint8_t v_constApprox_2686_; uint8_t v_isDefEqStuckEx_2687_; uint8_t v_unificationHints_2688_; uint8_t v_assignSyntheticOpaque_2689_; uint8_t v_offsetCnstrs_2690_; uint8_t v_transparency_2691_; uint8_t v_etaStruct_2692_; uint8_t v_univApprox_2693_; uint8_t v_iota_2694_; uint8_t v_beta_2695_; uint8_t v_proj_2696_; uint8_t v_zeta_2697_; uint8_t v_zetaDelta_2698_; uint8_t v_zetaUnused_2699_; uint8_t v_zetaHave_2700_; uint8_t v_canUnfoldPredicateConfig_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2778_; 
v___x_2682_ = l_Lean_Meta_Context_config(v___y_2601_);
v_foApprox_2683_ = lean_ctor_get_uint8(v___x_2682_, 0);
v_ctxApprox_2684_ = lean_ctor_get_uint8(v___x_2682_, 1);
v_quasiPatternApprox_2685_ = lean_ctor_get_uint8(v___x_2682_, 2);
v_constApprox_2686_ = lean_ctor_get_uint8(v___x_2682_, 3);
v_isDefEqStuckEx_2687_ = lean_ctor_get_uint8(v___x_2682_, 4);
v_unificationHints_2688_ = lean_ctor_get_uint8(v___x_2682_, 5);
v_assignSyntheticOpaque_2689_ = lean_ctor_get_uint8(v___x_2682_, 7);
v_offsetCnstrs_2690_ = lean_ctor_get_uint8(v___x_2682_, 8);
v_transparency_2691_ = lean_ctor_get_uint8(v___x_2682_, 9);
v_etaStruct_2692_ = lean_ctor_get_uint8(v___x_2682_, 10);
v_univApprox_2693_ = lean_ctor_get_uint8(v___x_2682_, 11);
v_iota_2694_ = lean_ctor_get_uint8(v___x_2682_, 12);
v_beta_2695_ = lean_ctor_get_uint8(v___x_2682_, 13);
v_proj_2696_ = lean_ctor_get_uint8(v___x_2682_, 14);
v_zeta_2697_ = lean_ctor_get_uint8(v___x_2682_, 15);
v_zetaDelta_2698_ = lean_ctor_get_uint8(v___x_2682_, 16);
v_zetaUnused_2699_ = lean_ctor_get_uint8(v___x_2682_, 17);
v_zetaHave_2700_ = lean_ctor_get_uint8(v___x_2682_, 18);
v_canUnfoldPredicateConfig_2701_ = lean_ctor_get_uint8(v___x_2682_, 19);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2703_ = v___x_2682_;
v_isShared_2704_ = v_isSharedCheck_2778_;
goto v_resetjp_2702_;
}
else
{
lean_dec(v___x_2682_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2778_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
uint8_t v_trackZetaDelta_2705_; lean_object* v_zetaDeltaSet_2706_; lean_object* v_lctx_2707_; lean_object* v_localInstances_2708_; lean_object* v_defEqCtx_x3f_2709_; lean_object* v_synthPendingDepth_2710_; lean_object* v_customCanUnfoldPredicate_x3f_2711_; uint8_t v_univApprox_2712_; uint8_t v_inTypeClassResolution_2713_; uint8_t v_cacheInferType_2714_; uint8_t v___x_2715_; lean_object* v___x_2717_; 
v_trackZetaDelta_2705_ = lean_ctor_get_uint8(v___y_2601_, sizeof(void*)*7);
v_zetaDeltaSet_2706_ = lean_ctor_get(v___y_2601_, 1);
v_lctx_2707_ = lean_ctor_get(v___y_2601_, 2);
v_localInstances_2708_ = lean_ctor_get(v___y_2601_, 3);
v_defEqCtx_x3f_2709_ = lean_ctor_get(v___y_2601_, 4);
v_synthPendingDepth_2710_ = lean_ctor_get(v___y_2601_, 5);
v_customCanUnfoldPredicate_x3f_2711_ = lean_ctor_get(v___y_2601_, 6);
v_univApprox_2712_ = lean_ctor_get_uint8(v___y_2601_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2713_ = lean_ctor_get_uint8(v___y_2601_, sizeof(void*)*7 + 2);
v_cacheInferType_2714_ = lean_ctor_get_uint8(v___y_2601_, sizeof(void*)*7 + 3);
v___x_2715_ = 0;
if (v_isShared_2704_ == 0)
{
v___x_2717_ = v___x_2703_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 0, v_foApprox_2683_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 1, v_ctxApprox_2684_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 2, v_quasiPatternApprox_2685_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 3, v_constApprox_2686_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 4, v_isDefEqStuckEx_2687_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 5, v_unificationHints_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 7, v_assignSyntheticOpaque_2689_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 8, v_offsetCnstrs_2690_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 9, v_transparency_2691_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 10, v_etaStruct_2692_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 11, v_univApprox_2693_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 12, v_iota_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 13, v_beta_2695_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 14, v_proj_2696_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 15, v_zeta_2697_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 16, v_zetaDelta_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 17, v_zetaUnused_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 18, v_zetaHave_2700_);
lean_ctor_set_uint8(v_reuseFailAlloc_2777_, 19, v_canUnfoldPredicateConfig_2701_);
v___x_2717_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
uint64_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v_transparency_2722_; lean_object* v___x_2723_; lean_object* v___y_2725_; uint8_t v___x_2771_; uint8_t v___x_2772_; 
lean_ctor_set_uint8(v___x_2717_, 6, v___x_2715_);
v___x_2718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2717_);
v___x_2719_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set_uint64(v___x_2719_, sizeof(void*)*1, v___x_2718_);
lean_inc(v_customCanUnfoldPredicate_x3f_2711_);
lean_inc(v_synthPendingDepth_2710_);
lean_inc(v_defEqCtx_x3f_2709_);
lean_inc_ref(v_localInstances_2708_);
lean_inc_ref(v_lctx_2707_);
lean_inc(v_zetaDeltaSet_2706_);
lean_inc_ref(v___x_2719_);
v___x_2720_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v_zetaDeltaSet_2706_);
lean_ctor_set(v___x_2720_, 2, v_lctx_2707_);
lean_ctor_set(v___x_2720_, 3, v_localInstances_2708_);
lean_ctor_set(v___x_2720_, 4, v_defEqCtx_x3f_2709_);
lean_ctor_set(v___x_2720_, 5, v_synthPendingDepth_2710_);
lean_ctor_set(v___x_2720_, 6, v_customCanUnfoldPredicate_x3f_2711_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7, v_trackZetaDelta_2705_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 1, v_univApprox_2712_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2713_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 3, v_cacheInferType_2714_);
v___x_2721_ = l_Lean_Meta_Context_config(v___x_2720_);
v_transparency_2722_ = lean_ctor_get_uint8(v___x_2721_, 9);
lean_dec_ref(v___x_2721_);
v___x_2723_ = lean_array_get_borrowed(v___x_2640_, v_params_2596_, v_val_2678_);
lean_dec(v_val_2678_);
v___x_2771_ = 2;
v___x_2772_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2722_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec_ref_known(v___x_2720_, 7);
v___x_2773_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2771_, v___x_2719_);
lean_inc(v_customCanUnfoldPredicate_x3f_2711_);
lean_inc(v_synthPendingDepth_2710_);
lean_inc(v_defEqCtx_x3f_2709_);
lean_inc_ref(v_localInstances_2708_);
lean_inc_ref(v_lctx_2707_);
lean_inc(v_zetaDeltaSet_2706_);
v___x_2774_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v_zetaDeltaSet_2706_);
lean_ctor_set(v___x_2774_, 2, v_lctx_2707_);
lean_ctor_set(v___x_2774_, 3, v_localInstances_2708_);
lean_ctor_set(v___x_2774_, 4, v_defEqCtx_x3f_2709_);
lean_ctor_set(v___x_2774_, 5, v_synthPendingDepth_2710_);
lean_ctor_set(v___x_2774_, 6, v_customCanUnfoldPredicate_x3f_2711_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7, v_trackZetaDelta_2705_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7 + 1, v_univApprox_2712_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2713_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*7 + 3, v_cacheInferType_2714_);
lean_inc(v___x_2674_);
lean_inc(v___x_2723_);
v___x_2775_ = l_Lean_Meta_isExprDefEq(v___x_2723_, v___x_2674_, v___x_2774_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec_ref_known(v___x_2774_, 7);
v___y_2725_ = v___x_2775_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2776_; 
lean_dec_ref_known(v___x_2719_, 1);
lean_inc(v___x_2674_);
lean_inc(v___x_2723_);
v___x_2776_ = l_Lean_Meta_isExprDefEq(v___x_2723_, v___x_2674_, v___x_2720_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec_ref_known(v___x_2720_, 7);
v___y_2725_ = v___x_2776_;
goto v___jp_2724_;
}
v___jp_2724_:
{
if (lean_obj_tag(v___y_2725_) == 0)
{
lean_object* v_a_2726_; uint8_t v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___y_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___y_2725_, 1);
v___x_2727_ = lean_unbox(v_a_2726_);
lean_dec(v_a_2726_);
if (v___x_2727_ == 0)
{
lean_object* v_toCold_2728_; lean_object* v_options_2729_; uint8_t v_hasTrace_2730_; 
v_toCold_2728_ = lean_ctor_get(v___y_2603_, 0);
v_options_2729_ = lean_ctor_get(v_toCold_2728_, 2);
v_hasTrace_2730_ = lean_ctor_get_uint8(v_options_2729_, sizeof(void*)*1);
if (v_hasTrace_2730_ == 0)
{
lean_del_object(v___x_2680_);
goto v___jp_2638_;
}
else
{
lean_object* v_inheritedTraceOptions_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v_inheritedTraceOptions_2731_ = lean_ctor_get(v_toCold_2728_, 11);
v___x_2732_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2733_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2734_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2731_, v_options_2729_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_del_object(v___x_2680_);
goto v___jp_2638_;
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2735_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2591_);
v___x_2736_ = l_Nat_reprFast(v_val_2591_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 3);
lean_ctor_set(v___x_2680_, 0, v___x_2736_);
v___x_2738_ = v___x_2680_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2739_ = l_Lean_MessageData_ofFormat(v___x_2738_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2735_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
lean_inc(v_a_2599_);
v___x_2743_ = l_Nat_reprFast(v_a_2599_);
v___x_2744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
v___x_2745_ = l_Lean_MessageData_ofFormat(v___x_2744_);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2742_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
lean_inc_ref(v_e_2594_);
v___x_2749_ = l_Lean_MessageData_ofExpr(v_e_2594_);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2748_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
lean_inc(v___x_2723_);
v___x_2753_ = l_Lean_MessageData_ofExpr(v___x_2723_);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
lean_inc(v___x_2674_);
v___x_2757_ = l_Lean_MessageData_ofExpr(v___x_2674_);
v___x_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2732_, v___x_2758_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
lean_inc(v_a_2599_);
v___x_2761_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2590_, v_val_2591_, v_a_2599_, v___x_2633_, v_a_2760_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
v___y_2612_ = v___x_2761_;
goto v___jp_2611_;
}
else
{
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
return v___x_2759_;
}
}
}
}
}
else
{
lean_del_object(v___x_2680_);
v_a_2607_ = v___x_2633_;
goto v___jp_2606_;
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_del_object(v___x_2680_);
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
v_a_2763_ = lean_ctor_get(v___y_2725_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___y_2725_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___y_2725_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___y_2725_);
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
}
}
}
else
{
lean_object* v___x_2780_; uint8_t v___x_2781_; lean_object* v___x_2782_; 
lean_dec(v___x_2677_);
v___x_2780_ = lean_unsigned_to_nat(0u);
v___x_2781_ = 0;
lean_inc(v___x_2674_);
lean_inc(v_a_2599_);
v___x_2782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2590_, v_val_2591_, v_a_2599_, v_next_2595_, v___x_2597_, v___x_2598_, v___x_2597_, v_params_2596_, v___x_2674_, v___x_2780_, v___x_2781_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; uint8_t v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = lean_unbox(v_a_2783_);
lean_dec(v_a_2783_);
if (v___x_2784_ == 0)
{
lean_object* v_toCold_2785_; lean_object* v_options_2786_; uint8_t v_hasTrace_2787_; 
v_toCold_2785_ = lean_ctor_get(v___y_2603_, 0);
v_options_2786_ = lean_ctor_get(v_toCold_2785_, 2);
v_hasTrace_2787_ = lean_ctor_get_uint8(v_options_2786_, sizeof(void*)*1);
if (v_hasTrace_2787_ == 0)
{
goto v___jp_2634_;
}
else
{
lean_object* v_inheritedTraceOptions_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_inheritedTraceOptions_2788_ = lean_ctor_get(v_toCold_2785_, 11);
v___x_2789_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2790_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2791_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2788_, v_options_2786_, v___x_2790_);
if (v___x_2791_ == 0)
{
goto v___jp_2634_;
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2792_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2591_);
v___x_2793_ = l_Nat_reprFast(v_val_2591_);
v___x_2794_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
v___x_2795_ = l_Lean_MessageData_ofFormat(v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2792_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2796_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
lean_inc(v_a_2599_);
v___x_2799_ = l_Nat_reprFast(v_a_2599_);
v___x_2800_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
v___x_2801_ = l_Lean_MessageData_ofFormat(v___x_2800_);
v___x_2802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2798_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
lean_inc_ref(v_e_2594_);
v___x_2805_ = l_Lean_MessageData_ofExpr(v_e_2594_);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
lean_inc(v___x_2674_);
v___x_2809_ = l_Lean_MessageData_ofExpr(v___x_2674_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2789_, v___x_2812_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
lean_inc(v_a_2599_);
v___x_2815_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2590_, v_val_2591_, v_a_2599_, v___x_2633_, v_a_2814_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
v___y_2612_ = v___x_2815_;
goto v___jp_2611_;
}
else
{
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
return v___x_2813_;
}
}
}
}
else
{
v_a_2607_ = v___x_2633_;
goto v___jp_2606_;
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
v_a_2816_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2782_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2782_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
v_a_2824_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2675_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2675_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
v_a_2832_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2641_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2641_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
v___jp_2634_:
{
lean_object* v___x_2635_; 
lean_inc(v_a_2599_);
v___x_2635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2590_, v_val_2591_, v_a_2599_, v___x_2633_, v___x_2633_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
v___y_2612_ = v___x_2635_;
goto v___jp_2611_;
}
v___jp_2636_:
{
lean_object* v___x_2637_; 
lean_inc(v_a_2599_);
v___x_2637_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2590_, v_val_2591_, v_a_2599_, v___x_2633_, v___x_2633_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
v___y_2612_ = v___x_2637_;
goto v___jp_2611_;
}
v___jp_2638_:
{
lean_object* v___x_2639_; 
lean_inc(v_a_2599_);
v___x_2639_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2590_, v_val_2591_, v_a_2599_, v___x_2633_, v___x_2633_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
v___y_2612_ = v___x_2639_;
goto v___jp_2611_;
}
}
v___jp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_unsigned_to_nat(1u);
v___x_2609_ = lean_nat_add(v_a_2599_, v___x_2608_);
lean_dec(v_a_2599_);
v_a_2599_ = v___x_2609_;
v_b_2600_ = v_a_2607_;
goto _start;
}
v___jp_2611_:
{
if (lean_obj_tag(v___y_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2622_; 
v_a_2613_ = lean_ctor_get(v___y_2612_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___y_2612_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2615_ = v___y_2612_;
v_isShared_2616_ = v_isSharedCheck_2622_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___y_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2622_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
if (lean_obj_tag(v_a_2613_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; 
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
v_a_2617_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v_a_2613_, 1);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v_a_2617_);
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
else
{
lean_object* v_a_2621_; 
lean_del_object(v___x_2615_);
v_a_2621_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v_a_2613_, 1);
v_a_2607_ = v_a_2621_;
goto v___jp_2606_;
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2594_);
lean_dec(v_val_2591_);
v_a_2623_ = lean_ctor_get(v___y_2612_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___y_2612_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___y_2612_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___y_2612_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2840_, lean_object* v_val_2841_, lean_object* v_upperBound_2842_, lean_object* v_args_2843_, lean_object* v_e_2844_, lean_object* v_next_2845_, lean_object* v_params_2846_, lean_object* v___x_2847_, lean_object* v___x_2848_, lean_object* v_a_2849_, lean_object* v_b_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2840_, v_val_2841_, v_upperBound_2842_, v_args_2843_, v_e_2844_, v_next_2845_, v_params_2846_, v___x_2847_, v___x_2848_, v_a_2849_, v_b_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___x_2848_);
lean_dec(v___x_2847_);
lean_dec_ref(v_params_2846_);
lean_dec(v_next_2845_);
lean_dec_ref(v_args_2843_);
lean_dec(v_upperBound_2842_);
lean_dec(v_val_2840_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2859_, lean_object* v___x_2860_, lean_object* v_val_2861_, lean_object* v_e_2862_, lean_object* v_next_2863_, lean_object* v_params_2864_, lean_object* v___x_2865_, lean_object* v___x_2866_, lean_object* v_x_2867_, lean_object* v_x_2868_, lean_object* v_x_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
if (lean_obj_tag(v_x_2867_) == 5)
{
lean_object* v_fn_2875_; lean_object* v_arg_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_fn_2875_ = lean_ctor_get(v_x_2867_, 0);
lean_inc_ref(v_fn_2875_);
v_arg_2876_ = lean_ctor_get(v_x_2867_, 1);
lean_inc_ref(v_arg_2876_);
lean_dec_ref_known(v_x_2867_, 2);
v___x_2877_ = lean_array_set(v_x_2868_, v_x_2869_, v_arg_2876_);
v___x_2878_ = lean_unsigned_to_nat(1u);
v___x_2879_ = lean_nat_sub(v_x_2869_, v___x_2878_);
lean_dec(v_x_2869_);
v_x_2867_ = v_fn_2875_;
v_x_2868_ = v___x_2877_;
v_x_2869_ = v___x_2879_;
goto _start;
}
else
{
uint8_t v___x_2881_; 
lean_dec(v_x_2869_);
v___x_2881_ = l_Lean_Expr_isConst(v_x_2867_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec_ref(v_x_2868_);
lean_dec_ref(v_x_2867_);
lean_dec_ref(v_e_2862_);
v___x_2882_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
return v___x_2883_;
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = l_Lean_Expr_constName_x21(v_x_2867_);
lean_dec_ref(v_x_2867_);
v___x_2885_ = lean_unsigned_to_nat(0u);
v___x_2886_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2884_, v_preDefs_2859_, v___x_2885_);
lean_dec(v___x_2884_);
if (lean_obj_tag(v___x_2886_) == 1)
{
lean_object* v_val_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_val_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_val_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_array_get_borrowed(v___x_2885_, v___x_2860_, v_val_2887_);
v___x_2890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2861_, v_val_2887_, v___x_2889_, v_x_2868_, v_e_2862_, v_next_2863_, v_params_2864_, v___x_2865_, v___x_2866_, v___x_2885_, v___x_2888_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec_ref(v_x_2868_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2898_; 
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2890_, 0);
lean_dec(v_unused_2899_);
v___x_2892_ = v___x_2890_;
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
else
{
lean_dec(v___x_2890_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2898_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2894_);
v___x_2896_ = v___x_2892_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_a_2900_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2890_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2890_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec(v___x_2886_);
lean_dec_ref(v_x_2868_);
lean_dec_ref(v_e_2862_);
v___x_2908_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
return v___x_2909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2910_, lean_object* v___x_2911_, lean_object* v_val_2912_, lean_object* v_e_2913_, lean_object* v_next_2914_, lean_object* v_params_2915_, lean_object* v___x_2916_, lean_object* v___x_2917_, lean_object* v_x_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2910_, v___x_2911_, v_val_2912_, v_e_2913_, v_next_2914_, v_params_2915_, v___x_2916_, v___x_2917_, v_x_2918_, v_x_2919_, v_x_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___x_2917_);
lean_dec(v___x_2916_);
lean_dec_ref(v_params_2915_);
lean_dec(v_next_2914_);
lean_dec(v_val_2912_);
lean_dec_ref(v___x_2911_);
lean_dec_ref(v_preDefs_2910_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2927_, lean_object* v___x_2928_, lean_object* v_val_2929_, lean_object* v_a_2930_, lean_object* v_params_2931_, lean_object* v___x_2932_, lean_object* v___x_2933_, lean_object* v_e_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_dummy_2940_; lean_object* v_nargs_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_dummy_2940_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2941_ = l_Lean_Expr_getAppNumArgs(v_e_2934_);
lean_inc(v_nargs_2941_);
v___x_2942_ = lean_mk_array(v_nargs_2941_, v_dummy_2940_);
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_2944_ = lean_nat_sub(v_nargs_2941_, v___x_2943_);
lean_dec(v_nargs_2941_);
lean_inc_ref(v_e_2934_);
v___x_2945_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2927_, v___x_2928_, v_val_2929_, v_e_2934_, v_a_2930_, v_params_2931_, v___x_2932_, v___x_2933_, v_e_2934_, v___x_2942_, v___x_2944_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2946_, lean_object* v___x_2947_, lean_object* v_val_2948_, lean_object* v_a_2949_, lean_object* v_params_2950_, lean_object* v___x_2951_, lean_object* v___x_2952_, lean_object* v_e_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2946_, v___x_2947_, v_val_2948_, v_a_2949_, v_params_2950_, v___x_2951_, v___x_2952_, v_e_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___x_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_params_2950_);
lean_dec(v_a_2949_);
lean_dec(v_val_2948_);
lean_dec_ref(v___x_2947_);
lean_dec_ref(v_preDefs_2946_);
return v_res_2959_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2963_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2964_ = lean_unsigned_to_nat(6u);
v___x_2965_ = lean_unsigned_to_nat(201u);
v___x_2966_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2967_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2968_ = l_mkPanicMessageWithDecl(v___x_2967_, v___x_2966_, v___x_2965_, v___x_2964_, v___x_2963_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2969_, lean_object* v___x_2970_, lean_object* v_a_2971_, lean_object* v_preDefs_2972_, lean_object* v_val_2973_, lean_object* v___f_2974_, lean_object* v___x_2975_, lean_object* v_params_2976_, lean_object* v_body_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2983_ = lean_array_get_size(v_params_2976_);
v___x_2984_ = lean_array_get(v___x_2969_, v___x_2970_, v_a_2971_);
v___x_2985_ = lean_nat_dec_eq(v___x_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec(v___x_2984_);
lean_dec_ref(v_body_2977_);
lean_dec_ref(v_params_2976_);
lean_dec_ref(v___f_2974_);
lean_dec(v_val_2973_);
lean_dec_ref(v_preDefs_2972_);
lean_dec(v_a_2971_);
lean_dec_ref(v___x_2970_);
v___x_2986_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2987_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2986_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
return v___x_2987_;
}
else
{
lean_object* v___f_2988_; uint8_t v___x_2989_; lean_object* v___x_2990_; 
v___f_2988_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2988_, 0, v_preDefs_2972_);
lean_closure_set(v___f_2988_, 1, v___x_2970_);
lean_closure_set(v___f_2988_, 2, v_val_2973_);
lean_closure_set(v___f_2988_, 3, v_a_2971_);
lean_closure_set(v___f_2988_, 4, v_params_2976_);
lean_closure_set(v___f_2988_, 5, v___x_2983_);
lean_closure_set(v___f_2988_, 6, v___x_2984_);
v___x_2989_ = 0;
v___x_2990_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2977_, v___f_2988_, v___f_2974_, v___x_2989_, v___x_2985_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v___x_2990_, 0);
lean_dec(v_unused_2998_);
v___x_2992_ = v___x_2990_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_dec(v___x_2990_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2975_);
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2975_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2999_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2990_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2990_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_3007_, lean_object* v___x_3008_, lean_object* v_a_3009_, lean_object* v_preDefs_3010_, lean_object* v_val_3011_, lean_object* v___f_3012_, lean_object* v___x_3013_, lean_object* v_params_3014_, lean_object* v_body_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_3007_, v___x_3008_, v_a_3009_, v_preDefs_3010_, v_val_3011_, v___f_3012_, v___x_3013_, v_params_3014_, v_body_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___x_3007_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v_e_3022_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v___x_3038_, lean_object* v_preDefs_3039_, lean_object* v_val_3040_, lean_object* v_upperBound_3041_, lean_object* v_a_3042_, lean_object* v_b_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_nat_dec_lt(v_a_3042_, v_upperBound_3041_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; 
lean_dec(v_a_3042_);
lean_dec(v_val_3040_);
lean_dec_ref(v_preDefs_3039_);
lean_dec_ref(v___x_3038_);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v_b_3043_);
return v___x_3050_;
}
else
{
lean_object* v___x_3051_; lean_object* v_value_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___f_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; 
v___x_3051_ = lean_array_fget_borrowed(v_preDefs_3039_, v_a_3042_);
v_value_3052_ = lean_ctor_get(v___x_3051_, 7);
v___f_3053_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = lean_box(0);
lean_inc(v_val_3040_);
lean_inc_ref(v_preDefs_3039_);
lean_inc(v_a_3042_);
lean_inc_ref(v___x_3038_);
v___f_3056_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3056_, 0, v___x_3054_);
lean_closure_set(v___f_3056_, 1, v___x_3038_);
lean_closure_set(v___f_3056_, 2, v_a_3042_);
lean_closure_set(v___f_3056_, 3, v_preDefs_3039_);
lean_closure_set(v___f_3056_, 4, v_val_3040_);
lean_closure_set(v___f_3056_, 5, v___f_3053_);
lean_closure_set(v___f_3056_, 6, v___x_3055_);
v___x_3057_ = 0;
lean_inc_ref(v_value_3052_);
v___x_3058_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3052_, v___f_3056_, v___x_3057_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
lean_dec_ref_known(v___x_3058_, 1);
v___x_3059_ = lean_unsigned_to_nat(1u);
v___x_3060_ = lean_nat_add(v_a_3042_, v___x_3059_);
lean_dec(v_a_3042_);
v_a_3042_ = v___x_3060_;
v_b_3043_ = v___x_3055_;
goto _start;
}
else
{
lean_dec(v_a_3042_);
lean_dec(v_val_3040_);
lean_dec_ref(v_preDefs_3039_);
lean_dec_ref(v___x_3038_);
return v___x_3058_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v___x_3062_, lean_object* v_preDefs_3063_, lean_object* v_val_3064_, lean_object* v_upperBound_3065_, lean_object* v_a_3066_, lean_object* v_b_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3062_, v_preDefs_3063_, v_val_3064_, v_upperBound_3065_, v_a_3066_, v_b_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v_upperBound_3065_);
return v_res_3073_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3076_ = l_Lean_stringToMessageData(v___x_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
size_t v_sz_3083_; size_t v___x_3084_; lean_object* v___x_3085_; 
v_sz_3083_ = lean_array_size(v_preDefs_3077_);
v___x_3084_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3077_);
v___x_3085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3083_, v___x_3084_, v_preDefs_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; size_t v_sz_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc_n(v_a_3086_, 2);
lean_dec_ref_known(v___x_3085_, 1);
v_sz_3087_ = lean_array_size(v_a_3086_);
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3087_, v___x_3084_, v_a_3086_);
v___x_3089_ = l_Lean_Elab_FixedParams_Info_init(v_a_3086_);
v___x_3090_ = lean_st_mk_ref(v___x_3089_);
v___x_3091_ = lean_st_ref_take(v___x_3090_);
v___x_3092_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3091_);
v___x_3093_ = lean_st_ref_put(v___x_3090_, v___x_3092_);
v___x_3094_ = lean_array_get_size(v_preDefs_3077_);
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_box(0);
lean_inc(v___x_3090_);
v___x_3097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3088_, v_preDefs_3077_, v___x_3090_, v___x_3094_, v___x_3095_, v___x_3096_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3137_; 
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___x_3097_, 0);
lean_dec(v_unused_3138_);
v___x_3099_ = v___x_3097_;
v_isShared_3100_ = v_isSharedCheck_3137_;
goto v_resetjp_3098_;
}
else
{
lean_dec(v___x_3097_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3137_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v_toCold_3102_; lean_object* v_options_3103_; uint8_t v_hasTrace_3104_; 
v___x_3101_ = lean_st_ref_get(v___x_3090_);
lean_dec(v___x_3090_);
v_toCold_3102_ = lean_ctor_get(v_a_3080_, 0);
v_options_3103_ = lean_ctor_get(v_toCold_3102_, 2);
v_hasTrace_3104_ = lean_ctor_get_uint8(v_options_3103_, sizeof(void*)*1);
if (v_hasTrace_3104_ == 0)
{
lean_object* v___x_3106_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3101_);
v___x_3106_ = v___x_3099_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_inheritedTraceOptions_3108_ = lean_ctor_get(v_toCold_3102_, 11);
v___x_3109_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3110_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3108_, v_options_3103_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3113_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3101_);
v___x_3113_ = v___x_3099_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3101_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_del_object(v___x_3099_);
v___x_3115_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3101_);
v___x_3116_ = l_Lean_Elab_FixedParams_Info_format(v___x_3101_);
v___x_3117_ = l_Std_Format_indentD(v___x_3116_);
v___x_3118_ = l_Lean_MessageData_ofFormat(v___x_3117_);
v___x_3119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3115_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3109_, v___x_3119_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3120_, 0);
lean_dec(v_unused_3128_);
v___x_3122_ = v___x_3120_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_dec(v___x_3120_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3101_);
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3101_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v___x_3101_);
v_a_3129_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3120_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3120_);
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
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec(v___x_3090_);
v_a_3139_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3097_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3097_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v_preDefs_3077_);
v_a_3147_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3085_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3085_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3162_, lean_object* v_val_3163_, lean_object* v_next_3164_, lean_object* v_next_3165_, lean_object* v___x_3166_, lean_object* v___x_3167_, lean_object* v_upperBound_3168_, lean_object* v_params_3169_, lean_object* v___x_3170_, lean_object* v_inst_3171_, lean_object* v_R_3172_, lean_object* v_a_3173_, uint8_t v_b_3174_, lean_object* v_c_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3162_, v_val_3163_, v_next_3164_, v_next_3165_, v___x_3166_, v___x_3167_, v_upperBound_3168_, v_params_3169_, v___x_3170_, v_a_3173_, v_b_3174_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3182_ = _args[0];
lean_object* v_val_3183_ = _args[1];
lean_object* v_next_3184_ = _args[2];
lean_object* v_next_3185_ = _args[3];
lean_object* v___x_3186_ = _args[4];
lean_object* v___x_3187_ = _args[5];
lean_object* v_upperBound_3188_ = _args[6];
lean_object* v_params_3189_ = _args[7];
lean_object* v___x_3190_ = _args[8];
lean_object* v_inst_3191_ = _args[9];
lean_object* v_R_3192_ = _args[10];
lean_object* v_a_3193_ = _args[11];
lean_object* v_b_3194_ = _args[12];
lean_object* v_c_3195_ = _args[13];
lean_object* v___y_3196_ = _args[14];
lean_object* v___y_3197_ = _args[15];
lean_object* v___y_3198_ = _args[16];
lean_object* v___y_3199_ = _args[17];
lean_object* v___y_3200_ = _args[18];
_start:
{
uint8_t v_b_boxed_3201_; lean_object* v_res_3202_; 
v_b_boxed_3201_ = lean_unbox(v_b_3194_);
v_res_3202_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3182_, v_val_3183_, v_next_3184_, v_next_3185_, v___x_3186_, v___x_3187_, v_upperBound_3188_, v_params_3189_, v___x_3190_, v_inst_3191_, v_R_3192_, v_a_3193_, v_b_boxed_3201_, v_c_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec_ref(v_params_3189_);
lean_dec(v_upperBound_3188_);
lean_dec(v___x_3187_);
lean_dec(v___x_3186_);
lean_dec(v_next_3185_);
lean_dec(v_val_3183_);
lean_dec(v_val_3182_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3203_, lean_object* v_val_3204_, lean_object* v_upperBound_3205_, lean_object* v_args_3206_, lean_object* v_e_3207_, lean_object* v_next_3208_, lean_object* v_params_3209_, lean_object* v___x_3210_, lean_object* v___x_3211_, lean_object* v_inst_3212_, lean_object* v_R_3213_, lean_object* v_a_3214_, lean_object* v_b_3215_, lean_object* v_c_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3203_, v_val_3204_, v_upperBound_3205_, v_args_3206_, v_e_3207_, v_next_3208_, v_params_3209_, v___x_3210_, v___x_3211_, v_a_3214_, v_b_3215_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3223_ = _args[0];
lean_object* v_val_3224_ = _args[1];
lean_object* v_upperBound_3225_ = _args[2];
lean_object* v_args_3226_ = _args[3];
lean_object* v_e_3227_ = _args[4];
lean_object* v_next_3228_ = _args[5];
lean_object* v_params_3229_ = _args[6];
lean_object* v___x_3230_ = _args[7];
lean_object* v___x_3231_ = _args[8];
lean_object* v_inst_3232_ = _args[9];
lean_object* v_R_3233_ = _args[10];
lean_object* v_a_3234_ = _args[11];
lean_object* v_b_3235_ = _args[12];
lean_object* v_c_3236_ = _args[13];
lean_object* v___y_3237_ = _args[14];
lean_object* v___y_3238_ = _args[15];
lean_object* v___y_3239_ = _args[16];
lean_object* v___y_3240_ = _args[17];
lean_object* v___y_3241_ = _args[18];
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3223_, v_val_3224_, v_upperBound_3225_, v_args_3226_, v_e_3227_, v_next_3228_, v_params_3229_, v___x_3230_, v___x_3231_, v_inst_3232_, v_R_3233_, v_a_3234_, v_b_3235_, v_c_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___x_3231_);
lean_dec(v___x_3230_);
lean_dec_ref(v_params_3229_);
lean_dec(v_next_3228_);
lean_dec_ref(v_args_3226_);
lean_dec(v_upperBound_3225_);
lean_dec(v_val_3223_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v___x_3243_, lean_object* v_preDefs_3244_, lean_object* v_val_3245_, lean_object* v_upperBound_3246_, lean_object* v_inst_3247_, lean_object* v_R_3248_, lean_object* v_a_3249_, lean_object* v_b_3250_, lean_object* v_c_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3243_, v_preDefs_3244_, v_val_3245_, v_upperBound_3246_, v_a_3249_, v_b_3250_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v___x_3258_, lean_object* v_preDefs_3259_, lean_object* v_val_3260_, lean_object* v_upperBound_3261_, lean_object* v_inst_3262_, lean_object* v_R_3263_, lean_object* v_a_3264_, lean_object* v_b_3265_, lean_object* v_c_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3258_, v_preDefs_3259_, v_val_3260_, v_upperBound_3261_, v_inst_3262_, v_R_3263_, v_a_3264_, v_b_3265_, v_c_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v_upperBound_3261_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_00_u03b2_3273_, lean_object* v_m_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___redArg(v_m_3274_, v_a_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_00_u03b2_3277_, lean_object* v_m_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_00_u03b2_3277_, v_m_3278_, v_a_3279_);
lean_dec_ref(v_a_3279_);
lean_dec_ref(v_m_3278_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_upperBound_3281_, lean_object* v___x_3282_, lean_object* v_pre_3283_, lean_object* v_post_3284_, uint8_t v_usedLetOnly_3285_, uint8_t v_skipConstInApp_3286_, uint8_t v_skipInstances_3287_, lean_object* v_postApp_3288_, lean_object* v___x_3289_, lean_object* v_inst_3290_, lean_object* v_R_3291_, lean_object* v_a_3292_, lean_object* v_b_3293_, lean_object* v_c_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_upperBound_3281_, v___x_3282_, v_pre_3283_, v_post_3284_, v_usedLetOnly_3285_, v_skipConstInApp_3286_, v_skipInstances_3287_, v_postApp_3288_, v_a_3292_, v_b_3293_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object** _args){
lean_object* v_upperBound_3302_ = _args[0];
lean_object* v___x_3303_ = _args[1];
lean_object* v_pre_3304_ = _args[2];
lean_object* v_post_3305_ = _args[3];
lean_object* v_usedLetOnly_3306_ = _args[4];
lean_object* v_skipConstInApp_3307_ = _args[5];
lean_object* v_skipInstances_3308_ = _args[6];
lean_object* v_postApp_3309_ = _args[7];
lean_object* v___x_3310_ = _args[8];
lean_object* v_inst_3311_ = _args[9];
lean_object* v_R_3312_ = _args[10];
lean_object* v_a_3313_ = _args[11];
lean_object* v_b_3314_ = _args[12];
lean_object* v_c_3315_ = _args[13];
lean_object* v___y_3316_ = _args[14];
lean_object* v___y_3317_ = _args[15];
lean_object* v___y_3318_ = _args[16];
lean_object* v___y_3319_ = _args[17];
lean_object* v___y_3320_ = _args[18];
lean_object* v___y_3321_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3322_; uint8_t v_skipConstInApp_boxed_3323_; uint8_t v_skipInstances_boxed_3324_; lean_object* v_res_3325_; 
v_usedLetOnly_boxed_3322_ = lean_unbox(v_usedLetOnly_3306_);
v_skipConstInApp_boxed_3323_ = lean_unbox(v_skipConstInApp_3307_);
v_skipInstances_boxed_3324_ = lean_unbox(v_skipInstances_3308_);
v_res_3325_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_upperBound_3302_, v___x_3303_, v_pre_3304_, v_post_3305_, v_usedLetOnly_boxed_3322_, v_skipConstInApp_boxed_3323_, v_skipInstances_boxed_3324_, v_postApp_3309_, v___x_3310_, v_inst_3311_, v_R_3312_, v_a_3313_, v_b_3314_, v_c_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec(v___x_3310_);
lean_dec_ref(v___x_3303_);
lean_dec(v_upperBound_3302_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3326_, lean_object* v_name_3327_, uint8_t v_bi_3328_, lean_object* v_type_3329_, lean_object* v_k_3330_, uint8_t v_kind_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3327_, v_bi_3328_, v_type_3329_, v_k_3330_, v_kind_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3339_, lean_object* v_name_3340_, lean_object* v_bi_3341_, lean_object* v_type_3342_, lean_object* v_k_3343_, lean_object* v_kind_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
uint8_t v_bi_boxed_3351_; uint8_t v_kind_boxed_3352_; lean_object* v_res_3353_; 
v_bi_boxed_3351_ = lean_unbox(v_bi_3341_);
v_kind_boxed_3352_ = lean_unbox(v_kind_3344_);
v_res_3353_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3339_, v_name_3340_, v_bi_boxed_3351_, v_type_3342_, v_k_3343_, v_kind_boxed_3352_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3354_, lean_object* v_name_3355_, lean_object* v_type_3356_, lean_object* v_val_3357_, lean_object* v_k_3358_, uint8_t v_nondep_3359_, uint8_t v_kind_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3355_, v_type_3356_, v_val_3357_, v_k_3358_, v_nondep_3359_, v_kind_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3368_, lean_object* v_name_3369_, lean_object* v_type_3370_, lean_object* v_val_3371_, lean_object* v_k_3372_, lean_object* v_nondep_3373_, lean_object* v_kind_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
uint8_t v_nondep_boxed_3381_; uint8_t v_kind_boxed_3382_; lean_object* v_res_3383_; 
v_nondep_boxed_3381_ = lean_unbox(v_nondep_3373_);
v_kind_boxed_3382_ = lean_unbox(v_kind_3374_);
v_res_3383_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3368_, v_name_3369_, v_type_3370_, v_val_3371_, v_k_3372_, v_nondep_boxed_3381_, v_kind_boxed_3382_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3384_, lean_object* v_ref_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3385_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3392_, lean_object* v_ref_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3392_, v_ref_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3400_, lean_object* v_x_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3409_, lean_object* v_x_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3409_, v_x_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3418_, lean_object* v_m_3419_, lean_object* v_a_3420_, lean_object* v_b_3421_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3419_, v_a_3420_, v_b_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12(lean_object* v_00_u03b2_3423_, lean_object* v_a_3424_, lean_object* v_x_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___redArg(v_a_3424_, v_x_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12___boxed(lean_object* v_00_u03b2_3427_, lean_object* v_a_3428_, lean_object* v_x_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10_spec__12(v_00_u03b2_3427_, v_a_3428_, v_x_3429_);
lean_dec(v_x_3429_);
lean_dec_ref(v_a_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3431_, lean_object* v_a_3432_, lean_object* v_x_3433_){
_start:
{
uint8_t v___x_3434_; 
v___x_3434_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3432_, v_x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3435_, lean_object* v_a_3436_, lean_object* v_x_3437_){
_start:
{
uint8_t v_res_3438_; lean_object* v_r_3439_; 
v_res_3438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3435_, v_a_3436_, v_x_3437_);
lean_dec(v_x_3437_);
lean_dec_ref(v_a_3436_);
v_r_3439_ = lean_box(v_res_3438_);
return v_r_3439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3440_, lean_object* v_data_3441_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3441_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3443_, lean_object* v_a_3444_, lean_object* v_b_3445_, lean_object* v_x_3446_){
_start:
{
lean_object* v___x_3447_; 
v___x_3447_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3444_, v_b_3445_, v_x_3446_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3448_, lean_object* v_i_3449_, lean_object* v_source_3450_, lean_object* v_target_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3449_, v_source_3450_, v_target_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3453_, lean_object* v_x_3454_, lean_object* v_x_3455_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3454_, v_x_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3470_, lean_object* v_x_3471_){
_start:
{
if (lean_obj_tag(v_x_3470_) == 0)
{
lean_object* v___x_3472_; 
v___x_3472_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3472_;
}
else
{
lean_object* v_val_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3484_; 
v_val_3473_ = lean_ctor_get(v_x_3470_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_x_3470_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3475_ = v_x_3470_;
v_isShared_3476_ = v_isSharedCheck_3484_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_val_3473_);
lean_dec(v_x_3470_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3484_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v___x_3477_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3478_ = l_Nat_reprFast(v_val_3473_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set_tag(v___x_3475_, 3);
lean_ctor_set(v___x_3475_, 0, v___x_3478_);
v___x_3480_ = v___x_3475_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3477_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = l_Repr_addAppParen(v___x_3481_, v_x_3471_);
return v___x_3482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3485_, lean_object* v_x_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3485_, v_x_3486_);
lean_dec(v_x_3486_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3488_, lean_object* v_x_3489_, lean_object* v_x_3490_){
_start:
{
if (lean_obj_tag(v_x_3490_) == 0)
{
lean_dec(v_x_3488_);
return v_x_3489_;
}
else
{
lean_object* v_head_3491_; lean_object* v_tail_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3503_; 
v_head_3491_ = lean_ctor_get(v_x_3490_, 0);
v_tail_3492_ = lean_ctor_get(v_x_3490_, 1);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_x_3490_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3494_ = v_x_3490_;
v_isShared_3495_ = v_isSharedCheck_3503_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_tail_3492_);
lean_inc(v_head_3491_);
lean_dec(v_x_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3503_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
lean_inc(v_x_3488_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set_tag(v___x_3494_, 5);
lean_ctor_set(v___x_3494_, 1, v_x_3488_);
lean_ctor_set(v___x_3494_, 0, v_x_3489_);
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_x_3489_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_x_3488_);
v___x_3497_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3498_ = lean_unsigned_to_nat(0u);
v___x_3499_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3491_, v___x_3498_);
v___x_3500_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3497_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
v_x_3489_ = v___x_3500_;
v_x_3490_ = v_tail_3492_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3504_, lean_object* v_x_3505_, lean_object* v_x_3506_){
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
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3514_ = lean_unsigned_to_nat(0u);
v___x_3515_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3507_, v___x_3514_);
v___x_3516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3513_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v___x_3517_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3504_, v___x_3516_, v_tail_3508_);
return v___x_3517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_unsigned_to_nat(0u);
v___x_3522_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3520_, v___x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3523_, lean_object* v_x_3524_){
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
v___x_3528_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3527_);
return v___x_3528_;
}
else
{
lean_object* v_head_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
lean_inc(v_tail_3526_);
v_head_3529_ = lean_ctor_get(v_x_3523_, 0);
lean_inc(v_head_3529_);
lean_dec_ref_known(v_x_3523_, 2);
v___x_3530_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3529_);
v___x_3531_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3524_, v___x_3530_, v_tail_3526_);
return v___x_3531_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3540_ = lean_string_length(v___x_3539_);
return v___x_3540_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3542_ = lean_nat_to_int(v___x_3541_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3548_){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v___x_3549_ = lean_array_get_size(v_xs_3548_);
v___x_3550_ = lean_unsigned_to_nat(0u);
v___x_3551_ = lean_nat_dec_eq(v___x_3549_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3552_ = lean_array_to_list(v_xs_3548_);
v___x_3553_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3554_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3552_, v___x_3553_);
v___x_3555_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3556_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v___x_3554_);
v___x_3558_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3557_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3555_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Std_Format_fill(v___x_3560_);
return v___x_3561_;
}
else
{
lean_object* v___x_3562_; 
lean_dec_ref(v_xs_3548_);
v___x_3562_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3562_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3563_, lean_object* v_x_3564_, lean_object* v_x_3565_){
_start:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_dec(v_x_3563_);
return v_x_3564_;
}
else
{
lean_object* v_head_3566_; lean_object* v_tail_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3577_; 
v_head_3566_ = lean_ctor_get(v_x_3565_, 0);
v_tail_3567_ = lean_ctor_get(v_x_3565_, 1);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_x_3565_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3569_ = v_x_3565_;
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_tail_3567_);
lean_inc(v_head_3566_);
lean_dec(v_x_3565_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3577_;
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
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_x_3564_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_x_3563_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3566_);
v___x_3574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v_x_3564_ = v___x_3574_;
v_x_3565_ = v_tail_3567_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3578_, lean_object* v_x_3579_){
_start:
{
if (lean_obj_tag(v_x_3578_) == 0)
{
lean_object* v___x_3580_; 
lean_dec(v_x_3579_);
v___x_3580_ = lean_box(0);
return v___x_3580_;
}
else
{
lean_object* v_tail_3581_; 
v_tail_3581_ = lean_ctor_get(v_x_3578_, 1);
if (lean_obj_tag(v_tail_3581_) == 0)
{
lean_object* v_head_3582_; lean_object* v___x_3583_; 
lean_dec(v_x_3579_);
v_head_3582_ = lean_ctor_get(v_x_3578_, 0);
lean_inc(v_head_3582_);
lean_dec_ref_known(v_x_3578_, 2);
v___x_3583_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3582_);
return v___x_3583_;
}
else
{
lean_object* v_head_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_inc(v_tail_3581_);
v_head_3584_ = lean_ctor_get(v_x_3578_, 0);
lean_inc(v_head_3584_);
lean_dec_ref_known(v_x_3578_, 2);
v___x_3585_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3584_);
v___x_3586_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3579_, v___x_3585_, v_tail_3581_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3587_){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v___x_3588_ = lean_array_get_size(v_xs_3587_);
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = lean_nat_dec_eq(v___x_3588_, v___x_3589_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3591_ = lean_array_to_list(v_xs_3587_);
v___x_3592_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3593_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3591_, v___x_3592_);
v___x_3594_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3595_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3596_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
lean_ctor_set(v___x_3596_, 1, v___x_3593_);
v___x_3597_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3594_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = l_Std_Format_fill(v___x_3599_);
return v___x_3600_;
}
else
{
lean_object* v___x_3601_; 
lean_dec_ref(v_xs_3587_);
v___x_3601_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3601_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
if (lean_obj_tag(v_x_3604_) == 0)
{
lean_dec(v_x_3602_);
return v_x_3603_;
}
else
{
lean_object* v_head_3605_; lean_object* v_tail_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3617_; 
v_head_3605_ = lean_ctor_get(v_x_3604_, 0);
v_tail_3606_ = lean_ctor_get(v_x_3604_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_x_3604_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3608_ = v_x_3604_;
v_isShared_3609_ = v_isSharedCheck_3617_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_tail_3606_);
lean_inc(v_head_3605_);
lean_dec(v_x_3604_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3617_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
lean_inc(v_x_3602_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 5);
lean_ctor_set(v___x_3608_, 1, v_x_3602_);
lean_ctor_set(v___x_3608_, 0, v_x_3603_);
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_x_3603_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_x_3602_);
v___x_3611_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = l_Nat_reprFast(v_head_3605_);
v___x_3613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3611_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v_x_3603_ = v___x_3614_;
v_x_3604_ = v_tail_3606_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3618_, lean_object* v_x_3619_, lean_object* v_x_3620_){
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
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3628_ = l_Nat_reprFast(v_head_3621_);
v___x_3629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
v___x_3630_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3627_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3618_, v___x_3630_, v_tail_3622_);
return v___x_3631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = l_Nat_reprFast(v___y_3634_);
v___x_3636_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3637_, lean_object* v_x_3638_){
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
v___x_3642_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3641_);
return v___x_3642_;
}
else
{
lean_object* v_head_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_inc(v_tail_3640_);
v_head_3643_ = lean_ctor_get(v_x_3637_, 0);
lean_inc(v_head_3643_);
lean_dec_ref_known(v_x_3637_, 2);
v___x_3644_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3643_);
v___x_3645_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3638_, v___x_3644_, v_tail_3640_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3646_){
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
v___x_3652_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3650_, v___x_3651_);
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
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3661_, lean_object* v_x_3662_, lean_object* v_x_3663_){
_start:
{
if (lean_obj_tag(v_x_3663_) == 0)
{
lean_dec(v_x_3661_);
return v_x_3662_;
}
else
{
lean_object* v_head_3664_; lean_object* v_tail_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3675_; 
v_head_3664_ = lean_ctor_get(v_x_3663_, 0);
v_tail_3665_ = lean_ctor_get(v_x_3663_, 1);
v_isSharedCheck_3675_ = !lean_is_exclusive(v_x_3663_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3667_ = v_x_3663_;
v_isShared_3668_ = v_isSharedCheck_3675_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_tail_3665_);
lean_inc(v_head_3664_);
lean_dec(v_x_3663_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3675_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
lean_inc(v_x_3661_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 5);
lean_ctor_set(v___x_3667_, 1, v_x_3661_);
lean_ctor_set(v___x_3667_, 0, v_x_3662_);
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_x_3662_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_x_3661_);
v___x_3670_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3664_);
v___x_3672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3670_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v_x_3662_ = v___x_3672_;
v_x_3663_ = v_tail_3665_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3676_, lean_object* v_x_3677_){
_start:
{
if (lean_obj_tag(v_x_3676_) == 0)
{
lean_object* v___x_3678_; 
lean_dec(v_x_3677_);
v___x_3678_ = lean_box(0);
return v___x_3678_;
}
else
{
lean_object* v_tail_3679_; 
v_tail_3679_ = lean_ctor_get(v_x_3676_, 1);
if (lean_obj_tag(v_tail_3679_) == 0)
{
lean_object* v_head_3680_; lean_object* v___x_3681_; 
lean_dec(v_x_3677_);
v_head_3680_ = lean_ctor_get(v_x_3676_, 0);
lean_inc(v_head_3680_);
lean_dec_ref_known(v_x_3676_, 2);
v___x_3681_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3680_);
return v___x_3681_;
}
else
{
lean_object* v_head_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_inc(v_tail_3679_);
v_head_3682_ = lean_ctor_get(v_x_3676_, 0);
lean_inc(v_head_3682_);
lean_dec_ref_known(v_x_3676_, 2);
v___x_3683_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3682_);
v___x_3684_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3677_, v___x_3683_, v_tail_3679_);
return v___x_3684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3685_){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v___x_3686_ = lean_array_get_size(v_xs_3685_);
v___x_3687_ = lean_unsigned_to_nat(0u);
v___x_3688_ = lean_nat_dec_eq(v___x_3686_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3689_ = lean_array_to_list(v_xs_3685_);
v___x_3690_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3691_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3689_, v___x_3690_);
v___x_3692_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3693_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
lean_ctor_set(v___x_3694_, 1, v___x_3691_);
v___x_3695_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3692_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l_Std_Format_fill(v___x_3697_);
return v___x_3698_;
}
else
{
lean_object* v___x_3699_; 
lean_dec_ref(v_xs_3685_);
v___x_3699_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3699_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_){
_start:
{
if (lean_obj_tag(v_x_3702_) == 0)
{
lean_dec(v_x_3700_);
return v_x_3701_;
}
else
{
lean_object* v_head_3703_; lean_object* v_tail_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3714_; 
v_head_3703_ = lean_ctor_get(v_x_3702_, 0);
v_tail_3704_ = lean_ctor_get(v_x_3702_, 1);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_x_3702_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3706_ = v_x_3702_;
v_isShared_3707_ = v_isSharedCheck_3714_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_tail_3704_);
lean_inc(v_head_3703_);
lean_dec(v_x_3702_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3714_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
lean_inc(v_x_3700_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 5);
lean_ctor_set(v___x_3706_, 1, v_x_3700_);
lean_ctor_set(v___x_3706_, 0, v_x_3701_);
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_x_3701_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_x_3700_);
v___x_3709_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3703_);
v___x_3711_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v_x_3701_ = v___x_3711_;
v_x_3702_ = v_tail_3704_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3715_, lean_object* v_x_3716_){
_start:
{
if (lean_obj_tag(v_x_3715_) == 0)
{
lean_object* v___x_3717_; 
lean_dec(v_x_3716_);
v___x_3717_ = lean_box(0);
return v___x_3717_;
}
else
{
lean_object* v_tail_3718_; 
v_tail_3718_ = lean_ctor_get(v_x_3715_, 1);
if (lean_obj_tag(v_tail_3718_) == 0)
{
lean_object* v_head_3719_; lean_object* v___x_3720_; 
lean_dec(v_x_3716_);
v_head_3719_ = lean_ctor_get(v_x_3715_, 0);
lean_inc(v_head_3719_);
lean_dec_ref_known(v_x_3715_, 2);
v___x_3720_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3719_);
return v___x_3720_;
}
else
{
lean_object* v_head_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_inc(v_tail_3718_);
v_head_3721_ = lean_ctor_get(v_x_3715_, 0);
lean_inc(v_head_3721_);
lean_dec_ref_known(v_x_3715_, 2);
v___x_3722_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3721_);
v___x_3723_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3716_, v___x_3722_, v_tail_3718_);
return v___x_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3724_){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; 
v___x_3725_ = lean_array_get_size(v_xs_3724_);
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_nat_dec_eq(v___x_3725_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3728_ = lean_array_to_list(v_xs_3724_);
v___x_3729_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3730_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3728_, v___x_3729_);
v___x_3731_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3732_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v___x_3730_);
v___x_3734_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3731_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Std_Format_fill(v___x_3736_);
return v___x_3737_;
}
else
{
lean_object* v___x_3738_; 
lean_dec_ref(v_xs_3724_);
v___x_3738_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3738_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_unsigned_to_nat(12u);
v___x_3753_ = lean_nat_to_int(v___x_3752_);
return v___x_3753_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = lean_unsigned_to_nat(9u);
v___x_3758_ = lean_nat_to_int(v___x_3757_);
return v___x_3758_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = lean_unsigned_to_nat(11u);
v___x_3763_ = lean_nat_to_int(v___x_3762_);
return v___x_3763_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3766_ = lean_string_length(v___x_3765_);
return v___x_3766_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3768_ = lean_nat_to_int(v___x_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3773_){
_start:
{
lean_object* v_numFixed_3774_; lean_object* v_perms_3775_; lean_object* v_revDeps_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v_numFixed_3774_ = lean_ctor_get(v_x_3773_, 0);
lean_inc(v_numFixed_3774_);
v_perms_3775_ = lean_ctor_get(v_x_3773_, 1);
lean_inc_ref(v_perms_3775_);
v_revDeps_3776_ = lean_ctor_get(v_x_3773_, 2);
lean_inc_ref(v_revDeps_3776_);
lean_dec_ref(v_x_3773_);
v___x_3777_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3778_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3779_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3780_ = l_Nat_reprFast(v_numFixed_3774_);
v___x_3781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3779_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = 0;
v___x_3784_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*1, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3778_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_box(1);
v___x_3789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
lean_ctor_set(v___x_3792_, 1, v___x_3777_);
v___x_3793_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3794_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3775_);
v___x_3795_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3793_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set_uint8(v___x_3796_, sizeof(void*)*1, v___x_3783_);
v___x_3797_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3792_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v___x_3786_);
v___x_3799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
lean_ctor_set(v___x_3799_, 1, v___x_3788_);
v___x_3800_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3801_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
lean_ctor_set(v___x_3802_, 1, v___x_3777_);
v___x_3803_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3804_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3776_);
v___x_3805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3803_);
lean_ctor_set(v___x_3805_, 1, v___x_3804_);
v___x_3806_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set_uint8(v___x_3806_, sizeof(void*)*1, v___x_3783_);
v___x_3807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3802_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3809_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___x_3807_);
v___x_3811_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3808_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set_uint8(v___x_3814_, sizeof(void*)*1, v___x_3783_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3815_, lean_object* v_prec_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3818_, lean_object* v_prec_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3818_, v_prec_3819_);
lean_dec(v_prec_3819_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___f_3829_; lean_object* v___x_5728__overap_3830_; lean_object* v___x_3831_; 
v___f_3829_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5728__overap_3830_ = lean_panic_fn_borrowed(v___f_3829_, v_msg_3823_);
lean_inc(v___y_3827_);
lean_inc_ref(v___y_3826_);
lean_inc(v___y_3825_);
lean_inc_ref(v___y_3824_);
v___x_3831_ = lean_apply_5(v___x_5728__overap_3830_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, lean_box(0));
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___f_3845_; lean_object* v___x_5738__overap_3846_; lean_object* v___x_3847_; 
v___f_3845_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5738__overap_3846_ = lean_panic_fn_borrowed(v___f_3845_, v_msg_3839_);
lean_inc(v___y_3843_);
lean_inc_ref(v___y_3842_);
lean_inc(v___y_3841_);
lean_inc_ref(v___y_3840_);
v___x_3847_ = lean_apply_5(v___x_5738__overap_3846_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, lean_box(0));
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___f_3861_; lean_object* v___x_5748__overap_3862_; lean_object* v___x_3863_; 
v___f_3861_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5748__overap_3862_ = lean_panic_fn_borrowed(v___f_3861_, v_msg_3855_);
lean_inc(v___y_3859_);
lean_inc_ref(v___y_3858_);
lean_inc(v___y_3857_);
lean_inc_ref(v___y_3856_);
v___x_3863_ = lean_apply_5(v___x_5748__overap_3862_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, lean_box(0));
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
return v_res_3870_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3874_ = lean_unsigned_to_nat(12u);
v___x_3875_ = lean_unsigned_to_nat(294u);
v___x_3876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3877_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3878_ = l_mkPanicMessageWithDecl(v___x_3877_, v___x_3876_, v___x_3875_, v___x_3874_, v___x_3873_);
return v___x_3878_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3881_ = lean_unsigned_to_nat(12u);
v___x_3882_ = lean_unsigned_to_nat(297u);
v___x_3883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3884_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3885_ = l_mkPanicMessageWithDecl(v___x_3884_, v___x_3883_, v___x_3882_, v___x_3881_, v___x_3880_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3886_, lean_object* v_as_3887_, size_t v_sz_3888_, size_t v_i_3889_, lean_object* v_b_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_a_3897_; uint8_t v___x_3901_; 
v___x_3901_ = lean_usize_dec_lt(v_i_3889_, v_sz_3888_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3902_, 0, v_b_3890_);
return v___x_3902_;
}
else
{
lean_object* v_a_3903_; 
v_a_3903_ = lean_array_uget_borrowed(v_as_3887_, v_i_3889_);
if (lean_obj_tag(v_a_3903_) == 1)
{
lean_object* v_val_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_val_3904_ = lean_ctor_get(v_a_3903_, 0);
v___x_3905_ = lean_box(0);
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = lean_array_get_borrowed(v___x_3905_, v_val_3904_, v___x_3906_);
if (lean_obj_tag(v___x_3907_) == 1)
{
lean_object* v_val_3908_; lean_object* v___x_3909_; 
v_val_3908_ = lean_ctor_get(v___x_3907_, 0);
v___x_3909_ = lean_array_get_borrowed(v___x_3905_, v___x_3886_, v_val_3908_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref(v_b_3890_);
v___x_3910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3911_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3910_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3921_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3914_ = v___x_3911_;
v_isShared_3915_ = v_isSharedCheck_3921_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3921_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
if (lean_obj_tag(v_a_3912_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; 
v_a_3916_ = lean_ctor_get(v_a_3912_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v_a_3912_, 1);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v_a_3916_);
v___x_3918_ = v___x_3914_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
else
{
lean_object* v_a_3920_; 
lean_del_object(v___x_3914_);
v_a_3920_ = lean_ctor_get(v_a_3912_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v_a_3912_, 1);
v_a_3897_ = v_a_3920_;
goto v___jp_3896_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
v_a_3922_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3911_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3911_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v___x_3930_; 
lean_inc_ref(v___x_3909_);
v___x_3930_ = lean_array_push(v_b_3890_, v___x_3909_);
v_a_3897_ = v___x_3930_;
goto v___jp_3896_;
}
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3932_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3931_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_dec_ref_known(v___x_3932_, 1);
v_a_3897_ = v_b_3890_;
goto v___jp_3896_;
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v_b_3890_);
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3932_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3932_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = lean_box(0);
v___x_3942_ = lean_array_push(v_b_3890_, v___x_3941_);
v_a_3897_ = v___x_3942_;
goto v___jp_3896_;
}
}
v___jp_3896_:
{
size_t v___x_3898_; size_t v___x_3899_; 
v___x_3898_ = ((size_t)1ULL);
v___x_3899_ = lean_usize_add(v_i_3889_, v___x_3898_);
v_i_3889_ = v___x_3899_;
v_b_3890_ = v_a_3897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3943_, lean_object* v_as_3944_, lean_object* v_sz_3945_, lean_object* v_i_3946_, lean_object* v_b_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
size_t v_sz_boxed_3953_; size_t v_i_boxed_3954_; lean_object* v_res_3955_; 
v_sz_boxed_3953_ = lean_unbox_usize(v_sz_3945_);
lean_dec(v_sz_3945_);
v_i_boxed_3954_ = lean_unbox_usize(v_i_3946_);
lean_dec(v_i_3946_);
v_res_3955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3943_, v_as_3944_, v_sz_boxed_3953_, v_i_boxed_3954_, v_b_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec_ref(v_as_3944_);
lean_dec_ref(v___x_3943_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3958_, lean_object* v___x_3959_, lean_object* v___x_3960_, lean_object* v_a_3961_, lean_object* v_b_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
uint8_t v___x_3968_; 
v___x_3968_ = lean_nat_dec_lt(v_a_3961_, v_upperBound_3958_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_dec(v_a_3961_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v_b_3962_);
return v___x_3969_;
}
else
{
lean_object* v___x_3970_; lean_object* v___x_3971_; size_t v_sz_3972_; size_t v___x_3973_; lean_object* v___x_3974_; 
v___x_3970_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3971_ = lean_array_fget_borrowed(v___x_3959_, v_a_3961_);
v_sz_3972_ = lean_array_size(v___x_3971_);
v___x_3973_ = ((size_t)0ULL);
v___x_3974_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3960_, v___x_3971_, v_sz_3972_, v___x_3973_, v___x_3970_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v___x_3974_, 1);
v___x_3976_ = lean_array_push(v_b_3962_, v_a_3975_);
v___x_3977_ = lean_unsigned_to_nat(1u);
v___x_3978_ = lean_nat_add(v_a_3961_, v___x_3977_);
lean_dec(v_a_3961_);
v_a_3961_ = v___x_3978_;
v_b_3962_ = v___x_3976_;
goto _start;
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v_b_3962_);
lean_dec(v_a_3961_);
v_a_3980_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3974_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3974_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3988_, lean_object* v___x_3989_, lean_object* v___x_3990_, lean_object* v_a_3991_, lean_object* v_b_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3988_, v___x_3989_, v___x_3990_, v_a_3991_, v_b_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec_ref(v___x_3990_);
lean_dec_ref(v___x_3989_);
lean_dec(v_upperBound_3988_);
return v_res_3998_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4000_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_4001_ = lean_unsigned_to_nat(8u);
v___x_4002_ = lean_unsigned_to_nat(281u);
v___x_4003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4005_ = l_mkPanicMessageWithDecl(v___x_4004_, v___x_4003_, v___x_4002_, v___x_4001_, v___x_4000_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_4006_, lean_object* v_a_4007_, lean_object* v_b_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_a_4015_; uint8_t v___x_4019_; 
v___x_4019_ = lean_nat_dec_lt(v_a_4007_, v_upperBound_4006_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; 
lean_dec(v_a_4007_);
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v_b_4008_);
return v___x_4020_;
}
else
{
lean_object* v_snd_4021_; lean_object* v_snd_4022_; lean_object* v_snd_4023_; lean_object* v_fst_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4148_; 
v_snd_4021_ = lean_ctor_get(v_b_4008_, 1);
lean_inc(v_snd_4021_);
v_snd_4022_ = lean_ctor_get(v_snd_4021_, 1);
lean_inc(v_snd_4022_);
v_snd_4023_ = lean_ctor_get(v_snd_4022_, 1);
lean_inc(v_snd_4023_);
v_fst_4024_ = lean_ctor_get(v_b_4008_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_b_4008_);
if (v_isSharedCheck_4148_ == 0)
{
lean_object* v_unused_4149_; 
v_unused_4149_ = lean_ctor_get(v_b_4008_, 1);
lean_dec(v_unused_4149_);
v___x_4026_ = v_b_4008_;
v_isShared_4027_ = v_isSharedCheck_4148_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_fst_4024_);
lean_dec(v_b_4008_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4148_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v_fst_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4146_; 
v_fst_4028_ = lean_ctor_get(v_snd_4021_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v_snd_4021_);
if (v_isSharedCheck_4146_ == 0)
{
lean_object* v_unused_4147_; 
v_unused_4147_ = lean_ctor_get(v_snd_4021_, 1);
lean_dec(v_unused_4147_);
v___x_4030_ = v_snd_4021_;
v_isShared_4031_ = v_isSharedCheck_4146_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_fst_4028_);
lean_dec(v_snd_4021_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4146_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v_fst_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4144_; 
v_fst_4032_ = lean_ctor_get(v_snd_4022_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_snd_4022_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v_snd_4022_, 1);
lean_dec(v_unused_4145_);
v___x_4034_ = v_snd_4022_;
v_isShared_4035_ = v_isSharedCheck_4144_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_fst_4032_);
lean_dec(v_snd_4022_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4144_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v_array_4036_; lean_object* v_start_4037_; lean_object* v_stop_4038_; uint8_t v___x_4039_; 
v_array_4036_ = lean_ctor_get(v_snd_4023_, 0);
v_start_4037_ = lean_ctor_get(v_snd_4023_, 1);
v_stop_4038_ = lean_ctor_get(v_snd_4023_, 2);
v___x_4039_ = lean_nat_dec_lt(v_start_4037_, v_stop_4038_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4041_; 
lean_dec(v_a_4007_);
if (v_isShared_4035_ == 0)
{
v___x_4041_ = v___x_4034_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_fst_4032_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_snd_4023_);
v___x_4041_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4043_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4041_);
v___x_4043_ = v___x_4030_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_fst_4028_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v___x_4041_);
v___x_4043_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
lean_object* v___x_4045_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4043_);
v___x_4045_ = v___x_4026_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_fst_4024_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_4043_);
v___x_4045_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
lean_object* v___x_4046_; 
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
}
}
else
{
lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4140_; 
lean_inc(v_stop_4038_);
lean_inc(v_start_4037_);
lean_inc_ref(v_array_4036_);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_snd_4023_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; lean_object* v_unused_4142_; lean_object* v_unused_4143_; 
v_unused_4141_ = lean_ctor_get(v_snd_4023_, 2);
lean_dec(v_unused_4141_);
v_unused_4142_ = lean_ctor_get(v_snd_4023_, 1);
lean_dec(v_unused_4142_);
v_unused_4143_ = lean_ctor_get(v_snd_4023_, 0);
lean_dec(v_unused_4143_);
v___x_4051_ = v_snd_4023_;
v_isShared_4052_ = v_isSharedCheck_4140_;
goto v_resetjp_4050_;
}
else
{
lean_dec(v_snd_4023_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4140_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v_array_4053_; lean_object* v_start_4054_; lean_object* v_stop_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4060_; 
v_array_4053_ = lean_ctor_get(v_fst_4032_, 0);
v_start_4054_ = lean_ctor_get(v_fst_4032_, 1);
v_stop_4055_ = lean_ctor_get(v_fst_4032_, 2);
v___x_4056_ = lean_array_fget(v_array_4036_, v_start_4037_);
v___x_4057_ = lean_unsigned_to_nat(1u);
v___x_4058_ = lean_nat_add(v_start_4037_, v___x_4057_);
lean_dec(v_start_4037_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 1, v___x_4058_);
v___x_4060_ = v___x_4051_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_array_4036_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4139_, 2, v_stop_4038_);
v___x_4060_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
uint8_t v___x_4061_; 
v___x_4061_ = lean_nat_dec_lt(v_start_4054_, v_stop_4055_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4063_; 
lean_dec(v___x_4056_);
lean_dec(v_a_4007_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 1, v___x_4060_);
v___x_4063_ = v___x_4034_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_fst_4032_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v___x_4060_);
v___x_4063_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4065_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4063_);
v___x_4065_ = v___x_4030_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_fst_4028_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4067_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4065_);
v___x_4067_ = v___x_4026_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_fst_4024_);
lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
}
}
else
{
lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4135_; 
lean_inc(v_stop_4055_);
lean_inc(v_start_4054_);
lean_inc_ref(v_array_4053_);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_fst_4032_);
if (v_isSharedCheck_4135_ == 0)
{
lean_object* v_unused_4136_; lean_object* v_unused_4137_; lean_object* v_unused_4138_; 
v_unused_4136_ = lean_ctor_get(v_fst_4032_, 2);
lean_dec(v_unused_4136_);
v_unused_4137_ = lean_ctor_get(v_fst_4032_, 1);
lean_dec(v_unused_4137_);
v_unused_4138_ = lean_ctor_get(v_fst_4032_, 0);
lean_dec(v_unused_4138_);
v___x_4073_ = v_fst_4032_;
v_isShared_4074_ = v_isSharedCheck_4135_;
goto v_resetjp_4072_;
}
else
{
lean_dec(v_fst_4032_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4135_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4075_; lean_object* v___x_4077_; 
v___x_4075_ = lean_nat_add(v_start_4054_, v___x_4057_);
lean_dec(v_start_4054_);
if (v_isShared_4074_ == 0)
{
lean_ctor_set(v___x_4073_, 1, v___x_4075_);
v___x_4077_ = v___x_4073_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_array_4053_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v___x_4075_);
lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_stop_4055_);
v___x_4077_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
if (lean_obj_tag(v___x_4056_) == 1)
{
lean_object* v_val_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4122_; 
v_val_4078_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4080_ = v___x_4056_;
v_isShared_4081_ = v_isSharedCheck_4122_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_val_4078_);
lean_dec(v___x_4056_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4122_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
v___x_4082_ = lean_box(0);
v___x_4083_ = lean_unsigned_to_nat(0u);
v___x_4084_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4085_ = lean_array_get(v___x_4082_, v_val_4078_, v___x_4083_);
lean_dec(v_val_4078_);
lean_inc(v_a_4007_);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_a_4007_);
v___x_4087_ = v___x_4080_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4007_);
v___x_4087_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
uint8_t v___x_4088_; 
v___x_4088_ = l_Option_instDecidableEq___redArg(v___x_4084_, v___x_4085_, v___x_4087_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
lean_dec_ref(v___x_4077_);
lean_dec_ref(v___x_4060_);
lean_del_object(v___x_4034_);
lean_del_object(v___x_4030_);
lean_dec(v_fst_4028_);
lean_del_object(v___x_4026_);
lean_dec(v_fst_4024_);
v___x_4089_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4090_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4089_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4100_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4100_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4100_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
if (lean_obj_tag(v_a_4091_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4097_; 
lean_dec(v_a_4007_);
v_a_4095_ = lean_ctor_get(v_a_4091_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v_a_4091_, 1);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 0, v_a_4095_);
v___x_4097_ = v___x_4093_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4095_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
else
{
lean_object* v_a_4099_; 
lean_del_object(v___x_4093_);
v_a_4099_ = lean_ctor_get(v_a_4091_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v_a_4091_, 1);
v_a_4015_ = v_a_4099_;
goto v___jp_4014_;
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec(v_a_4007_);
v_a_4101_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4090_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4090_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4113_; 
lean_inc(v_fst_4028_);
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_fst_4028_);
v___x_4110_ = lean_array_push(v_fst_4024_, v___x_4109_);
v___x_4111_ = lean_nat_add(v_fst_4028_, v___x_4057_);
lean_dec(v_fst_4028_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 1, v___x_4060_);
lean_ctor_set(v___x_4034_, 0, v___x_4077_);
v___x_4113_ = v___x_4034_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v___x_4060_);
v___x_4113_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4115_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4113_);
lean_ctor_set(v___x_4030_, 0, v___x_4111_);
v___x_4115_ = v___x_4030_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v___x_4111_);
lean_ctor_set(v_reuseFailAlloc_4119_, 1, v___x_4113_);
v___x_4115_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
lean_object* v___x_4117_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4115_);
lean_ctor_set(v___x_4026_, 0, v___x_4110_);
v___x_4117_ = v___x_4026_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4110_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v___x_4115_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
v_a_4015_ = v___x_4117_;
goto v___jp_4014_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4126_; 
lean_dec(v___x_4056_);
v___x_4123_ = lean_box(0);
v___x_4124_ = lean_array_push(v_fst_4024_, v___x_4123_);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 1, v___x_4060_);
lean_ctor_set(v___x_4034_, 0, v___x_4077_);
v___x_4126_ = v___x_4034_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4077_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v___x_4060_);
v___x_4126_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4128_; 
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 1, v___x_4126_);
v___x_4128_ = v___x_4030_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_fst_4028_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4130_; 
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4128_);
lean_ctor_set(v___x_4026_, 0, v___x_4124_);
v___x_4130_ = v___x_4026_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4124_);
lean_ctor_set(v_reuseFailAlloc_4131_, 1, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
v_a_4015_ = v___x_4130_;
goto v___jp_4014_;
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
v___jp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_unsigned_to_nat(1u);
v___x_4017_ = lean_nat_add(v_a_4007_, v___x_4016_);
lean_dec(v_a_4007_);
v_a_4007_ = v___x_4017_;
v_b_4008_ = v_a_4015_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4150_, lean_object* v_a_4151_, lean_object* v_b_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4150_, v_a_4151_, v_b_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v_upperBound_4150_);
return v_res_4158_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4160_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4161_ = lean_unsigned_to_nat(4u);
v___x_4162_ = lean_unsigned_to_nat(275u);
v___x_4163_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4164_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4165_ = l_mkPanicMessageWithDecl(v___x_4164_, v___x_4163_, v___x_4162_, v___x_4161_, v___x_4160_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4166_, lean_object* v___x_4167_, lean_object* v___x_4168_, lean_object* v_xs_4169_, lean_object* v_x_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_graph_4176_; lean_object* v_revDeps_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4230_; 
v_graph_4176_ = lean_ctor_get(v_a_4166_, 0);
v_revDeps_4177_ = lean_ctor_get(v_a_4166_, 1);
v_isSharedCheck_4230_ = !lean_is_exclusive(v_a_4166_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4179_ = v_a_4166_;
v_isShared_4180_ = v_isSharedCheck_4230_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_revDeps_4177_);
lean_inc(v_graph_4176_);
lean_dec(v_a_4166_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4230_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; uint8_t v___x_4184_; 
v___x_4181_ = lean_array_get_borrowed(v___x_4167_, v_graph_4176_, v___x_4168_);
v___x_4182_ = lean_array_get_size(v_xs_4169_);
v___x_4183_ = lean_array_get_size(v___x_4181_);
v___x_4184_ = lean_nat_dec_eq(v___x_4182_, v___x_4183_);
if (v___x_4184_ == 0)
{
lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_del_object(v___x_4179_);
lean_dec_ref(v_revDeps_4177_);
lean_dec_ref(v_graph_4176_);
lean_dec_ref(v_xs_4169_);
lean_dec(v___x_4168_);
v___x_4185_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4186_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4185_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
return v___x_4186_;
}
else
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4191_; 
v___x_4187_ = lean_mk_empty_array_with_capacity(v___x_4168_);
lean_inc_n(v___x_4168_, 2);
v___x_4188_ = l_Array_toSubarray___redArg(v_xs_4169_, v___x_4168_, v___x_4182_);
lean_inc(v___x_4181_);
v___x_4189_ = l_Array_toSubarray___redArg(v___x_4181_, v___x_4168_, v___x_4183_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v___x_4189_);
lean_ctor_set(v___x_4179_, 0, v___x_4188_);
v___x_4191_ = v___x_4179_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4188_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___x_4189_);
v___x_4191_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_inc(v___x_4168_);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4168_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4187_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4182_, v___x_4168_, v___x_4193_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v_snd_4196_; lean_object* v_fst_4197_; lean_object* v_fst_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v_snd_4196_ = lean_ctor_get(v_a_4195_, 1);
lean_inc(v_snd_4196_);
v_fst_4197_ = lean_ctor_get(v_a_4195_, 0);
lean_inc_n(v_fst_4197_, 2);
lean_dec(v_a_4195_);
v_fst_4198_ = lean_ctor_get(v_snd_4196_, 0);
lean_inc(v_fst_4198_);
lean_dec(v_snd_4196_);
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = lean_array_get_size(v_graph_4176_);
v___x_4201_ = lean_mk_empty_array_with_capacity(v___x_4199_);
v___x_4202_ = lean_array_push(v___x_4201_, v_fst_4197_);
v___x_4203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4200_, v_graph_4176_, v_fst_4197_, v___x_4199_, v___x_4202_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v_fst_4197_);
lean_dec_ref(v_graph_4176_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4212_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4208_; lean_object* v___x_4210_; 
v___x_4208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4208_, 0, v_fst_4198_);
lean_ctor_set(v___x_4208_, 1, v_a_4204_);
lean_ctor_set(v___x_4208_, 2, v_revDeps_4177_);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4208_);
v___x_4210_ = v___x_4206_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec(v_fst_4198_);
lean_dec_ref(v_revDeps_4177_);
v_a_4213_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4203_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4203_);
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
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec_ref(v_revDeps_4177_);
lean_dec_ref(v_graph_4176_);
v_a_4221_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4194_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4194_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4231_, lean_object* v___x_4232_, lean_object* v___x_4233_, lean_object* v_xs_4234_, lean_object* v_x_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4231_, v___x_4232_, v___x_4233_, v_xs_4234_, v_x_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec_ref(v_x_4235_);
lean_dec_ref(v___x_4232_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4248_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4249_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
lean_inc_ref(v_preDefs_4242_);
v___x_4250_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v_value_4254_; lean_object* v___f_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v___x_4250_, 1);
v___x_4252_ = lean_unsigned_to_nat(0u);
v___x_4253_ = lean_array_get(v___x_4248_, v_preDefs_4242_, v___x_4252_);
lean_dec_ref(v_preDefs_4242_);
v_value_4254_ = lean_ctor_get(v___x_4253_, 7);
lean_inc_ref(v_value_4254_);
lean_dec(v___x_4253_);
v___f_4255_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4255_, 0, v_a_4251_);
lean_closure_set(v___f_4255_, 1, v___x_4249_);
lean_closure_set(v___f_4255_, 2, v___x_4252_);
v___x_4256_ = 0;
v___x_4257_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4254_, v___f_4255_, v___x_4256_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
return v___x_4257_;
}
else
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
lean_dec_ref(v_preDefs_4242_);
v_a_4258_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4260_ = v___x_4250_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4250_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4273_, lean_object* v___x_4274_, lean_object* v___x_4275_, lean_object* v_inst_4276_, lean_object* v_R_4277_, lean_object* v_a_4278_, lean_object* v_b_4279_, lean_object* v_c_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v___x_4286_; 
v___x_4286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4273_, v___x_4274_, v___x_4275_, v_a_4278_, v_b_4279_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4287_, lean_object* v___x_4288_, lean_object* v___x_4289_, lean_object* v_inst_4290_, lean_object* v_R_4291_, lean_object* v_a_4292_, lean_object* v_b_4293_, lean_object* v_c_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4287_, v___x_4288_, v___x_4289_, v_inst_4290_, v_R_4291_, v_a_4292_, v_b_4293_, v_c_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec_ref(v___x_4289_);
lean_dec_ref(v___x_4288_);
lean_dec(v_upperBound_4287_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4301_, lean_object* v_inst_4302_, lean_object* v_R_4303_, lean_object* v_a_4304_, lean_object* v_b_4305_, lean_object* v_c_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4301_, v_a_4304_, v_b_4305_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4313_, lean_object* v_inst_4314_, lean_object* v_R_4315_, lean_object* v_a_4316_, lean_object* v_b_4317_, lean_object* v_c_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4313_, v_inst_4314_, v_R_4315_, v_a_4316_, v_b_4317_, v_c_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v_upperBound_4313_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4325_, size_t v_i_4326_, size_t v_stop_4327_, lean_object* v_b_4328_){
_start:
{
uint8_t v___x_4329_; 
v___x_4329_ = lean_usize_dec_eq(v_i_4326_, v_stop_4327_);
if (v___x_4329_ == 0)
{
size_t v___x_4330_; size_t v___x_4331_; lean_object* v___x_4332_; 
v___x_4330_ = ((size_t)1ULL);
v___x_4331_ = lean_usize_sub(v_i_4326_, v___x_4330_);
v___x_4332_ = lean_array_uget_borrowed(v_as_4325_, v___x_4331_);
if (lean_obj_tag(v___x_4332_) == 0)
{
v_i_4326_ = v___x_4331_;
goto _start;
}
else
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = lean_unsigned_to_nat(1u);
v___x_4335_ = lean_nat_add(v_b_4328_, v___x_4334_);
lean_dec(v_b_4328_);
v_i_4326_ = v___x_4331_;
v_b_4328_ = v___x_4335_;
goto _start;
}
}
else
{
return v_b_4328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4337_, lean_object* v_i_4338_, lean_object* v_stop_4339_, lean_object* v_b_4340_){
_start:
{
size_t v_i_boxed_4341_; size_t v_stop_boxed_4342_; lean_object* v_res_4343_; 
v_i_boxed_4341_ = lean_unbox_usize(v_i_4338_);
lean_dec(v_i_4338_);
v_stop_boxed_4342_ = lean_unbox_usize(v_stop_4339_);
lean_dec(v_stop_4339_);
v_res_4343_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4337_, v_i_boxed_4341_, v_stop_boxed_4342_, v_b_4340_);
lean_dec_ref(v_as_4337_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4344_){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; 
v___x_4345_ = lean_unsigned_to_nat(0u);
v___x_4346_ = lean_array_get_size(v_perm_4344_);
v___x_4347_ = lean_nat_dec_lt(v___x_4345_, v___x_4346_);
if (v___x_4347_ == 0)
{
return v___x_4345_;
}
else
{
size_t v___x_4348_; size_t v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = lean_usize_of_nat(v___x_4346_);
v___x_4349_ = ((size_t)0ULL);
v___x_4350_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4344_, v___x_4348_, v___x_4349_, v___x_4345_);
return v___x_4350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4351_);
lean_dec_ref(v_perm_4351_);
return v_res_4352_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4353_, lean_object* v_i_4354_){
_start:
{
lean_object* v___x_4355_; uint8_t v___x_4356_; 
v___x_4355_ = lean_array_get_size(v_perm_4353_);
v___x_4356_ = lean_nat_dec_lt(v_i_4354_, v___x_4355_);
if (v___x_4356_ == 0)
{
return v___x_4356_;
}
else
{
lean_object* v___x_4357_; 
v___x_4357_ = lean_array_fget_borrowed(v_perm_4353_, v_i_4354_);
if (lean_obj_tag(v___x_4357_) == 0)
{
uint8_t v___x_4358_; 
v___x_4358_ = 0;
return v___x_4358_;
}
else
{
return v___x_4356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4359_, lean_object* v_i_4360_){
_start:
{
uint8_t v_res_4361_; lean_object* v_r_4362_; 
v_res_4361_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4359_, v_i_4360_);
lean_dec(v_i_4360_);
lean_dec_ref(v_perm_4359_);
v_r_4362_ = lean_box(v_res_4361_);
return v_r_4362_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v___f_4369_; lean_object* v___x_757__overap_4370_; lean_object* v___x_4371_; 
v___f_4369_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_757__overap_4370_ = lean_panic_fn_borrowed(v___f_4369_, v_msg_4363_);
lean_inc(v___y_4367_);
lean_inc_ref(v___y_4366_);
lean_inc(v___y_4365_);
lean_inc_ref(v___y_4364_);
v___x_4371_ = lean_apply_5(v___x_757__overap_4370_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, lean_box(0));
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4379_, lean_object* v_msg_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4387_, lean_object* v_msg_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4387_, v_msg_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4395_, lean_object* v_maxFVars_x3f_4396_, lean_object* v_k_4397_, uint8_t v_cleanupAnnotations_4398_, uint8_t v_whnfType_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v___f_4405_; lean_object* v___x_4406_; 
v___f_4405_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4405_, 0, v_k_4397_);
v___x_4406_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4395_, v_maxFVars_x3f_4396_, v___f_4405_, v_cleanupAnnotations_4398_, v_whnfType_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4406_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4406_);
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
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
v_a_4415_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4406_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4406_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4423_, lean_object* v_maxFVars_x3f_4424_, lean_object* v_k_4425_, lean_object* v_cleanupAnnotations_4426_, lean_object* v_whnfType_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4433_; uint8_t v_whnfType_boxed_4434_; lean_object* v_res_4435_; 
v_cleanupAnnotations_boxed_4433_ = lean_unbox(v_cleanupAnnotations_4426_);
v_whnfType_boxed_4434_ = lean_unbox(v_whnfType_4427_);
v_res_4435_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4423_, v_maxFVars_x3f_4424_, v_k_4425_, v_cleanupAnnotations_boxed_4433_, v_whnfType_boxed_4434_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4436_, lean_object* v_type_4437_, lean_object* v_maxFVars_x3f_4438_, lean_object* v_k_4439_, uint8_t v_cleanupAnnotations_4440_, uint8_t v_whnfType_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4437_, v_maxFVars_x3f_4438_, v_k_4439_, v_cleanupAnnotations_4440_, v_whnfType_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4448_, lean_object* v_type_4449_, lean_object* v_maxFVars_x3f_4450_, lean_object* v_k_4451_, lean_object* v_cleanupAnnotations_4452_, lean_object* v_whnfType_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4459_; uint8_t v_whnfType_boxed_4460_; lean_object* v_res_4461_; 
v_cleanupAnnotations_boxed_4459_ = lean_unbox(v_cleanupAnnotations_4452_);
v_whnfType_boxed_4460_ = lean_unbox(v_whnfType_4453_);
v_res_4461_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4448_, v_type_4449_, v_maxFVars_x3f_4450_, v_k_4451_, v_cleanupAnnotations_boxed_4459_, v_whnfType_boxed_4460_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
return v_res_4461_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4464_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4465_ = lean_unsigned_to_nat(6u);
v___x_4466_ = lean_unsigned_to_nat(329u);
v___x_4467_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4468_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4469_ = l_mkPanicMessageWithDecl(v___x_4468_, v___x_4467_, v___x_4466_, v___x_4465_, v___x_4464_);
return v___x_4469_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4474_ = lean_unsigned_to_nat(8u);
v___x_4475_ = lean_unsigned_to_nat(322u);
v___x_4476_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4477_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4478_ = l_mkPanicMessageWithDecl(v___x_4477_, v___x_4476_, v___x_4475_, v___x_4474_, v___x_4473_);
return v___x_4478_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4480_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4481_ = lean_unsigned_to_nat(8u);
v___x_4482_ = lean_unsigned_to_nat(325u);
v___x_4483_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4484_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4485_ = l_mkPanicMessageWithDecl(v___x_4484_, v___x_4483_, v___x_4482_, v___x_4481_, v___x_4480_);
return v___x_4485_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4488_ = lean_unsigned_to_nat(8u);
v___x_4489_ = lean_unsigned_to_nat(324u);
v___x_4490_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4491_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4492_ = l_mkPanicMessageWithDecl(v___x_4491_, v___x_4490_, v___x_4489_, v___x_4488_, v___x_4487_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4493_, lean_object* v___x_4494_, lean_object* v_xs_4495_, lean_object* v_val_4496_, lean_object* v_i_4497_, lean_object* v_perm_4498_, lean_object* v_k_4499_, lean_object* v_xs_x27_4500_, lean_object* v_type_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4507_ = lean_array_get_size(v_xs_x27_4500_);
v___x_4508_ = lean_nat_dec_eq(v___x_4507_, v___x_4493_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_dec_ref(v_type_4501_);
lean_dec_ref(v_k_4499_);
lean_dec_ref(v_perm_4498_);
lean_dec_ref(v_xs_4495_);
v___x_4509_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4510_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4509_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v___x_4510_;
}
else
{
lean_object* v___x_4511_; lean_object* v_x_4512_; lean_object* v___x_4513_; 
v___x_4511_ = lean_unsigned_to_nat(0u);
v_x_4512_ = lean_array_get_borrowed(v___x_4494_, v_xs_x27_4500_, v___x_4511_);
lean_inc(v___y_4505_);
lean_inc_ref(v___y_4504_);
lean_inc(v___y_4503_);
lean_inc_ref(v___y_4502_);
lean_inc(v_x_4512_);
v___x_4513_ = lean_infer_type(v_x_4512_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; uint8_t v___x_4515_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4513_, 1);
v___x_4515_ = l_Lean_Expr_hasLooseBVars(v_a_4514_);
lean_dec(v_a_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; uint8_t v___x_4517_; 
v___x_4516_ = lean_array_get_size(v_xs_4495_);
v___x_4517_ = lean_nat_dec_lt(v_val_4496_, v___x_4516_);
if (v___x_4517_ == 0)
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_dec_ref(v_type_4501_);
lean_dec_ref(v_k_4499_);
lean_dec_ref(v_perm_4498_);
lean_dec_ref(v_xs_4495_);
v___x_4518_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4519_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4518_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v___x_4519_;
}
else
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4520_ = lean_nat_add(v_i_4497_, v___x_4493_);
lean_inc(v_x_4512_);
v___x_4521_ = lean_array_set(v_xs_4495_, v_val_4496_, v_x_4512_);
v___x_4522_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4498_, v_k_4499_, v___x_4520_, v_type_4501_, v___x_4521_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v___x_4522_;
}
}
else
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
lean_dec_ref(v_type_4501_);
lean_dec_ref(v_k_4499_);
lean_dec_ref(v_perm_4498_);
lean_dec_ref(v_xs_4495_);
v___x_4523_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4524_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4523_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
return v___x_4524_;
}
}
else
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
lean_dec_ref(v_type_4501_);
lean_dec_ref(v_k_4499_);
lean_dec_ref(v_perm_4498_);
lean_dec_ref(v_xs_4495_);
v_a_4525_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4527_ = v___x_4513_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4513_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4533_, lean_object* v___x_4534_, lean_object* v_xs_4535_, lean_object* v_val_4536_, lean_object* v_i_4537_, lean_object* v_perm_4538_, lean_object* v_k_4539_, lean_object* v_xs_x27_4540_, lean_object* v_type_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4533_, v___x_4534_, v_xs_4535_, v_val_4536_, v_i_4537_, v_perm_4538_, v_k_4539_, v_xs_x27_4540_, v_type_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec_ref(v_xs_x27_4540_);
lean_dec(v_i_4537_);
lean_dec(v_val_4536_);
lean_dec_ref(v___x_4534_);
lean_dec(v___x_4533_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4548_, lean_object* v_k_4549_, lean_object* v_i_4550_, lean_object* v_type_4551_, lean_object* v_xs_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_){
_start:
{
lean_object* v___x_4558_; uint8_t v___x_4559_; 
v___x_4558_ = lean_array_get_size(v_perm_4548_);
v___x_4559_ = lean_nat_dec_lt(v_i_4550_, v___x_4558_);
if (v___x_4559_ == 0)
{
lean_object* v___x_4560_; 
lean_dec_ref(v_type_4551_);
lean_dec(v_i_4550_);
lean_dec_ref(v_perm_4548_);
lean_inc(v_a_4556_);
lean_inc_ref(v_a_4555_);
lean_inc(v_a_4554_);
lean_inc_ref(v_a_4553_);
v___x_4560_ = lean_apply_6(v_k_4549_, v_xs_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, lean_box(0));
return v___x_4560_;
}
else
{
lean_object* v___x_4561_; 
v___x_4561_ = lean_array_fget_borrowed(v_perm_4548_, v_i_4550_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v___x_4562_; 
lean_inc(v_a_4556_);
lean_inc_ref(v_a_4555_);
lean_inc(v_a_4554_);
lean_inc_ref(v_a_4553_);
v___x_4562_ = lean_whnf(v_type_4551_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; uint8_t v___x_4564_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref_known(v___x_4562_, 1);
v___x_4564_ = l_Lean_Expr_isForall(v_a_4563_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
lean_dec(v_a_4563_);
lean_dec_ref(v_xs_4552_);
lean_dec(v_i_4550_);
lean_dec_ref(v_k_4549_);
lean_dec_ref(v_perm_4548_);
v___x_4565_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4566_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4565_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___x_4567_ = lean_unsigned_to_nat(1u);
v___x_4568_ = lean_nat_add(v_i_4550_, v___x_4567_);
lean_dec(v_i_4550_);
v___x_4569_ = l_Lean_Expr_bindingBody_x21(v_a_4563_);
lean_dec(v_a_4563_);
v_i_4550_ = v___x_4568_;
v_type_4551_ = v___x_4569_;
goto _start;
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v_xs_4552_);
lean_dec(v_i_4550_);
lean_dec_ref(v_k_4549_);
lean_dec_ref(v_perm_4548_);
v_a_4571_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4562_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4562_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
else
{
lean_object* v_val_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___f_4582_; lean_object* v___x_4583_; uint8_t v___x_4584_; lean_object* v___x_4585_; 
v_val_4579_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_val_4579_);
v___x_4580_ = l_Lean_instInhabitedExpr;
v___x_4581_ = lean_unsigned_to_nat(1u);
v___f_4582_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4582_, 0, v___x_4581_);
lean_closure_set(v___f_4582_, 1, v___x_4580_);
lean_closure_set(v___f_4582_, 2, v_xs_4552_);
lean_closure_set(v___f_4582_, 3, v_val_4579_);
lean_closure_set(v___f_4582_, 4, v_i_4550_);
lean_closure_set(v___f_4582_, 5, v_perm_4548_);
lean_closure_set(v___f_4582_, 6, v_k_4549_);
v___x_4583_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4584_ = 0;
v___x_4585_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4551_, v___x_4583_, v___f_4582_, v___x_4559_, v___x_4584_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
return v___x_4585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4586_, lean_object* v_k_4587_, lean_object* v_i_4588_, lean_object* v_type_4589_, lean_object* v_xs_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4586_, v_k_4587_, v_i_4588_, v_type_4589_, v_xs_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4597_, lean_object* v_perm_4598_, lean_object* v_k_4599_, lean_object* v_i_4600_, lean_object* v_type_4601_, lean_object* v_xs_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4598_, v_k_4599_, v_i_4600_, v_type_4601_, v_xs_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4609_, lean_object* v_perm_4610_, lean_object* v_k_4611_, lean_object* v_i_4612_, lean_object* v_type_4613_, lean_object* v_xs_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4609_, v_perm_4610_, v_k_4611_, v_i_4612_, v_type_4613_, v_xs_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4617_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
return v_res_4620_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = lean_unsigned_to_nat(0u);
v___x_4622_ = l_Lean_Level_ofNat(v___x_4621_);
return v___x_4622_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4624_ = l_Lean_mkSort(v___x_4623_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4625_, lean_object* v_type_4626_, lean_object* v_k_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4633_ = lean_unsigned_to_nat(0u);
v___x_4634_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4625_);
v___x_4635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4636_ = lean_mk_array(v___x_4634_, v___x_4635_);
v___x_4637_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4625_, v_k_4627_, v___x_4633_, v_type_4626_, v___x_4636_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4638_, lean_object* v_type_4639_, lean_object* v_k_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4638_, v_type_4639_, v_k_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4647_, lean_object* v_perm_4648_, lean_object* v_type_4649_, lean_object* v_k_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4648_, v_type_4649_, v_k_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4657_, lean_object* v_perm_4658_, lean_object* v_type_4659_, lean_object* v_k_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4657_, v_perm_4658_, v_type_4659_, v_k_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4667_, lean_object* v_runInBase_4668_, lean_object* v_b_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = lean_apply_1(v_k_4667_, v_b_4669_);
lean_inc(v___y_4673_);
lean_inc_ref(v___y_4672_);
lean_inc(v___y_4671_);
lean_inc_ref(v___y_4670_);
v___x_4676_ = lean_apply_7(v_runInBase_4668_, lean_box(0), v___x_4675_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, lean_box(0));
return v___x_4676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4677_, lean_object* v_runInBase_4678_, lean_object* v_b_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v_res_4685_; 
v_res_4685_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4677_, v_runInBase_4678_, v_b_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4686_, lean_object* v_perm_4687_, lean_object* v_type_4688_, lean_object* v_runInBase_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
lean_object* v___f_4695_; lean_object* v___x_4696_; 
v___f_4695_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4695_, 0, v_k_4686_);
lean_closure_set(v___f_4695_, 1, v_runInBase_4689_);
v___x_4696_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4687_, v_type_4688_, v___f_4695_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4697_, lean_object* v_perm_4698_, lean_object* v_type_4699_, lean_object* v_runInBase_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4697_, v_perm_4698_, v_type_4699_, v_runInBase_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4707_, lean_object* v_inst_4708_, lean_object* v_perm_4709_, lean_object* v_type_4710_, lean_object* v_k_4711_){
_start:
{
lean_object* v_toBind_4712_; lean_object* v_liftWith_4713_; lean_object* v_restoreM_4714_; lean_object* v___f_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v_toBind_4712_ = lean_ctor_get(v_inst_4708_, 1);
lean_inc(v_toBind_4712_);
lean_dec_ref(v_inst_4708_);
v_liftWith_4713_ = lean_ctor_get(v_inst_4707_, 0);
lean_inc(v_liftWith_4713_);
v_restoreM_4714_ = lean_ctor_get(v_inst_4707_, 1);
lean_inc(v_restoreM_4714_);
lean_dec_ref(v_inst_4707_);
v___f_4715_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4715_, 0, v_k_4711_);
lean_closure_set(v___f_4715_, 1, v_perm_4709_);
lean_closure_set(v___f_4715_, 2, v_type_4710_);
v___x_4716_ = lean_apply_2(v_liftWith_4713_, lean_box(0), v___f_4715_);
v___x_4717_ = lean_apply_1(v_restoreM_4714_, lean_box(0));
v___x_4718_ = lean_apply_4(v_toBind_4712_, lean_box(0), lean_box(0), v___x_4716_, v___x_4717_);
return v___x_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4719_, lean_object* v_00_u03b1_4720_, lean_object* v_inst_4721_, lean_object* v_inst_4722_, lean_object* v_perm_4723_, lean_object* v_type_4724_, lean_object* v_k_4725_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4721_, v_inst_4722_, v_perm_4723_, v_type_4724_, v_k_4725_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v___f_4733_; lean_object* v___x_512__overap_4734_; lean_object* v___x_4735_; 
v___f_4733_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_512__overap_4734_ = lean_panic_fn_borrowed(v___f_4733_, v_msg_4727_);
lean_inc(v___y_4731_);
lean_inc_ref(v___y_4730_);
lean_inc(v___y_4729_);
lean_inc_ref(v___y_4728_);
v___x_4735_ = lean_apply_5(v___x_512__overap_4734_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, lean_box(0));
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
return v_res_4742_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4745_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4746_ = lean_unsigned_to_nat(10u);
v___x_4747_ = lean_unsigned_to_nat(353u);
v___x_4748_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4749_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4750_ = l_mkPanicMessageWithDecl(v___x_4749_, v___x_4748_, v___x_4747_, v___x_4746_, v___x_4745_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4751_, lean_object* v_xs_4752_, lean_object* v_tail_4753_, lean_object* v_ys_4754_, lean_object* v_type_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4751_, v_xs_4752_, v_tail_4753_, v_ys_4754_, v_type_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec_ref(v_ys_4754_);
lean_dec(v___x_4751_);
return v_res_4761_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4762_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4763_ = lean_unsigned_to_nat(8u);
v___x_4764_ = lean_unsigned_to_nat(349u);
v___x_4765_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4766_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4767_ = l_mkPanicMessageWithDecl(v___x_4766_, v___x_4765_, v___x_4764_, v___x_4763_, v___x_4762_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4768_, lean_object* v_x_4769_, lean_object* v_x_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_){
_start:
{
if (lean_obj_tag(v_x_4769_) == 0)
{
lean_object* v___x_4776_; 
lean_dec_ref(v_xs_4768_);
v___x_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4776_, 0, v_x_4770_);
return v___x_4776_;
}
else
{
lean_object* v_head_4777_; 
v_head_4777_ = lean_ctor_get(v_x_4769_, 0);
if (lean_obj_tag(v_head_4777_) == 0)
{
lean_object* v_tail_4778_; lean_object* v___x_4779_; lean_object* v___f_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; 
v_tail_4778_ = lean_ctor_get(v_x_4769_, 1);
lean_inc(v_tail_4778_);
lean_dec_ref_known(v_x_4769_, 2);
v___x_4779_ = lean_unsigned_to_nat(1u);
v___f_4780_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4780_, 0, v___x_4779_);
lean_closure_set(v___f_4780_, 1, v_xs_4768_);
lean_closure_set(v___f_4780_, 2, v_tail_4778_);
v___x_4781_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4782_ = 0;
v___x_4783_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4770_, v___x_4781_, v___f_4780_, v___x_4782_, v___x_4782_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
return v___x_4783_;
}
else
{
lean_object* v_tail_4784_; lean_object* v_val_4785_; lean_object* v___x_4786_; uint8_t v___x_4787_; 
lean_inc_ref(v_head_4777_);
v_tail_4784_ = lean_ctor_get(v_x_4769_, 1);
lean_inc(v_tail_4784_);
lean_dec_ref_known(v_x_4769_, 2);
v_val_4785_ = lean_ctor_get(v_head_4777_, 0);
lean_inc(v_val_4785_);
lean_dec_ref_known(v_head_4777_, 1);
v___x_4786_ = lean_array_get_size(v_xs_4768_);
v___x_4787_ = lean_nat_dec_lt(v_val_4785_, v___x_4786_);
if (v___x_4787_ == 0)
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
lean_dec(v_val_4785_);
lean_dec(v_tail_4784_);
lean_dec_ref(v_x_4770_);
lean_dec_ref(v_xs_4768_);
v___x_4788_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4789_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4788_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
return v___x_4789_;
}
else
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4790_ = l_Lean_instInhabitedExpr;
v___x_4791_ = lean_array_get_borrowed(v___x_4790_, v_xs_4768_, v_val_4785_);
lean_dec(v_val_4785_);
v___x_4792_ = lean_unsigned_to_nat(1u);
v___x_4793_ = lean_mk_empty_array_with_capacity(v___x_4792_);
lean_inc(v___x_4791_);
v___x_4794_ = lean_array_push(v___x_4793_, v___x_4791_);
v___x_4795_ = l_Lean_Meta_instantiateForall(v_x_4770_, v___x_4794_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_);
lean_dec_ref(v___x_4794_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref_known(v___x_4795_, 1);
v_x_4769_ = v_tail_4784_;
v_x_4770_ = v_a_4796_;
goto _start;
}
else
{
lean_dec(v_tail_4784_);
lean_dec_ref(v_xs_4768_);
return v___x_4795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4798_, lean_object* v_xs_4799_, lean_object* v_tail_4800_, lean_object* v_ys_4801_, lean_object* v_type_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
lean_object* v___x_4808_; uint8_t v___x_4809_; 
v___x_4808_ = lean_array_get_size(v_ys_4801_);
v___x_4809_ = lean_nat_dec_eq(v___x_4808_, v___x_4798_);
if (v___x_4809_ == 0)
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
lean_dec_ref(v_type_4802_);
lean_dec(v_tail_4800_);
lean_dec_ref(v_xs_4799_);
v___x_4810_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4811_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4810_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
return v___x_4811_;
}
else
{
lean_object* v___x_4812_; 
v___x_4812_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4799_, v_tail_4800_, v_type_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; uint8_t v___x_4814_; uint8_t v___x_4815_; lean_object* v___x_4816_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
lean_inc(v_a_4813_);
lean_dec_ref_known(v___x_4812_, 1);
v___x_4814_ = 0;
v___x_4815_ = 1;
v___x_4816_ = l_Lean_Meta_mkForallFVars(v_ys_4801_, v_a_4813_, v___x_4814_, v___x_4809_, v___x_4809_, v___x_4815_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
return v___x_4816_;
}
else
{
return v___x_4812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4817_, lean_object* v_x_4818_, lean_object* v_x_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4817_, v_x_4818_, v_x_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_);
lean_dec(v_a_4823_);
lean_dec_ref(v_a_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_a_4820_);
return v_res_4825_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4828_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4829_ = lean_unsigned_to_nat(2u);
v___x_4830_ = lean_unsigned_to_nat(343u);
v___x_4831_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4832_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4833_ = l_mkPanicMessageWithDecl(v___x_4832_, v___x_4831_, v___x_4830_, v___x_4829_, v___x_4828_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4834_, lean_object* v_type_u2080_4835_, lean_object* v_xs_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; uint8_t v___x_4844_; 
v___x_4842_ = lean_array_get_size(v_xs_4836_);
v___x_4843_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4834_);
v___x_4844_ = lean_nat_dec_eq(v___x_4842_, v___x_4843_);
lean_dec(v___x_4843_);
if (v___x_4844_ == 0)
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
lean_dec_ref(v_xs_4836_);
lean_dec_ref(v_type_u2080_4835_);
lean_dec_ref(v_perm_4834_);
v___x_4845_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4846_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4845_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
return v___x_4846_;
}
else
{
lean_object* v_mask_4847_; lean_object* v___x_4848_; 
v_mask_4847_ = lean_array_to_list(v_perm_4834_);
v___x_4848_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4836_, v_mask_4847_, v_type_u2080_4835_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_);
return v___x_4848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4849_, lean_object* v_type_u2080_4850_, lean_object* v_xs_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4849_, v_type_u2080_4850_, v_xs_4851_, v_a_4852_, v_a_4853_, v_a_4854_, v_a_4855_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec(v_a_4853_);
lean_dec_ref(v_a_4852_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4858_, lean_object* v_maxFVars_4859_, lean_object* v_k_4860_, uint8_t v_cleanupAnnotations_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v___f_4867_; uint8_t v___x_4868_; uint8_t v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___f_4867_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4867_, 0, v_k_4860_);
v___x_4868_ = 1;
v___x_4869_ = 0;
v___x_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4870_, 0, v_maxFVars_4859_);
v___x_4871_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4858_, v___x_4868_, v___x_4869_, v___x_4868_, v___x_4869_, v___x_4870_, v___f_4867_, v_cleanupAnnotations_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
lean_dec_ref_known(v___x_4870_, 1);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4871_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4871_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
else
{
lean_object* v_a_4880_; lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4887_; 
v_a_4880_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4887_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4887_ == 0)
{
v___x_4882_ = v___x_4871_;
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
else
{
lean_inc(v_a_4880_);
lean_dec(v___x_4871_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4887_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4885_; 
if (v_isShared_4883_ == 0)
{
v___x_4885_ = v___x_4882_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4888_, lean_object* v_maxFVars_4889_, lean_object* v_k_4890_, lean_object* v_cleanupAnnotations_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4897_; lean_object* v_res_4898_; 
v_cleanupAnnotations_boxed_4897_ = lean_unbox(v_cleanupAnnotations_4891_);
v_res_4898_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4888_, v_maxFVars_4889_, v_k_4890_, v_cleanupAnnotations_boxed_4897_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4899_, lean_object* v_e_4900_, lean_object* v_maxFVars_4901_, lean_object* v_k_4902_, uint8_t v_cleanupAnnotations_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v___x_4909_; 
v___x_4909_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4900_, v_maxFVars_4901_, v_k_4902_, v_cleanupAnnotations_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4910_, lean_object* v_e_4911_, lean_object* v_maxFVars_4912_, lean_object* v_k_4913_, lean_object* v_cleanupAnnotations_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4920_; lean_object* v_res_4921_; 
v_cleanupAnnotations_boxed_4920_ = lean_unbox(v_cleanupAnnotations_4914_);
v_res_4921_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4910_, v_e_4911_, v_maxFVars_4912_, v_k_4913_, v_cleanupAnnotations_boxed_4920_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
lean_dec(v___y_4916_);
lean_dec_ref(v___y_4915_);
return v_res_4921_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4922_){
_start:
{
if (lean_obj_tag(v_x_4922_) == 0)
{
uint8_t v___x_4923_; 
v___x_4923_ = 1;
return v___x_4923_;
}
else
{
lean_object* v_head_4924_; 
v_head_4924_ = lean_ctor_get(v_x_4922_, 0);
if (lean_obj_tag(v_head_4924_) == 0)
{
lean_object* v_tail_4925_; 
v_tail_4925_ = lean_ctor_get(v_x_4922_, 1);
v_x_4922_ = v_tail_4925_;
goto _start;
}
else
{
uint8_t v___x_4927_; 
v___x_4927_ = 0;
return v___x_4927_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4928_){
_start:
{
uint8_t v_res_4929_; lean_object* v_r_4930_; 
v_res_4929_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4928_);
lean_dec(v_x_4928_);
v_r_4930_ = lean_box(v_res_4929_);
return v_r_4930_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4933_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4934_ = lean_unsigned_to_nat(12u);
v___x_4935_ = lean_unsigned_to_nat(376u);
v___x_4936_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4937_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4938_ = l_mkPanicMessageWithDecl(v___x_4937_, v___x_4936_, v___x_4935_, v___x_4934_, v___x_4933_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4939_, lean_object* v_xs_4940_, lean_object* v_tail_4941_, lean_object* v___x_4942_, lean_object* v___x_4943_, lean_object* v_ys_4944_, lean_object* v_value_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
uint8_t v___x_1127__boxed_4951_; uint8_t v___x_1128__boxed_4952_; lean_object* v_res_4953_; 
v___x_1127__boxed_4951_ = lean_unbox(v___x_4942_);
v___x_1128__boxed_4952_ = lean_unbox(v___x_4943_);
v_res_4953_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4939_, v_xs_4940_, v_tail_4941_, v___x_1127__boxed_4951_, v___x_1128__boxed_4952_, v_ys_4944_, v_value_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec(v___y_4947_);
lean_dec_ref(v___y_4946_);
lean_dec_ref(v_ys_4944_);
lean_dec(v___x_4939_);
return v_res_4953_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4954_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4955_ = lean_unsigned_to_nat(8u);
v___x_4956_ = lean_unsigned_to_nat(368u);
v___x_4957_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4959_ = l_mkPanicMessageWithDecl(v___x_4958_, v___x_4957_, v___x_4956_, v___x_4955_, v___x_4954_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4960_, lean_object* v_x_4961_, lean_object* v_x_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_){
_start:
{
if (lean_obj_tag(v_x_4961_) == 0)
{
lean_object* v___x_4968_; 
lean_dec_ref(v_xs_4960_);
v___x_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_x_4962_);
return v___x_4968_;
}
else
{
lean_object* v_head_4969_; 
v_head_4969_ = lean_ctor_get(v_x_4961_, 0);
if (lean_obj_tag(v_head_4969_) == 0)
{
lean_object* v_tail_4970_; uint8_t v___x_4971_; 
v_tail_4970_ = lean_ctor_get(v_x_4961_, 1);
lean_inc(v_tail_4970_);
lean_dec_ref_known(v_x_4961_, 2);
v___x_4971_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4970_);
if (v___x_4971_ == 0)
{
uint8_t v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___f_4976_; lean_object* v___x_4977_; 
v___x_4972_ = 1;
v___x_4973_ = lean_unsigned_to_nat(1u);
v___x_4974_ = lean_box(v___x_4971_);
v___x_4975_ = lean_box(v___x_4972_);
v___f_4976_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4976_, 0, v___x_4973_);
lean_closure_set(v___f_4976_, 1, v_xs_4960_);
lean_closure_set(v___f_4976_, 2, v_tail_4970_);
lean_closure_set(v___f_4976_, 3, v___x_4974_);
lean_closure_set(v___f_4976_, 4, v___x_4975_);
v___x_4977_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4962_, v___x_4973_, v___f_4976_, v___x_4971_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
return v___x_4977_;
}
else
{
lean_object* v___x_4978_; 
lean_dec(v_tail_4970_);
lean_dec_ref(v_xs_4960_);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v_x_4962_);
return v___x_4978_;
}
}
else
{
lean_object* v_tail_4979_; lean_object* v_val_4980_; lean_object* v___x_4981_; uint8_t v___x_4982_; 
lean_inc_ref(v_head_4969_);
v_tail_4979_ = lean_ctor_get(v_x_4961_, 1);
lean_inc(v_tail_4979_);
lean_dec_ref_known(v_x_4961_, 2);
v_val_4980_ = lean_ctor_get(v_head_4969_, 0);
lean_inc(v_val_4980_);
lean_dec_ref_known(v_head_4969_, 1);
v___x_4981_ = lean_array_get_size(v_xs_4960_);
v___x_4982_ = lean_nat_dec_lt(v_val_4980_, v___x_4981_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
lean_dec(v_val_4980_);
lean_dec(v_tail_4979_);
lean_dec_ref(v_x_4962_);
lean_dec_ref(v_xs_4960_);
v___x_4983_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4984_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4983_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
return v___x_4984_;
}
else
{
lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4985_ = l_Lean_instInhabitedExpr;
v___x_4986_ = lean_array_get_borrowed(v___x_4985_, v_xs_4960_, v_val_4980_);
lean_dec(v_val_4980_);
v___x_4987_ = lean_unsigned_to_nat(1u);
v___x_4988_ = lean_mk_empty_array_with_capacity(v___x_4987_);
lean_inc(v___x_4986_);
v___x_4989_ = lean_array_push(v___x_4988_, v___x_4986_);
v___x_4990_ = l_Lean_Meta_instantiateLambda(v_x_4962_, v___x_4989_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_);
lean_dec_ref(v___x_4989_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref_known(v___x_4990_, 1);
v_x_4961_ = v_tail_4979_;
v_x_4962_ = v_a_4991_;
goto _start;
}
else
{
lean_dec(v_tail_4979_);
lean_dec_ref(v_xs_4960_);
return v___x_4990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4993_, lean_object* v_xs_4994_, lean_object* v_tail_4995_, uint8_t v___x_4996_, uint8_t v___x_4997_, lean_object* v_ys_4998_, lean_object* v_value_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
lean_object* v___x_5005_; uint8_t v___x_5006_; 
v___x_5005_ = lean_array_get_size(v_ys_4998_);
v___x_5006_ = lean_nat_dec_eq(v___x_5005_, v___x_4993_);
if (v___x_5006_ == 0)
{
lean_object* v___x_5007_; lean_object* v___x_5008_; 
lean_dec_ref(v_value_4999_);
lean_dec(v_tail_4995_);
lean_dec_ref(v_xs_4994_);
v___x_5007_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_5008_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5007_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
return v___x_5008_;
}
else
{
lean_object* v___x_5009_; 
v___x_5009_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4994_, v_tail_4995_, v_value_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; uint8_t v___x_5011_; lean_object* v___x_5012_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
lean_inc(v_a_5010_);
lean_dec_ref_known(v___x_5009_, 1);
v___x_5011_ = 1;
v___x_5012_ = l_Lean_Meta_mkLambdaFVars(v_ys_4998_, v_a_5010_, v___x_4996_, v___x_4997_, v___x_4996_, v___x_4997_, v___x_5011_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
return v___x_5012_;
}
else
{
return v___x_5009_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_5013_, lean_object* v_x_5014_, lean_object* v_x_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5013_, v_x_5014_, v_x_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_);
lean_dec(v_a_5019_);
lean_dec_ref(v_a_5018_);
lean_dec(v_a_5017_);
lean_dec_ref(v_a_5016_);
return v_res_5021_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5023_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_5024_ = lean_unsigned_to_nat(2u);
v___x_5025_ = lean_unsigned_to_nat(362u);
v___x_5026_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_5027_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5028_ = l_mkPanicMessageWithDecl(v___x_5027_, v___x_5026_, v___x_5025_, v___x_5024_, v___x_5023_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_5029_, lean_object* v_value_u2080_5030_, lean_object* v_xs_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
v___x_5037_ = lean_array_get_size(v_xs_5031_);
v___x_5038_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5029_);
v___x_5039_ = lean_nat_dec_eq(v___x_5037_, v___x_5038_);
lean_dec(v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
lean_dec_ref(v_xs_5031_);
lean_dec_ref(v_value_u2080_5030_);
lean_dec_ref(v_perm_5029_);
v___x_5040_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_5041_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_5040_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
return v___x_5041_;
}
else
{
lean_object* v_mask_5042_; lean_object* v___x_5043_; 
v_mask_5042_ = lean_array_to_list(v_perm_5029_);
v___x_5043_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_5031_, v_mask_5042_, v_value_u2080_5030_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
return v___x_5043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_5044_, lean_object* v_value_u2080_5045_, lean_object* v_xs_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_5044_, v_value_u2080_5045_, v_xs_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
lean_dec(v_a_5050_);
lean_dec_ref(v_a_5049_);
lean_dec(v_a_5048_);
lean_dec_ref(v_a_5047_);
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5060_){
_start:
{
lean_object* v___f_5061_; lean_object* v___f_5062_; lean_object* v___f_5063_; lean_object* v___f_5064_; lean_object* v___f_5065_; lean_object* v___f_5066_; lean_object* v___f_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___f_5061_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5062_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5063_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5064_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5065_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5066_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5067_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5068_, 0, v___f_5061_);
lean_ctor_set(v___x_5068_, 1, v___f_5062_);
v___x_5069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5068_);
lean_ctor_set(v___x_5069_, 1, v___f_5063_);
lean_ctor_set(v___x_5069_, 2, v___f_5064_);
lean_ctor_set(v___x_5069_, 3, v___f_5065_);
lean_ctor_set(v___x_5069_, 4, v___f_5066_);
v___x_5070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5069_);
lean_ctor_set(v___x_5070_, 1, v___f_5067_);
v___x_5071_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5072_ = l_instInhabitedOfMonad___redArg(v___x_5070_, v___x_5071_);
v___x_5073_ = lean_panic_fn_borrowed(v___x_5072_, v_msg_5060_);
lean_dec(v___x_5072_);
return v___x_5073_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5074_, lean_object* v_msg_5075_){
_start:
{
lean_object* v___x_5076_; 
v___x_5076_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5075_);
return v___x_5076_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5079_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5080_ = lean_unsigned_to_nat(8u);
v___x_5081_ = lean_unsigned_to_nat(394u);
v___x_5082_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5083_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5084_ = l_mkPanicMessageWithDecl(v___x_5083_, v___x_5082_, v___x_5081_, v___x_5080_, v___x_5079_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5085_, lean_object* v_x_5086_){
_start:
{
if (lean_obj_tag(v_x_5085_) == 0)
{
return v_x_5086_;
}
else
{
lean_object* v_head_5087_; lean_object* v_fst_5088_; 
v_head_5087_ = lean_ctor_get(v_x_5085_, 0);
v_fst_5088_ = lean_ctor_get(v_head_5087_, 0);
if (lean_obj_tag(v_fst_5088_) == 0)
{
lean_object* v_tail_5089_; 
v_tail_5089_ = lean_ctor_get(v_x_5085_, 1);
lean_inc(v_tail_5089_);
lean_dec_ref_known(v_x_5085_, 2);
v_x_5085_ = v_tail_5089_;
goto _start;
}
else
{
lean_object* v_tail_5091_; lean_object* v_snd_5092_; lean_object* v_val_5093_; lean_object* v___x_5094_; uint8_t v___x_5095_; 
lean_inc_ref(v_fst_5088_);
lean_inc(v_head_5087_);
v_tail_5091_ = lean_ctor_get(v_x_5085_, 1);
lean_inc(v_tail_5091_);
lean_dec_ref_known(v_x_5085_, 2);
v_snd_5092_ = lean_ctor_get(v_head_5087_, 1);
lean_inc(v_snd_5092_);
lean_dec(v_head_5087_);
v_val_5093_ = lean_ctor_get(v_fst_5088_, 0);
lean_inc(v_val_5093_);
lean_dec_ref_known(v_fst_5088_, 1);
v___x_5094_ = lean_array_get_size(v_x_5086_);
v___x_5095_ = lean_nat_dec_lt(v_val_5093_, v___x_5094_);
if (v___x_5095_ == 0)
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
lean_dec(v_val_5093_);
lean_dec(v_snd_5092_);
lean_dec(v_tail_5091_);
lean_dec_ref(v_x_5086_);
v___x_5096_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5097_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5096_);
return v___x_5097_;
}
else
{
lean_object* v___x_5098_; 
v___x_5098_ = lean_array_set(v_x_5086_, v_val_5093_, v_snd_5092_);
lean_dec(v_val_5093_);
v_x_5085_ = v_tail_5091_;
v_x_5086_ = v___x_5098_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5100_, lean_object* v_x_5101_, lean_object* v_x_5102_){
_start:
{
lean_object* v___x_5103_; 
v___x_5103_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5101_, v_x_5102_);
return v___x_5103_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5106_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5107_ = lean_unsigned_to_nat(2u);
v___x_5108_ = lean_unsigned_to_nat(384u);
v___x_5109_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5110_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5111_ = l_mkPanicMessageWithDecl(v___x_5110_, v___x_5109_, v___x_5108_, v___x_5107_, v___x_5106_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5114_, lean_object* v_xs_5115_){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; uint8_t v___x_5118_; 
v___x_5116_ = lean_array_get_size(v_xs_5115_);
v___x_5117_ = lean_array_get_size(v_perm_5114_);
v___x_5118_ = lean_nat_dec_eq(v___x_5116_, v___x_5117_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5119_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5120_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5119_);
return v___x_5120_;
}
else
{
lean_object* v___x_5121_; uint8_t v___x_5122_; 
v___x_5121_ = lean_unsigned_to_nat(0u);
v___x_5122_ = lean_nat_dec_eq(v___x_5116_, v___x_5121_);
if (v___x_5122_ == 0)
{
lean_object* v_dummy_5123_; lean_object* v___x_5124_; lean_object* v_ys_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v_dummy_5123_ = lean_array_fget_borrowed(v_xs_5115_, v___x_5121_);
v___x_5124_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5114_);
lean_inc(v_dummy_5123_);
v_ys_5125_ = lean_mk_array(v___x_5124_, v_dummy_5123_);
v___x_5126_ = l_Array_zip___redArg(v_perm_5114_, v_xs_5115_);
v___x_5127_ = lean_array_to_list(v___x_5126_);
v___x_5128_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5127_, v_ys_5125_);
return v___x_5128_;
}
else
{
lean_object* v___x_5129_; 
v___x_5129_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5130_, lean_object* v_xs_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5130_, v_xs_5131_);
lean_dec_ref(v_xs_5131_);
lean_dec_ref(v_perm_5130_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5133_, lean_object* v_perm_5134_, lean_object* v_xs_5135_){
_start:
{
lean_object* v___x_5136_; 
v___x_5136_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5134_, v_xs_5135_);
return v___x_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5137_, lean_object* v_perm_5138_, lean_object* v_xs_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5137_, v_perm_5138_, v_xs_5139_);
lean_dec_ref(v_xs_5139_);
lean_dec_ref(v_perm_5138_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5141_, lean_object* v_upperBound_5142_, lean_object* v_perm_5143_, lean_object* v_a_5144_, lean_object* v_b_5145_){
_start:
{
lean_object* v_a_5147_; uint8_t v___x_5154_; 
v___x_5154_ = lean_nat_dec_lt(v_a_5144_, v_upperBound_5142_);
if (v___x_5154_ == 0)
{
lean_dec(v_a_5144_);
return v_b_5145_;
}
else
{
lean_object* v___x_5155_; uint8_t v___x_5156_; 
v___x_5155_ = lean_array_get_size(v_perm_5143_);
v___x_5156_ = lean_nat_dec_lt(v_a_5144_, v___x_5155_);
if (v___x_5156_ == 0)
{
goto v___jp_5151_;
}
else
{
lean_object* v___x_5157_; 
v___x_5157_ = lean_array_fget_borrowed(v_perm_5143_, v_a_5144_);
if (lean_obj_tag(v___x_5157_) == 0)
{
goto v___jp_5151_;
}
else
{
v_a_5147_ = v_b_5145_;
goto v___jp_5146_;
}
}
}
v___jp_5146_:
{
lean_object* v___x_5148_; lean_object* v___x_5149_; 
v___x_5148_ = lean_unsigned_to_nat(1u);
v___x_5149_ = lean_nat_add(v_a_5144_, v___x_5148_);
lean_dec(v_a_5144_);
v_a_5144_ = v___x_5149_;
v_b_5145_ = v_a_5147_;
goto _start;
}
v___jp_5151_:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5152_ = lean_array_fget_borrowed(v_xs_5141_, v_a_5144_);
lean_inc(v___x_5152_);
v___x_5153_ = lean_array_push(v_b_5145_, v___x_5152_);
v_a_5147_ = v___x_5153_;
goto v___jp_5146_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5158_, lean_object* v_upperBound_5159_, lean_object* v_perm_5160_, lean_object* v_a_5161_, lean_object* v_b_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5158_, v_upperBound_5159_, v_perm_5160_, v_a_5161_, v_b_5162_);
lean_dec_ref(v_perm_5160_);
lean_dec(v_upperBound_5159_);
lean_dec_ref(v_xs_5158_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5164_, lean_object* v_xs_5165_){
_start:
{
lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v_ys_5168_; lean_object* v___x_5169_; 
v___x_5166_ = lean_array_get_size(v_xs_5165_);
v___x_5167_ = lean_unsigned_to_nat(0u);
v_ys_5168_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5165_, v___x_5166_, v_perm_5164_, v___x_5167_, v_ys_5168_);
return v___x_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5170_, lean_object* v_xs_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5170_, v_xs_5171_);
lean_dec_ref(v_xs_5171_);
lean_dec_ref(v_perm_5170_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5173_, lean_object* v_perm_5174_, lean_object* v_xs_5175_){
_start:
{
lean_object* v___x_5176_; 
v___x_5176_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5174_, v_xs_5175_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5177_, lean_object* v_perm_5178_, lean_object* v_xs_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5177_, v_perm_5178_, v_xs_5179_);
lean_dec_ref(v_xs_5179_);
lean_dec_ref(v_perm_5178_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5181_, lean_object* v_xs_5182_, lean_object* v_upperBound_5183_, lean_object* v_perm_5184_, lean_object* v_inst_5185_, lean_object* v_R_5186_, lean_object* v_a_5187_, lean_object* v_b_5188_, lean_object* v_c_5189_){
_start:
{
lean_object* v___x_5190_; 
v___x_5190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5182_, v_upperBound_5183_, v_perm_5184_, v_a_5187_, v_b_5188_);
return v___x_5190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5191_, lean_object* v_xs_5192_, lean_object* v_upperBound_5193_, lean_object* v_perm_5194_, lean_object* v_inst_5195_, lean_object* v_R_5196_, lean_object* v_a_5197_, lean_object* v_b_5198_, lean_object* v_c_5199_){
_start:
{
lean_object* v_res_5200_; 
v_res_5200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5191_, v_xs_5192_, v_upperBound_5193_, v_perm_5194_, v_inst_5195_, v_R_5196_, v_a_5197_, v_b_5198_, v_c_5199_);
lean_dec_ref(v_perm_5194_);
lean_dec(v_upperBound_5193_);
lean_dec_ref(v_xs_5192_);
return v_res_5200_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5201_){
_start:
{
lean_object* v___x_5202_; lean_object* v___x_5203_; 
v___x_5202_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5203_ = lean_panic_fn_borrowed(v___x_5202_, v_msg_5201_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5204_, lean_object* v_msg_5205_){
_start:
{
lean_object* v___x_5206_; 
v___x_5206_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5205_);
return v___x_5206_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5207_, lean_object* v___x_5208_, lean_object* v_i_5209_, lean_object* v___x_5210_, lean_object* v_as_5211_, size_t v_i_5212_, size_t v_stop_5213_){
_start:
{
uint8_t v___x_5214_; 
v___x_5214_ = lean_usize_dec_eq(v_i_5212_, v_stop_5213_);
if (v___x_5214_ == 0)
{
uint8_t v___x_5215_; uint8_t v___y_5217_; lean_object* v___x_5221_; 
v___x_5215_ = 1;
v___x_5221_ = lean_array_uget_borrowed(v_as_5211_, v_i_5212_);
if (lean_obj_tag(v___x_5221_) == 0)
{
uint8_t v___x_5222_; 
v___x_5222_ = lean_nat_dec_lt(v_j_5207_, v___x_5208_);
v___y_5217_ = v___x_5222_;
goto v___jp_5216_;
}
else
{
uint8_t v___x_5223_; 
v___x_5223_ = lean_nat_dec_lt(v_i_5209_, v___x_5210_);
v___y_5217_ = v___x_5223_;
goto v___jp_5216_;
}
v___jp_5216_:
{
if (v___y_5217_ == 0)
{
size_t v___x_5218_; size_t v___x_5219_; 
v___x_5218_ = ((size_t)1ULL);
v___x_5219_ = lean_usize_add(v_i_5212_, v___x_5218_);
v_i_5212_ = v___x_5219_;
goto _start;
}
else
{
return v___x_5215_;
}
}
}
else
{
uint8_t v___x_5224_; 
v___x_5224_ = 0;
return v___x_5224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5225_, lean_object* v___x_5226_, lean_object* v_i_5227_, lean_object* v___x_5228_, lean_object* v_as_5229_, lean_object* v_i_5230_, lean_object* v_stop_5231_){
_start:
{
size_t v_i_boxed_5232_; size_t v_stop_boxed_5233_; uint8_t v_res_5234_; lean_object* v_r_5235_; 
v_i_boxed_5232_ = lean_unbox_usize(v_i_5230_);
lean_dec(v_i_5230_);
v_stop_boxed_5233_ = lean_unbox_usize(v_stop_5231_);
lean_dec(v_stop_5231_);
v_res_5234_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5225_, v___x_5226_, v_i_5227_, v___x_5228_, v_as_5229_, v_i_boxed_5232_, v_stop_boxed_5233_);
lean_dec_ref(v_as_5229_);
lean_dec(v___x_5228_);
lean_dec(v_i_5227_);
lean_dec(v___x_5226_);
lean_dec(v_j_5225_);
v_r_5235_ = lean_box(v_res_5234_);
return v_r_5235_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; 
v___x_5238_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5239_ = lean_unsigned_to_nat(10u);
v___x_5240_ = lean_unsigned_to_nat(425u);
v___x_5241_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5242_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5243_ = l_mkPanicMessageWithDecl(v___x_5242_, v___x_5241_, v___x_5240_, v___x_5239_, v___x_5238_);
return v___x_5243_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; 
v___x_5245_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5246_ = lean_unsigned_to_nat(12u);
v___x_5247_ = lean_unsigned_to_nat(433u);
v___x_5248_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5249_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5250_ = l_mkPanicMessageWithDecl(v___x_5249_, v___x_5248_, v___x_5247_, v___x_5246_, v___x_5245_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5251_, lean_object* v_fixedArgs_5252_, lean_object* v_varyingArgs_5253_, lean_object* v_i_5254_, lean_object* v_j_5255_, lean_object* v_xs_5256_){
_start:
{
lean_object* v_lower_5258_; lean_object* v_upper_5259_; lean_object* v___x_5263_; uint8_t v___x_5264_; 
v___x_5263_ = lean_array_get_size(v_perm_5251_);
v___x_5264_ = lean_nat_dec_lt(v_i_5254_, v___x_5263_);
if (v___x_5264_ == 0)
{
lean_object* v___x_5265_; lean_object* v___x_5266_; uint8_t v___x_5267_; 
lean_dec(v_i_5254_);
lean_dec_ref(v_perm_5251_);
v___x_5265_ = lean_unsigned_to_nat(0u);
v___x_5266_ = lean_array_get_size(v_varyingArgs_5253_);
v___x_5267_ = lean_nat_dec_le(v_j_5255_, v___x_5265_);
if (v___x_5267_ == 0)
{
v_lower_5258_ = v_j_5255_;
v_upper_5259_ = v___x_5266_;
goto v___jp_5257_;
}
else
{
lean_dec(v_j_5255_);
v_lower_5258_ = v___x_5265_;
v_upper_5259_ = v___x_5266_;
goto v___jp_5257_;
}
}
else
{
lean_object* v___x_5268_; 
v___x_5268_ = lean_array_fget_borrowed(v_perm_5251_, v_i_5254_);
if (lean_obj_tag(v___x_5268_) == 1)
{
lean_object* v_val_5269_; lean_object* v___x_5270_; uint8_t v___x_5271_; 
v_val_5269_ = lean_ctor_get(v___x_5268_, 0);
v___x_5270_ = lean_array_get_size(v_fixedArgs_5252_);
v___x_5271_ = lean_nat_dec_lt(v_val_5269_, v___x_5270_);
if (v___x_5271_ == 0)
{
lean_object* v___x_5272_; lean_object* v___x_5273_; 
lean_dec_ref(v_xs_5256_);
lean_dec(v_j_5255_);
lean_dec(v_i_5254_);
lean_dec_ref(v_varyingArgs_5253_);
lean_dec_ref(v_perm_5251_);
v___x_5272_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5273_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5272_);
return v___x_5273_;
}
else
{
lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5274_ = lean_unsigned_to_nat(1u);
v___x_5275_ = lean_nat_add(v_i_5254_, v___x_5274_);
lean_dec(v_i_5254_);
v___x_5276_ = lean_array_fget_borrowed(v_fixedArgs_5252_, v_val_5269_);
lean_inc(v___x_5276_);
v___x_5277_ = lean_array_push(v_xs_5256_, v___x_5276_);
v_i_5254_ = v___x_5275_;
v_xs_5256_ = v___x_5277_;
goto _start;
}
}
else
{
lean_object* v___x_5279_; lean_object* v___y_5281_; lean_object* v___y_5282_; lean_object* v___y_5283_; lean_object* v_lower_5291_; lean_object* v_upper_5292_; uint8_t v___x_5300_; 
v___x_5279_ = lean_array_get_size(v_varyingArgs_5253_);
v___x_5300_ = lean_nat_dec_lt(v_j_5255_, v___x_5279_);
if (v___x_5300_ == 0)
{
lean_object* v___x_5301_; uint8_t v___x_5302_; 
lean_dec_ref(v_varyingArgs_5253_);
v___x_5301_ = lean_unsigned_to_nat(0u);
v___x_5302_ = lean_nat_dec_le(v_i_5254_, v___x_5301_);
if (v___x_5302_ == 0)
{
lean_inc(v_i_5254_);
v_lower_5291_ = v_i_5254_;
v_upper_5292_ = v___x_5263_;
goto v___jp_5290_;
}
else
{
v_lower_5291_ = v___x_5301_;
v_upper_5292_ = v___x_5263_;
goto v___jp_5290_;
}
}
else
{
lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5303_ = lean_unsigned_to_nat(1u);
v___x_5304_ = lean_nat_add(v_i_5254_, v___x_5303_);
lean_dec(v_i_5254_);
v___x_5305_ = lean_nat_add(v_j_5255_, v___x_5303_);
v___x_5306_ = lean_array_fget_borrowed(v_varyingArgs_5253_, v_j_5255_);
lean_dec(v_j_5255_);
lean_inc(v___x_5306_);
v___x_5307_ = lean_array_push(v_xs_5256_, v___x_5306_);
v_i_5254_ = v___x_5304_;
v_j_5255_ = v___x_5305_;
v_xs_5256_ = v___x_5307_;
goto _start;
}
v___jp_5280_:
{
uint8_t v___x_5284_; 
v___x_5284_ = lean_nat_dec_lt(v___y_5281_, v___y_5283_);
if (v___x_5284_ == 0)
{
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec(v_j_5255_);
lean_dec(v_i_5254_);
return v_xs_5256_;
}
else
{
size_t v___x_5285_; size_t v___x_5286_; uint8_t v___x_5287_; 
v___x_5285_ = lean_usize_of_nat(v___y_5281_);
lean_dec(v___y_5281_);
v___x_5286_ = lean_usize_of_nat(v___y_5283_);
lean_dec(v___y_5283_);
v___x_5287_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5255_, v___x_5279_, v_i_5254_, v___x_5263_, v___y_5282_, v___x_5285_, v___x_5286_);
lean_dec_ref(v___y_5282_);
lean_dec(v_i_5254_);
lean_dec(v_j_5255_);
if (v___x_5287_ == 0)
{
return v_xs_5256_;
}
else
{
lean_object* v___x_5288_; lean_object* v___x_5289_; 
lean_dec_ref(v_xs_5256_);
v___x_5288_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5289_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5288_);
return v___x_5289_;
}
}
}
v___jp_5290_:
{
lean_object* v___x_5293_; lean_object* v_array_5294_; lean_object* v_start_5295_; lean_object* v_stop_5296_; uint8_t v___x_5297_; 
v___x_5293_ = l_Array_toSubarray___redArg(v_perm_5251_, v_lower_5291_, v_upper_5292_);
v_array_5294_ = lean_ctor_get(v___x_5293_, 0);
lean_inc_ref(v_array_5294_);
v_start_5295_ = lean_ctor_get(v___x_5293_, 1);
lean_inc(v_start_5295_);
v_stop_5296_ = lean_ctor_get(v___x_5293_, 2);
lean_inc(v_stop_5296_);
lean_dec_ref(v___x_5293_);
v___x_5297_ = lean_nat_dec_lt(v_start_5295_, v_stop_5296_);
if (v___x_5297_ == 0)
{
lean_dec(v_stop_5296_);
lean_dec(v_start_5295_);
lean_dec_ref(v_array_5294_);
lean_dec(v_j_5255_);
lean_dec(v_i_5254_);
return v_xs_5256_;
}
else
{
lean_object* v___x_5298_; uint8_t v___x_5299_; 
v___x_5298_ = lean_array_get_size(v_array_5294_);
v___x_5299_ = lean_nat_dec_le(v_stop_5296_, v___x_5298_);
if (v___x_5299_ == 0)
{
lean_dec(v_stop_5296_);
v___y_5281_ = v_start_5295_;
v___y_5282_ = v_array_5294_;
v___y_5283_ = v___x_5298_;
goto v___jp_5280_;
}
else
{
v___y_5281_ = v_start_5295_;
v___y_5282_ = v_array_5294_;
v___y_5283_ = v_stop_5296_;
goto v___jp_5280_;
}
}
}
}
}
v___jp_5257_:
{
lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5260_ = l_Array_toSubarray___redArg(v_varyingArgs_5253_, v_lower_5258_, v_upper_5259_);
v___x_5261_ = l_Subarray_copy___redArg(v___x_5260_);
v___x_5262_ = l_Array_append___redArg(v_xs_5256_, v___x_5261_);
lean_dec_ref(v___x_5261_);
return v___x_5262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5309_, lean_object* v_fixedArgs_5310_, lean_object* v_varyingArgs_5311_, lean_object* v_i_5312_, lean_object* v_j_5313_, lean_object* v_xs_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5309_, v_fixedArgs_5310_, v_varyingArgs_5311_, v_i_5312_, v_j_5313_, v_xs_5314_);
lean_dec_ref(v_fixedArgs_5310_);
return v_res_5315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5316_, lean_object* v_perm_5317_, lean_object* v_fixedArgs_5318_, lean_object* v_varyingArgs_5319_, lean_object* v_i_5320_, lean_object* v_j_5321_, lean_object* v_xs_5322_){
_start:
{
lean_object* v___x_5323_; 
v___x_5323_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5317_, v_fixedArgs_5318_, v_varyingArgs_5319_, v_i_5320_, v_j_5321_, v_xs_5322_);
return v___x_5323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5324_, lean_object* v_perm_5325_, lean_object* v_fixedArgs_5326_, lean_object* v_varyingArgs_5327_, lean_object* v_i_5328_, lean_object* v_j_5329_, lean_object* v_xs_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5324_, v_perm_5325_, v_fixedArgs_5326_, v_varyingArgs_5327_, v_i_5328_, v_j_5329_, v_xs_5330_);
lean_dec_ref(v_fixedArgs_5326_);
return v_res_5331_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; 
v___x_5334_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5335_ = lean_unsigned_to_nat(2u);
v___x_5336_ = lean_unsigned_to_nat(416u);
v___x_5337_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5339_ = l_mkPanicMessageWithDecl(v___x_5338_, v___x_5337_, v___x_5336_, v___x_5335_, v___x_5334_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5340_, lean_object* v_fixedArgs_5341_, lean_object* v_varyingArgs_5342_){
_start:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; uint8_t v___x_5345_; 
v___x_5343_ = lean_array_get_size(v_fixedArgs_5341_);
v___x_5344_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5340_);
v___x_5345_ = lean_nat_dec_eq(v___x_5343_, v___x_5344_);
lean_dec(v___x_5344_);
if (v___x_5345_ == 0)
{
lean_object* v___x_5346_; lean_object* v___x_5347_; 
lean_dec_ref(v_varyingArgs_5342_);
lean_dec_ref(v_perm_5340_);
v___x_5346_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5347_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5346_);
return v___x_5347_;
}
else
{
lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; 
v___x_5348_ = lean_unsigned_to_nat(0u);
v___x_5349_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5350_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5340_, v_fixedArgs_5341_, v_varyingArgs_5342_, v___x_5348_, v___x_5348_, v___x_5349_);
return v___x_5350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5351_, lean_object* v_fixedArgs_5352_, lean_object* v_varyingArgs_5353_){
_start:
{
lean_object* v_res_5354_; 
v_res_5354_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5351_, v_fixedArgs_5352_, v_varyingArgs_5353_);
lean_dec_ref(v_fixedArgs_5352_);
return v_res_5354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5355_, lean_object* v_perm_5356_, lean_object* v_fixedArgs_5357_, lean_object* v_varyingArgs_5358_){
_start:
{
lean_object* v___x_5359_; 
v___x_5359_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5356_, v_fixedArgs_5357_, v_varyingArgs_5358_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5360_, lean_object* v_perm_5361_, lean_object* v_fixedArgs_5362_, lean_object* v_varyingArgs_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5360_, v_perm_5361_, v_fixedArgs_5362_, v_varyingArgs_5363_);
lean_dec_ref(v_fixedArgs_5362_);
return v_res_5364_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5365_, lean_object* v_x_5366_){
_start:
{
if (lean_obj_tag(v_x_5365_) == 0)
{
if (lean_obj_tag(v_x_5366_) == 0)
{
uint8_t v___x_5367_; 
v___x_5367_ = 1;
return v___x_5367_;
}
else
{
uint8_t v___x_5368_; 
v___x_5368_ = 0;
return v___x_5368_;
}
}
else
{
if (lean_obj_tag(v_x_5366_) == 0)
{
uint8_t v___x_5369_; 
v___x_5369_ = 0;
return v___x_5369_;
}
else
{
lean_object* v_val_5370_; lean_object* v_val_5371_; uint8_t v___x_5372_; 
v_val_5370_ = lean_ctor_get(v_x_5365_, 0);
v_val_5371_ = lean_ctor_get(v_x_5366_, 0);
v___x_5372_ = lean_nat_dec_eq(v_val_5370_, v_val_5371_);
return v___x_5372_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5373_, lean_object* v_x_5374_){
_start:
{
uint8_t v_res_5375_; lean_object* v_r_5376_; 
v_res_5375_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5373_, v_x_5374_);
lean_dec(v_x_5374_);
lean_dec(v_x_5373_);
v_r_5376_ = lean_box(v_res_5375_);
return v_r_5376_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5377_, lean_object* v_ys_5378_, lean_object* v_x_5379_){
_start:
{
lean_object* v_zero_5380_; uint8_t v_isZero_5381_; 
v_zero_5380_ = lean_unsigned_to_nat(0u);
v_isZero_5381_ = lean_nat_dec_eq(v_x_5379_, v_zero_5380_);
if (v_isZero_5381_ == 1)
{
lean_dec(v_x_5379_);
return v_isZero_5381_;
}
else
{
lean_object* v_one_5382_; lean_object* v_n_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; uint8_t v___x_5386_; 
v_one_5382_ = lean_unsigned_to_nat(1u);
v_n_5383_ = lean_nat_sub(v_x_5379_, v_one_5382_);
lean_dec(v_x_5379_);
v___x_5384_ = lean_array_fget_borrowed(v_xs_5377_, v_n_5383_);
v___x_5385_ = lean_array_fget_borrowed(v_ys_5378_, v_n_5383_);
v___x_5386_ = l_instBEqOption_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5384_, v___x_5385_);
if (v___x_5386_ == 0)
{
lean_dec(v_n_5383_);
return v___x_5386_;
}
else
{
v_x_5379_ = v_n_5383_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5388_, lean_object* v_ys_5389_, lean_object* v_x_5390_){
_start:
{
uint8_t v_res_5391_; lean_object* v_r_5392_; 
v_res_5391_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5388_, v_ys_5389_, v_x_5390_);
lean_dec_ref(v_ys_5389_);
lean_dec_ref(v_xs_5388_);
v_r_5392_ = lean_box(v_res_5391_);
return v_r_5392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5393_, size_t v_i_5394_, lean_object* v_bs_5395_){
_start:
{
uint8_t v___x_5396_; 
v___x_5396_ = lean_usize_dec_lt(v_i_5394_, v_sz_5393_);
if (v___x_5396_ == 0)
{
return v_bs_5395_;
}
else
{
lean_object* v_v_5397_; lean_object* v___x_5398_; lean_object* v_bs_x27_5399_; lean_object* v___x_5400_; size_t v___x_5401_; size_t v___x_5402_; lean_object* v___x_5403_; 
v_v_5397_ = lean_array_uget(v_bs_5395_, v_i_5394_);
v___x_5398_ = lean_unsigned_to_nat(0u);
v_bs_x27_5399_ = lean_array_uset(v_bs_5395_, v_i_5394_, v___x_5398_);
v___x_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5400_, 0, v_v_5397_);
v___x_5401_ = ((size_t)1ULL);
v___x_5402_ = lean_usize_add(v_i_5394_, v___x_5401_);
v___x_5403_ = lean_array_uset(v_bs_x27_5399_, v_i_5394_, v___x_5400_);
v_i_5394_ = v___x_5402_;
v_bs_5395_ = v___x_5403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5405_, lean_object* v_i_5406_, lean_object* v_bs_5407_){
_start:
{
size_t v_sz_boxed_5408_; size_t v_i_boxed_5409_; lean_object* v_res_5410_; 
v_sz_boxed_5408_ = lean_unbox_usize(v_sz_5405_);
lean_dec(v_sz_5405_);
v_i_boxed_5409_ = lean_unbox_usize(v_i_5406_);
lean_dec(v_i_5406_);
v_res_5410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5408_, v_i_boxed_5409_, v_bs_5407_);
return v_res_5410_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5411_, lean_object* v_as_5412_, size_t v_i_5413_, size_t v_stop_5414_){
_start:
{
uint8_t v___x_5415_; 
v___x_5415_ = lean_usize_dec_eq(v_i_5413_, v_stop_5414_);
if (v___x_5415_ == 0)
{
lean_object* v_numFixed_5416_; uint8_t v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; size_t v_sz_5420_; size_t v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; 
v_numFixed_5416_ = lean_ctor_get(v_fixedParamPerms_5411_, 0);
v___x_5417_ = 1;
v___x_5418_ = lean_array_uget_borrowed(v_as_5412_, v_i_5413_);
lean_inc(v_numFixed_5416_);
v___x_5419_ = l_Array_range(v_numFixed_5416_);
v_sz_5420_ = lean_array_size(v___x_5419_);
v___x_5421_ = ((size_t)0ULL);
v___x_5422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5420_, v___x_5421_, v___x_5419_);
v___x_5423_ = lean_array_get_size(v___x_5418_);
v___x_5424_ = lean_nat_sub(v___x_5423_, v_numFixed_5416_);
v___x_5425_ = lean_box(0);
v___x_5426_ = lean_mk_array(v___x_5424_, v___x_5425_);
v___x_5427_ = l_Array_append___redArg(v___x_5422_, v___x_5426_);
lean_dec_ref(v___x_5426_);
v___x_5428_ = lean_array_get_size(v___x_5427_);
v___x_5429_ = lean_nat_dec_eq(v___x_5423_, v___x_5428_);
if (v___x_5429_ == 0)
{
lean_dec_ref(v___x_5427_);
lean_dec_ref(v_fixedParamPerms_5411_);
return v___x_5417_;
}
else
{
uint8_t v___x_5430_; 
v___x_5430_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5418_, v___x_5427_, v___x_5423_);
lean_dec_ref(v___x_5427_);
if (v___x_5430_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5411_);
return v___x_5417_;
}
else
{
size_t v___x_5431_; size_t v___x_5432_; 
v___x_5431_ = ((size_t)1ULL);
v___x_5432_ = lean_usize_add(v_i_5413_, v___x_5431_);
v_i_5413_ = v___x_5432_;
goto _start;
}
}
}
else
{
uint8_t v___x_5434_; 
lean_dec_ref(v_fixedParamPerms_5411_);
v___x_5434_ = 0;
return v___x_5434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5435_, lean_object* v_as_5436_, lean_object* v_i_5437_, lean_object* v_stop_5438_){
_start:
{
size_t v_i_boxed_5439_; size_t v_stop_boxed_5440_; uint8_t v_res_5441_; lean_object* v_r_5442_; 
v_i_boxed_5439_ = lean_unbox_usize(v_i_5437_);
lean_dec(v_i_5437_);
v_stop_boxed_5440_ = lean_unbox_usize(v_stop_5438_);
lean_dec(v_stop_5438_);
v_res_5441_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5435_, v_as_5436_, v_i_boxed_5439_, v_stop_boxed_5440_);
lean_dec_ref(v_as_5436_);
v_r_5442_ = lean_box(v_res_5441_);
return v_r_5442_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5443_){
_start:
{
lean_object* v_perms_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; uint8_t v___x_5447_; 
v_perms_5444_ = lean_ctor_get(v_fixedParamPerms_5443_, 1);
lean_inc_ref(v_perms_5444_);
v___x_5445_ = lean_unsigned_to_nat(0u);
v___x_5446_ = lean_array_get_size(v_perms_5444_);
v___x_5447_ = lean_nat_dec_lt(v___x_5445_, v___x_5446_);
if (v___x_5447_ == 0)
{
uint8_t v___x_5448_; 
lean_dec_ref(v_perms_5444_);
lean_dec_ref(v_fixedParamPerms_5443_);
v___x_5448_ = 1;
return v___x_5448_;
}
else
{
if (v___x_5447_ == 0)
{
lean_dec_ref(v_perms_5444_);
lean_dec_ref(v_fixedParamPerms_5443_);
return v___x_5447_;
}
else
{
size_t v___x_5449_; size_t v___x_5450_; uint8_t v___x_5451_; 
v___x_5449_ = ((size_t)0ULL);
v___x_5450_ = lean_usize_of_nat(v___x_5446_);
v___x_5451_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5443_, v_perms_5444_, v___x_5449_, v___x_5450_);
lean_dec_ref(v_perms_5444_);
if (v___x_5451_ == 0)
{
return v___x_5447_;
}
else
{
uint8_t v___x_5452_; 
v___x_5452_ = 0;
return v___x_5452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5453_){
_start:
{
uint8_t v_res_5454_; lean_object* v_r_5455_; 
v_res_5454_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5453_);
v_r_5455_ = lean_box(v_res_5454_);
return v_r_5455_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5456_, lean_object* v_ys_5457_, lean_object* v_hsz_5458_, lean_object* v_x_5459_, lean_object* v_x_5460_){
_start:
{
uint8_t v___x_5461_; 
v___x_5461_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5456_, v_ys_5457_, v_x_5459_);
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5462_, lean_object* v_ys_5463_, lean_object* v_hsz_5464_, lean_object* v_x_5465_, lean_object* v_x_5466_){
_start:
{
uint8_t v_res_5467_; lean_object* v_r_5468_; 
v_res_5467_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5462_, v_ys_5463_, v_hsz_5464_, v_x_5465_, v_x_5466_);
lean_dec_ref(v_ys_5463_);
lean_dec_ref(v_xs_5462_);
v_r_5468_ = lean_box(v_res_5467_);
return v_r_5468_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___x_5469_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5470_, 0, v___x_5469_);
lean_ctor_set(v___x_5470_, 1, v___x_5469_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5471_){
_start:
{
lean_object* v___f_5472_; lean_object* v___f_5473_; lean_object* v___f_5474_; lean_object* v___f_5475_; lean_object* v___f_5476_; lean_object* v___f_5477_; lean_object* v___f_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___f_5472_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5473_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5474_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5475_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5476_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5477_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5478_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5479_, 0, v___f_5472_);
lean_ctor_set(v___x_5479_, 1, v___f_5473_);
v___x_5480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5479_);
lean_ctor_set(v___x_5480_, 1, v___f_5474_);
lean_ctor_set(v___x_5480_, 2, v___f_5475_);
lean_ctor_set(v___x_5480_, 3, v___f_5476_);
lean_ctor_set(v___x_5480_, 4, v___f_5477_);
v___x_5481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5481_, 0, v___x_5480_);
lean_ctor_set(v___x_5481_, 1, v___f_5478_);
v___x_5482_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5483_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5482_);
lean_ctor_set(v___x_5484_, 1, v___x_5483_);
v___x_5485_ = l_instInhabitedOfMonad___redArg(v___x_5481_, v___x_5484_);
v___x_5486_ = lean_panic_fn_borrowed(v___x_5485_, v_msg_5471_);
lean_dec(v___x_5485_);
return v___x_5486_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___x_5487_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5488_, 0, v___x_5487_);
return v___x_5488_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5489_){
_start:
{
lean_object* v___f_5490_; lean_object* v___f_5491_; lean_object* v___f_5492_; lean_object* v___f_5493_; lean_object* v___f_5494_; lean_object* v___f_5495_; lean_object* v___f_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; 
v___f_5490_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5491_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5492_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5493_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5494_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5495_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5496_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5497_, 0, v___f_5490_);
lean_ctor_set(v___x_5497_, 1, v___f_5491_);
v___x_5498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5498_, 0, v___x_5497_);
lean_ctor_set(v___x_5498_, 1, v___f_5492_);
lean_ctor_set(v___x_5498_, 2, v___f_5493_);
lean_ctor_set(v___x_5498_, 3, v___f_5494_);
lean_ctor_set(v___x_5498_, 4, v___f_5495_);
v___x_5499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5499_, 0, v___x_5498_);
lean_ctor_set(v___x_5499_, 1, v___f_5496_);
v___x_5500_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5501_ = l_instInhabitedOfMonad___redArg(v___x_5499_, v___x_5500_);
v___x_5502_ = lean_panic_fn_borrowed(v___x_5501_, v_msg_5489_);
lean_dec(v___x_5501_);
return v___x_5502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5503_, lean_object* v___x_5504_, lean_object* v___x_5505_, lean_object* v_as_5506_, size_t v_sz_5507_, size_t v_i_5508_, lean_object* v_b_5509_){
_start:
{
lean_object* v_a_5511_; uint8_t v___x_5515_; 
v___x_5515_ = lean_usize_dec_lt(v_i_5508_, v_sz_5507_);
if (v___x_5515_ == 0)
{
return v_b_5509_;
}
else
{
lean_object* v_fst_5516_; lean_object* v_snd_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5542_; 
v_fst_5516_ = lean_ctor_get(v_b_5509_, 0);
v_snd_5517_ = lean_ctor_get(v_b_5509_, 1);
v_isSharedCheck_5542_ = !lean_is_exclusive(v_b_5509_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5519_ = v_b_5509_;
v_isShared_5520_ = v_isSharedCheck_5542_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_snd_5517_);
lean_inc(v_fst_5516_);
lean_dec(v_b_5509_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5542_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; lean_object* v_a_5522_; lean_object* v___x_5523_; 
v___x_5521_ = lean_box(0);
v_a_5522_ = lean_array_uget_borrowed(v_as_5506_, v_i_5508_);
v___x_5523_ = lean_array_get_borrowed(v___x_5521_, v___x_5503_, v_a_5522_);
if (lean_obj_tag(v___x_5523_) == 1)
{
lean_object* v_val_5524_; uint8_t v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; uint8_t v___x_5528_; 
v_val_5524_ = lean_ctor_get(v___x_5523_, 0);
v___x_5525_ = 0;
v___x_5526_ = lean_box(v___x_5525_);
v___x_5527_ = lean_array_get(v___x_5526_, v_fst_5516_, v_val_5524_);
lean_dec(v___x_5526_);
v___x_5528_ = lean_unbox(v___x_5527_);
lean_dec(v___x_5527_);
if (v___x_5528_ == 0)
{
uint8_t v_changed_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5534_; 
lean_dec(v_snd_5517_);
v_changed_5529_ = lean_nat_dec_eq(v___x_5504_, v___x_5505_);
v___x_5530_ = lean_box(v_changed_5529_);
v___x_5531_ = lean_array_set(v_fst_5516_, v_val_5524_, v___x_5530_);
v___x_5532_ = lean_box(v_changed_5529_);
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 1, v___x_5532_);
lean_ctor_set(v___x_5519_, 0, v___x_5531_);
v___x_5534_ = v___x_5519_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v___x_5531_);
lean_ctor_set(v_reuseFailAlloc_5535_, 1, v___x_5532_);
v___x_5534_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
v_a_5511_ = v___x_5534_;
goto v___jp_5510_;
}
}
else
{
lean_object* v___x_5537_; 
if (v_isShared_5520_ == 0)
{
v___x_5537_ = v___x_5519_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_fst_5516_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v_snd_5517_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
v_a_5511_ = v___x_5537_;
goto v___jp_5510_;
}
}
}
else
{
lean_object* v___x_5540_; 
if (v_isShared_5520_ == 0)
{
v___x_5540_ = v___x_5519_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_fst_5516_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v_snd_5517_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
v_a_5511_ = v___x_5540_;
goto v___jp_5510_;
}
}
}
}
v___jp_5510_:
{
size_t v___x_5512_; size_t v___x_5513_; 
v___x_5512_ = ((size_t)1ULL);
v___x_5513_ = lean_usize_add(v_i_5508_, v___x_5512_);
v_i_5508_ = v___x_5513_;
v_b_5509_ = v_a_5511_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5543_, lean_object* v___x_5544_, lean_object* v___x_5545_, lean_object* v_as_5546_, lean_object* v_sz_5547_, lean_object* v_i_5548_, lean_object* v_b_5549_){
_start:
{
size_t v_sz_boxed_5550_; size_t v_i_boxed_5551_; lean_object* v_res_5552_; 
v_sz_boxed_5550_ = lean_unbox_usize(v_sz_5547_);
lean_dec(v_sz_5547_);
v_i_boxed_5551_ = lean_unbox_usize(v_i_5548_);
lean_dec(v_i_5548_);
v_res_5552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5543_, v___x_5544_, v___x_5545_, v_as_5546_, v_sz_boxed_5550_, v_i_boxed_5551_, v_b_5549_);
lean_dec_ref(v_as_5546_);
lean_dec(v___x_5545_);
lean_dec(v___x_5544_);
lean_dec_ref(v___x_5543_);
return v_res_5552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5553_, lean_object* v___x_5554_, lean_object* v_fixedParamPerms_5555_, lean_object* v_next_5556_, lean_object* v___x_5557_, lean_object* v___x_5558_, lean_object* v_a_5559_, lean_object* v_b_5560_){
_start:
{
lean_object* v_a_5562_; uint8_t v___x_5566_; 
v___x_5566_ = lean_nat_dec_lt(v_a_5559_, v_upperBound_5553_);
if (v___x_5566_ == 0)
{
lean_dec(v_a_5559_);
return v_b_5560_;
}
else
{
lean_object* v_fst_5567_; lean_object* v_snd_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5603_; 
v_fst_5567_ = lean_ctor_get(v_b_5560_, 0);
v_snd_5568_ = lean_ctor_get(v_b_5560_, 1);
v_isSharedCheck_5603_ = !lean_is_exclusive(v_b_5560_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5570_ = v_b_5560_;
v_isShared_5571_ = v_isSharedCheck_5603_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_snd_5568_);
lean_inc(v_fst_5567_);
lean_dec(v_b_5560_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5603_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5572_; 
v___x_5572_ = lean_array_fget_borrowed(v___x_5554_, v_a_5559_);
if (lean_obj_tag(v___x_5572_) == 1)
{
lean_object* v_val_5573_; uint8_t v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; uint8_t v___x_5577_; 
v_val_5573_ = lean_ctor_get(v___x_5572_, 0);
v___x_5574_ = 0;
v___x_5575_ = lean_box(v___x_5574_);
v___x_5576_ = lean_array_get(v___x_5575_, v_fst_5567_, v_val_5573_);
lean_dec(v___x_5575_);
v___x_5577_ = lean_unbox(v___x_5576_);
lean_dec(v___x_5576_);
if (v___x_5577_ == 0)
{
lean_object* v___x_5579_; 
if (v_isShared_5571_ == 0)
{
v___x_5579_ = v___x_5570_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_fst_5567_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v_snd_5568_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
v_a_5562_ = v___x_5579_;
goto v___jp_5561_;
}
}
else
{
lean_object* v_revDeps_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5586_; 
v_revDeps_5581_ = lean_ctor_get(v_fixedParamPerms_5555_, 2);
v___x_5582_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5583_ = lean_array_get_borrowed(v___x_5582_, v_revDeps_5581_, v_next_5556_);
v___x_5584_ = lean_array_get_borrowed(v___x_5582_, v___x_5583_, v_a_5559_);
if (v_isShared_5571_ == 0)
{
v___x_5586_ = v___x_5570_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_fst_5567_);
lean_ctor_set(v_reuseFailAlloc_5599_, 1, v_snd_5568_);
v___x_5586_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
size_t v_sz_5587_; size_t v___x_5588_; lean_object* v___x_5589_; lean_object* v_fst_5590_; lean_object* v_snd_5591_; lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5598_; 
v_sz_5587_ = lean_array_size(v___x_5584_);
v___x_5588_ = ((size_t)0ULL);
v___x_5589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5554_, v___x_5557_, v___x_5558_, v___x_5584_, v_sz_5587_, v___x_5588_, v___x_5586_);
v_fst_5590_ = lean_ctor_get(v___x_5589_, 0);
v_snd_5591_ = lean_ctor_get(v___x_5589_, 1);
v_isSharedCheck_5598_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5598_ == 0)
{
v___x_5593_ = v___x_5589_;
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
else
{
lean_inc(v_snd_5591_);
lean_inc(v_fst_5590_);
lean_dec(v___x_5589_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5598_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v___x_5596_; 
if (v_isShared_5594_ == 0)
{
v___x_5596_ = v___x_5593_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_fst_5590_);
lean_ctor_set(v_reuseFailAlloc_5597_, 1, v_snd_5591_);
v___x_5596_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
v_a_5562_ = v___x_5596_;
goto v___jp_5561_;
}
}
}
}
}
else
{
lean_object* v___x_5601_; 
if (v_isShared_5571_ == 0)
{
v___x_5601_ = v___x_5570_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_fst_5567_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v_snd_5568_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
v_a_5562_ = v___x_5601_;
goto v___jp_5561_;
}
}
}
}
v___jp_5561_:
{
lean_object* v___x_5563_; lean_object* v___x_5564_; 
v___x_5563_ = lean_unsigned_to_nat(1u);
v___x_5564_ = lean_nat_add(v_a_5559_, v___x_5563_);
lean_dec(v_a_5559_);
v_a_5559_ = v___x_5564_;
v_b_5560_ = v_a_5562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5604_, lean_object* v___x_5605_, lean_object* v_fixedParamPerms_5606_, lean_object* v_next_5607_, lean_object* v___x_5608_, lean_object* v___x_5609_, lean_object* v_a_5610_, lean_object* v_b_5611_){
_start:
{
lean_object* v_res_5612_; 
v_res_5612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5604_, v___x_5605_, v_fixedParamPerms_5606_, v_next_5607_, v___x_5608_, v___x_5609_, v_a_5610_, v_b_5611_);
lean_dec(v___x_5609_);
lean_dec(v___x_5608_);
lean_dec(v_next_5607_);
lean_dec_ref(v_fixedParamPerms_5606_);
lean_dec_ref(v___x_5605_);
lean_dec(v_upperBound_5604_);
return v_res_5612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(lean_object* v_upperBound_5613_, lean_object* v___x_5614_, lean_object* v_fixedParamPerms_5615_, lean_object* v___x_5616_, lean_object* v___x_5617_, lean_object* v_a_5618_, lean_object* v_b_5619_){
_start:
{
uint8_t v___x_5620_; 
v___x_5620_ = lean_nat_dec_lt(v_a_5618_, v_upperBound_5613_);
if (v___x_5620_ == 0)
{
lean_dec(v_a_5618_);
return v_b_5619_;
}
else
{
lean_object* v_fst_5621_; lean_object* v_snd_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5645_; 
v_fst_5621_ = lean_ctor_get(v_b_5619_, 0);
v_snd_5622_ = lean_ctor_get(v_b_5619_, 1);
v_isSharedCheck_5645_ = !lean_is_exclusive(v_b_5619_);
if (v_isSharedCheck_5645_ == 0)
{
v___x_5624_ = v_b_5619_;
v_isShared_5625_ = v_isSharedCheck_5645_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_snd_5622_);
lean_inc(v_fst_5621_);
lean_dec(v_b_5619_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5645_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5630_; 
v___x_5626_ = lean_array_fget_borrowed(v___x_5614_, v_a_5618_);
v___x_5627_ = lean_array_get_size(v___x_5626_);
v___x_5628_ = lean_unsigned_to_nat(0u);
if (v_isShared_5625_ == 0)
{
v___x_5630_ = v___x_5624_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v_fst_5621_);
lean_ctor_set(v_reuseFailAlloc_5644_, 1, v_snd_5622_);
v___x_5630_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
lean_object* v___x_5631_; lean_object* v_fst_5632_; lean_object* v_snd_5633_; lean_object* v___x_5635_; uint8_t v_isShared_5636_; uint8_t v_isSharedCheck_5643_; 
v___x_5631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5627_, v___x_5626_, v_fixedParamPerms_5615_, v_a_5618_, v___x_5616_, v___x_5617_, v___x_5628_, v___x_5630_);
v_fst_5632_ = lean_ctor_get(v___x_5631_, 0);
v_snd_5633_ = lean_ctor_get(v___x_5631_, 1);
v_isSharedCheck_5643_ = !lean_is_exclusive(v___x_5631_);
if (v_isSharedCheck_5643_ == 0)
{
v___x_5635_ = v___x_5631_;
v_isShared_5636_ = v_isSharedCheck_5643_;
goto v_resetjp_5634_;
}
else
{
lean_inc(v_snd_5633_);
lean_inc(v_fst_5632_);
lean_dec(v___x_5631_);
v___x_5635_ = lean_box(0);
v_isShared_5636_ = v_isSharedCheck_5643_;
goto v_resetjp_5634_;
}
v_resetjp_5634_:
{
lean_object* v___x_5638_; 
if (v_isShared_5636_ == 0)
{
v___x_5638_ = v___x_5635_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_fst_5632_);
lean_ctor_set(v_reuseFailAlloc_5642_, 1, v_snd_5633_);
v___x_5638_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
lean_object* v___x_5639_; lean_object* v___x_5640_; 
v___x_5639_ = lean_unsigned_to_nat(1u);
v___x_5640_ = lean_nat_add(v_a_5618_, v___x_5639_);
lean_dec(v_a_5618_);
v_a_5618_ = v___x_5640_;
v_b_5619_ = v___x_5638_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg___boxed(lean_object* v_upperBound_5646_, lean_object* v___x_5647_, lean_object* v_fixedParamPerms_5648_, lean_object* v___x_5649_, lean_object* v___x_5650_, lean_object* v_a_5651_, lean_object* v_b_5652_){
_start:
{
lean_object* v_res_5653_; 
v_res_5653_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(v_upperBound_5646_, v___x_5647_, v_fixedParamPerms_5648_, v___x_5649_, v___x_5650_, v_a_5651_, v_b_5652_);
lean_dec(v___x_5650_);
lean_dec(v___x_5649_);
lean_dec_ref(v_fixedParamPerms_5648_);
lean_dec_ref(v___x_5647_);
lean_dec(v_upperBound_5646_);
return v_res_5653_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5654_, lean_object* v___x_5655_, lean_object* v___x_5656_, lean_object* v___x_5657_, lean_object* v_fixedParamPerms_5658_, lean_object* v_a_5659_, lean_object* v_b_5660_){
_start:
{
uint8_t v___x_5661_; 
v___x_5661_ = lean_nat_dec_lt(v_a_5659_, v_upperBound_5654_);
if (v___x_5661_ == 0)
{
return v_b_5660_;
}
else
{
lean_object* v_fst_5662_; lean_object* v_snd_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5686_; 
v_fst_5662_ = lean_ctor_get(v_b_5660_, 0);
v_snd_5663_ = lean_ctor_get(v_b_5660_, 1);
v_isSharedCheck_5686_ = !lean_is_exclusive(v_b_5660_);
if (v_isSharedCheck_5686_ == 0)
{
v___x_5665_ = v_b_5660_;
v_isShared_5666_ = v_isSharedCheck_5686_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_snd_5663_);
lean_inc(v_fst_5662_);
lean_dec(v_b_5660_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5686_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5671_; 
v___x_5667_ = lean_array_fget_borrowed(v___x_5655_, v_a_5659_);
v___x_5668_ = lean_array_get_size(v___x_5667_);
v___x_5669_ = lean_unsigned_to_nat(0u);
if (v_isShared_5666_ == 0)
{
v___x_5671_ = v___x_5665_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5685_; 
v_reuseFailAlloc_5685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_fst_5662_);
lean_ctor_set(v_reuseFailAlloc_5685_, 1, v_snd_5663_);
v___x_5671_ = v_reuseFailAlloc_5685_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
lean_object* v___x_5672_; lean_object* v_fst_5673_; lean_object* v_snd_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5684_; 
v___x_5672_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5668_, v___x_5667_, v_fixedParamPerms_5658_, v_a_5659_, v___x_5656_, v___x_5657_, v___x_5669_, v___x_5671_);
v_fst_5673_ = lean_ctor_get(v___x_5672_, 0);
v_snd_5674_ = lean_ctor_get(v___x_5672_, 1);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5672_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5676_ = v___x_5672_;
v_isShared_5677_ = v_isSharedCheck_5684_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_snd_5674_);
lean_inc(v_fst_5673_);
lean_dec(v___x_5672_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5684_;
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
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_fst_5673_);
lean_ctor_set(v_reuseFailAlloc_5683_, 1, v_snd_5674_);
v___x_5679_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; 
v___x_5680_ = lean_unsigned_to_nat(1u);
v___x_5681_ = lean_nat_add(v_a_5659_, v___x_5680_);
v___x_5682_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(v_upperBound_5654_, v___x_5655_, v_fixedParamPerms_5658_, v___x_5656_, v___x_5657_, v___x_5681_, v___x_5679_);
return v___x_5682_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5687_, lean_object* v___x_5688_, lean_object* v___x_5689_, lean_object* v___x_5690_, lean_object* v_fixedParamPerms_5691_, lean_object* v_a_5692_, lean_object* v_b_5693_){
_start:
{
lean_object* v_res_5694_; 
v_res_5694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5687_, v___x_5688_, v___x_5689_, v___x_5690_, v_fixedParamPerms_5691_, v_a_5692_, v_b_5693_);
lean_dec(v_a_5692_);
lean_dec_ref(v_fixedParamPerms_5691_);
lean_dec(v___x_5690_);
lean_dec(v___x_5689_);
lean_dec_ref(v___x_5688_);
lean_dec(v_upperBound_5687_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5695_, lean_object* v___x_5696_, lean_object* v___x_5697_, lean_object* v_fixedParamPerms_5698_, lean_object* v_a_5699_){
_start:
{
lean_object* v_snd_5700_; uint8_t v___x_5701_; 
v_snd_5700_ = lean_ctor_get(v_a_5699_, 1);
v___x_5701_ = lean_unbox(v_snd_5700_);
if (v___x_5701_ == 0)
{
lean_object* v_fst_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5709_; 
lean_inc(v_snd_5700_);
v_fst_5702_ = lean_ctor_get(v_a_5699_, 0);
v_isSharedCheck_5709_ = !lean_is_exclusive(v_a_5699_);
if (v_isSharedCheck_5709_ == 0)
{
lean_object* v_unused_5710_; 
v_unused_5710_ = lean_ctor_get(v_a_5699_, 1);
lean_dec(v_unused_5710_);
v___x_5704_ = v_a_5699_;
v_isShared_5705_ = v_isSharedCheck_5709_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_fst_5702_);
lean_dec(v_a_5699_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5709_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v___x_5707_; 
if (v_isShared_5705_ == 0)
{
v___x_5707_ = v___x_5704_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_fst_5702_);
lean_ctor_set(v_reuseFailAlloc_5708_, 1, v_snd_5700_);
v___x_5707_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
return v___x_5707_;
}
}
}
else
{
lean_object* v_fst_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5732_; 
v_fst_5711_ = lean_ctor_get(v_a_5699_, 0);
v_isSharedCheck_5732_ = !lean_is_exclusive(v_a_5699_);
if (v_isSharedCheck_5732_ == 0)
{
lean_object* v_unused_5733_; 
v_unused_5733_ = lean_ctor_get(v_a_5699_, 1);
lean_dec(v_unused_5733_);
v___x_5713_ = v_a_5699_;
v_isShared_5714_ = v_isSharedCheck_5732_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_fst_5711_);
lean_dec(v_a_5699_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5732_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
uint8_t v_changed_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5719_; 
v_changed_5715_ = 0;
v___x_5716_ = lean_unsigned_to_nat(0u);
v___x_5717_ = lean_box(v_changed_5715_);
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 1, v___x_5717_);
v___x_5719_ = v___x_5713_;
goto v_reusejp_5718_;
}
else
{
lean_object* v_reuseFailAlloc_5731_; 
v_reuseFailAlloc_5731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_fst_5711_);
lean_ctor_set(v_reuseFailAlloc_5731_, 1, v___x_5717_);
v___x_5719_ = v_reuseFailAlloc_5731_;
goto v_reusejp_5718_;
}
v_reusejp_5718_:
{
lean_object* v___x_5720_; lean_object* v_fst_5721_; lean_object* v_snd_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5730_; 
v___x_5720_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5695_, v___x_5696_, v___x_5697_, v___x_5695_, v_fixedParamPerms_5698_, v___x_5716_, v___x_5719_);
v_fst_5721_ = lean_ctor_get(v___x_5720_, 0);
v_snd_5722_ = lean_ctor_get(v___x_5720_, 1);
v_isSharedCheck_5730_ = !lean_is_exclusive(v___x_5720_);
if (v_isSharedCheck_5730_ == 0)
{
v___x_5724_ = v___x_5720_;
v_isShared_5725_ = v_isSharedCheck_5730_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_snd_5722_);
lean_inc(v_fst_5721_);
lean_dec(v___x_5720_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5730_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v___x_5727_; 
if (v_isShared_5725_ == 0)
{
v___x_5727_ = v___x_5724_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_fst_5721_);
lean_ctor_set(v_reuseFailAlloc_5729_, 1, v_snd_5722_);
v___x_5727_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
v_a_5699_ = v___x_5727_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5734_, lean_object* v___x_5735_, lean_object* v___x_5736_, lean_object* v_fixedParamPerms_5737_, lean_object* v_a_5738_){
_start:
{
lean_object* v_res_5739_; 
v_res_5739_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5734_, v___x_5735_, v___x_5736_, v_fixedParamPerms_5737_, v_a_5738_);
lean_dec_ref(v_fixedParamPerms_5737_);
lean_dec(v___x_5736_);
lean_dec_ref(v___x_5735_);
lean_dec(v___x_5734_);
return v_res_5739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5740_, lean_object* v_a_5741_, lean_object* v_b_5742_){
_start:
{
lean_object* v_a_5744_; uint8_t v___x_5748_; 
v___x_5748_ = lean_nat_dec_lt(v_a_5741_, v_upperBound_5740_);
if (v___x_5748_ == 0)
{
lean_dec(v_a_5741_);
return v_b_5742_;
}
else
{
lean_object* v_snd_5749_; lean_object* v_snd_5750_; lean_object* v_snd_5751_; lean_object* v_snd_5752_; lean_object* v_fst_5753_; lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5865_; 
v_snd_5749_ = lean_ctor_get(v_b_5742_, 1);
lean_inc(v_snd_5749_);
v_snd_5750_ = lean_ctor_get(v_snd_5749_, 1);
lean_inc(v_snd_5750_);
v_snd_5751_ = lean_ctor_get(v_snd_5750_, 1);
lean_inc(v_snd_5751_);
v_snd_5752_ = lean_ctor_get(v_snd_5751_, 1);
lean_inc(v_snd_5752_);
v_fst_5753_ = lean_ctor_get(v_b_5742_, 0);
v_isSharedCheck_5865_ = !lean_is_exclusive(v_b_5742_);
if (v_isSharedCheck_5865_ == 0)
{
lean_object* v_unused_5866_; 
v_unused_5866_ = lean_ctor_get(v_b_5742_, 1);
lean_dec(v_unused_5866_);
v___x_5755_ = v_b_5742_;
v_isShared_5756_ = v_isSharedCheck_5865_;
goto v_resetjp_5754_;
}
else
{
lean_inc(v_fst_5753_);
lean_dec(v_b_5742_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5865_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v_fst_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5863_; 
v_fst_5757_ = lean_ctor_get(v_snd_5749_, 0);
v_isSharedCheck_5863_ = !lean_is_exclusive(v_snd_5749_);
if (v_isSharedCheck_5863_ == 0)
{
lean_object* v_unused_5864_; 
v_unused_5864_ = lean_ctor_get(v_snd_5749_, 1);
lean_dec(v_unused_5864_);
v___x_5759_ = v_snd_5749_;
v_isShared_5760_ = v_isSharedCheck_5863_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_fst_5757_);
lean_dec(v_snd_5749_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5863_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v_fst_5761_; lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5861_; 
v_fst_5761_ = lean_ctor_get(v_snd_5750_, 0);
v_isSharedCheck_5861_ = !lean_is_exclusive(v_snd_5750_);
if (v_isSharedCheck_5861_ == 0)
{
lean_object* v_unused_5862_; 
v_unused_5862_ = lean_ctor_get(v_snd_5750_, 1);
lean_dec(v_unused_5862_);
v___x_5763_ = v_snd_5750_;
v_isShared_5764_ = v_isSharedCheck_5861_;
goto v_resetjp_5762_;
}
else
{
lean_inc(v_fst_5761_);
lean_dec(v_snd_5750_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5861_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
lean_object* v_fst_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5859_; 
v_fst_5765_ = lean_ctor_get(v_snd_5751_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v_snd_5751_);
if (v_isSharedCheck_5859_ == 0)
{
lean_object* v_unused_5860_; 
v_unused_5860_ = lean_ctor_get(v_snd_5751_, 1);
lean_dec(v_unused_5860_);
v___x_5767_ = v_snd_5751_;
v_isShared_5768_ = v_isSharedCheck_5859_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_fst_5765_);
lean_dec(v_snd_5751_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5859_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v_array_5769_; lean_object* v_start_5770_; lean_object* v_stop_5771_; uint8_t v___x_5772_; 
v_array_5769_ = lean_ctor_get(v_snd_5752_, 0);
v_start_5770_ = lean_ctor_get(v_snd_5752_, 1);
v_stop_5771_ = lean_ctor_get(v_snd_5752_, 2);
v___x_5772_ = lean_nat_dec_lt(v_start_5770_, v_stop_5771_);
if (v___x_5772_ == 0)
{
lean_object* v___x_5774_; 
lean_dec(v_a_5741_);
if (v_isShared_5768_ == 0)
{
v___x_5774_ = v___x_5767_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_fst_5765_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v_snd_5752_);
v___x_5774_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
lean_object* v___x_5776_; 
if (v_isShared_5764_ == 0)
{
lean_ctor_set(v___x_5763_, 1, v___x_5774_);
v___x_5776_ = v___x_5763_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_fst_5761_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v___x_5774_);
v___x_5776_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5778_; 
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 1, v___x_5776_);
v___x_5778_ = v___x_5759_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_fst_5757_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5776_);
v___x_5778_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_5780_; 
if (v_isShared_5756_ == 0)
{
lean_ctor_set(v___x_5755_, 1, v___x_5778_);
v___x_5780_ = v___x_5755_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_fst_5753_);
lean_ctor_set(v_reuseFailAlloc_5781_, 1, v___x_5778_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
}
else
{
lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5855_; 
lean_inc(v_stop_5771_);
lean_inc(v_start_5770_);
lean_inc_ref(v_array_5769_);
v_isSharedCheck_5855_ = !lean_is_exclusive(v_snd_5752_);
if (v_isSharedCheck_5855_ == 0)
{
lean_object* v_unused_5856_; lean_object* v_unused_5857_; lean_object* v_unused_5858_; 
v_unused_5856_ = lean_ctor_get(v_snd_5752_, 2);
lean_dec(v_unused_5856_);
v_unused_5857_ = lean_ctor_get(v_snd_5752_, 1);
lean_dec(v_unused_5857_);
v_unused_5858_ = lean_ctor_get(v_snd_5752_, 0);
lean_dec(v_unused_5858_);
v___x_5786_ = v_snd_5752_;
v_isShared_5787_ = v_isSharedCheck_5855_;
goto v_resetjp_5785_;
}
else
{
lean_dec(v_snd_5752_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5855_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v_array_5788_; lean_object* v_start_5789_; lean_object* v_stop_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5795_; 
v_array_5788_ = lean_ctor_get(v_fst_5765_, 0);
v_start_5789_ = lean_ctor_get(v_fst_5765_, 1);
v_stop_5790_ = lean_ctor_get(v_fst_5765_, 2);
v___x_5791_ = lean_array_fget(v_array_5769_, v_start_5770_);
v___x_5792_ = lean_unsigned_to_nat(1u);
v___x_5793_ = lean_nat_add(v_start_5770_, v___x_5792_);
lean_dec(v_start_5770_);
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 1, v___x_5793_);
v___x_5795_ = v___x_5786_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5854_; 
v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_array_5769_);
lean_ctor_set(v_reuseFailAlloc_5854_, 1, v___x_5793_);
lean_ctor_set(v_reuseFailAlloc_5854_, 2, v_stop_5771_);
v___x_5795_ = v_reuseFailAlloc_5854_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
uint8_t v___x_5796_; 
v___x_5796_ = lean_nat_dec_lt(v_start_5789_, v_stop_5790_);
if (v___x_5796_ == 0)
{
lean_object* v___x_5798_; 
lean_dec(v___x_5791_);
lean_dec(v_a_5741_);
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5795_);
v___x_5798_ = v___x_5767_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5808_; 
v_reuseFailAlloc_5808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5808_, 0, v_fst_5765_);
lean_ctor_set(v_reuseFailAlloc_5808_, 1, v___x_5795_);
v___x_5798_ = v_reuseFailAlloc_5808_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
lean_object* v___x_5800_; 
if (v_isShared_5764_ == 0)
{
lean_ctor_set(v___x_5763_, 1, v___x_5798_);
v___x_5800_ = v___x_5763_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v_fst_5761_);
lean_ctor_set(v_reuseFailAlloc_5807_, 1, v___x_5798_);
v___x_5800_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
lean_object* v___x_5802_; 
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 1, v___x_5800_);
v___x_5802_ = v___x_5759_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_fst_5757_);
lean_ctor_set(v_reuseFailAlloc_5806_, 1, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
lean_object* v___x_5804_; 
if (v_isShared_5756_ == 0)
{
lean_ctor_set(v___x_5755_, 1, v___x_5802_);
v___x_5804_ = v___x_5755_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_fst_5753_);
lean_ctor_set(v_reuseFailAlloc_5805_, 1, v___x_5802_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
}
}
else
{
lean_object* v___x_5810_; uint8_t v_isShared_5811_; uint8_t v_isSharedCheck_5850_; 
lean_inc(v_stop_5790_);
lean_inc(v_start_5789_);
lean_inc_ref(v_array_5788_);
v_isSharedCheck_5850_ = !lean_is_exclusive(v_fst_5765_);
if (v_isSharedCheck_5850_ == 0)
{
lean_object* v_unused_5851_; lean_object* v_unused_5852_; lean_object* v_unused_5853_; 
v_unused_5851_ = lean_ctor_get(v_fst_5765_, 2);
lean_dec(v_unused_5851_);
v_unused_5852_ = lean_ctor_get(v_fst_5765_, 1);
lean_dec(v_unused_5852_);
v_unused_5853_ = lean_ctor_get(v_fst_5765_, 0);
lean_dec(v_unused_5853_);
v___x_5810_ = v_fst_5765_;
v_isShared_5811_ = v_isSharedCheck_5850_;
goto v_resetjp_5809_;
}
else
{
lean_dec(v_fst_5765_);
v___x_5810_ = lean_box(0);
v_isShared_5811_ = v_isSharedCheck_5850_;
goto v_resetjp_5809_;
}
v_resetjp_5809_:
{
lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5815_; 
v___x_5812_ = lean_array_fget(v_array_5788_, v_start_5789_);
v___x_5813_ = lean_nat_add(v_start_5789_, v___x_5792_);
lean_dec(v_start_5789_);
if (v_isShared_5811_ == 0)
{
lean_ctor_set(v___x_5810_, 1, v___x_5813_);
v___x_5815_ = v___x_5810_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_array_5788_);
lean_ctor_set(v_reuseFailAlloc_5849_, 1, v___x_5813_);
lean_ctor_set(v_reuseFailAlloc_5849_, 2, v_stop_5790_);
v___x_5815_ = v_reuseFailAlloc_5849_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
uint8_t v___x_5816_; 
v___x_5816_ = lean_unbox(v___x_5812_);
lean_dec(v___x_5812_);
if (v___x_5816_ == 0)
{
lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5822_; 
v___x_5817_ = lean_array_get_size(v_fst_5761_);
v___x_5818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5818_, 0, v___x_5817_);
v___x_5819_ = lean_array_push(v_fst_5753_, v___x_5818_);
v___x_5820_ = lean_array_push(v_fst_5761_, v___x_5791_);
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5795_);
lean_ctor_set(v___x_5767_, 0, v___x_5815_);
v___x_5822_ = v___x_5767_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v___x_5815_);
lean_ctor_set(v_reuseFailAlloc_5832_, 1, v___x_5795_);
v___x_5822_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5821_;
}
v_reusejp_5821_:
{
lean_object* v___x_5824_; 
if (v_isShared_5764_ == 0)
{
lean_ctor_set(v___x_5763_, 1, v___x_5822_);
lean_ctor_set(v___x_5763_, 0, v___x_5820_);
v___x_5824_ = v___x_5763_;
goto v_reusejp_5823_;
}
else
{
lean_object* v_reuseFailAlloc_5831_; 
v_reuseFailAlloc_5831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5831_, 0, v___x_5820_);
lean_ctor_set(v_reuseFailAlloc_5831_, 1, v___x_5822_);
v___x_5824_ = v_reuseFailAlloc_5831_;
goto v_reusejp_5823_;
}
v_reusejp_5823_:
{
lean_object* v___x_5826_; 
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 1, v___x_5824_);
v___x_5826_ = v___x_5759_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5830_; 
v_reuseFailAlloc_5830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5830_, 0, v_fst_5757_);
lean_ctor_set(v_reuseFailAlloc_5830_, 1, v___x_5824_);
v___x_5826_ = v_reuseFailAlloc_5830_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_5828_; 
if (v_isShared_5756_ == 0)
{
lean_ctor_set(v___x_5755_, 1, v___x_5826_);
lean_ctor_set(v___x_5755_, 0, v___x_5819_);
v___x_5828_ = v___x_5755_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v___x_5819_);
lean_ctor_set(v_reuseFailAlloc_5829_, 1, v___x_5826_);
v___x_5828_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
v_a_5744_ = v___x_5828_;
goto v___jp_5743_;
}
}
}
}
}
else
{
lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5838_; 
v___x_5833_ = lean_box(0);
v___x_5834_ = lean_array_push(v_fst_5753_, v___x_5833_);
v___x_5835_ = l_Lean_Expr_fvarId_x21(v___x_5791_);
lean_dec(v___x_5791_);
v___x_5836_ = lean_array_push(v_fst_5757_, v___x_5835_);
if (v_isShared_5768_ == 0)
{
lean_ctor_set(v___x_5767_, 1, v___x_5795_);
lean_ctor_set(v___x_5767_, 0, v___x_5815_);
v___x_5838_ = v___x_5767_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v___x_5815_);
lean_ctor_set(v_reuseFailAlloc_5848_, 1, v___x_5795_);
v___x_5838_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
lean_object* v___x_5840_; 
if (v_isShared_5764_ == 0)
{
lean_ctor_set(v___x_5763_, 1, v___x_5838_);
v___x_5840_ = v___x_5763_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_fst_5761_);
lean_ctor_set(v_reuseFailAlloc_5847_, 1, v___x_5838_);
v___x_5840_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
lean_object* v___x_5842_; 
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 1, v___x_5840_);
lean_ctor_set(v___x_5759_, 0, v___x_5836_);
v___x_5842_ = v___x_5759_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5836_);
lean_ctor_set(v_reuseFailAlloc_5846_, 1, v___x_5840_);
v___x_5842_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
lean_object* v___x_5844_; 
if (v_isShared_5756_ == 0)
{
lean_ctor_set(v___x_5755_, 1, v___x_5842_);
lean_ctor_set(v___x_5755_, 0, v___x_5834_);
v___x_5844_ = v___x_5755_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v___x_5834_);
lean_ctor_set(v_reuseFailAlloc_5845_, 1, v___x_5842_);
v___x_5844_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
v_a_5744_ = v___x_5844_;
goto v___jp_5743_;
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
v___jp_5743_:
{
lean_object* v___x_5745_; lean_object* v___x_5746_; 
v___x_5745_ = lean_unsigned_to_nat(1u);
v___x_5746_ = lean_nat_add(v_a_5741_, v___x_5745_);
lean_dec(v_a_5741_);
v_a_5741_ = v___x_5746_;
v_b_5742_ = v_a_5744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5867_, lean_object* v_a_5868_, lean_object* v_b_5869_){
_start:
{
lean_object* v_res_5870_; 
v_res_5870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5867_, v_a_5868_, v_b_5869_);
lean_dec(v_upperBound_5867_);
return v_res_5870_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5871_, size_t v_i_5872_, size_t v_stop_5873_){
_start:
{
uint8_t v___x_5874_; 
v___x_5874_ = lean_usize_dec_eq(v_i_5872_, v_stop_5873_);
if (v___x_5874_ == 0)
{
lean_object* v___x_5875_; uint8_t v___x_5876_; 
v___x_5875_ = lean_array_uget_borrowed(v_as_5871_, v_i_5872_);
v___x_5876_ = l_Lean_Expr_isFVar(v___x_5875_);
if (v___x_5876_ == 0)
{
uint8_t v___x_5877_; 
v___x_5877_ = 1;
return v___x_5877_;
}
else
{
size_t v___x_5878_; size_t v___x_5879_; 
v___x_5878_ = ((size_t)1ULL);
v___x_5879_ = lean_usize_add(v_i_5872_, v___x_5878_);
v_i_5872_ = v___x_5879_;
goto _start;
}
}
else
{
uint8_t v___x_5881_; 
v___x_5881_ = 0;
return v___x_5881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5882_, lean_object* v_i_5883_, lean_object* v_stop_5884_){
_start:
{
size_t v_i_boxed_5885_; size_t v_stop_boxed_5886_; uint8_t v_res_5887_; lean_object* v_r_5888_; 
v_i_boxed_5885_ = lean_unbox_usize(v_i_5883_);
lean_dec(v_i_5883_);
v_stop_boxed_5886_ = lean_unbox_usize(v_stop_5884_);
lean_dec(v_stop_5884_);
v_res_5887_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5882_, v_i_boxed_5885_, v_stop_boxed_5886_);
lean_dec_ref(v_as_5882_);
v_r_5888_ = lean_box(v_res_5887_);
return v_r_5888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5889_, size_t v_sz_5890_, size_t v_i_5891_, lean_object* v_bs_5892_){
_start:
{
uint8_t v___x_5893_; 
v___x_5893_ = lean_usize_dec_lt(v_i_5891_, v_sz_5890_);
if (v___x_5893_ == 0)
{
return v_bs_5892_;
}
else
{
lean_object* v_v_5894_; lean_object* v___x_5895_; lean_object* v_bs_x27_5896_; lean_object* v___y_5898_; 
v_v_5894_ = lean_array_uget(v_bs_5892_, v_i_5891_);
v___x_5895_ = lean_unsigned_to_nat(0u);
v_bs_x27_5896_ = lean_array_uset(v_bs_5892_, v_i_5891_, v___x_5895_);
if (lean_obj_tag(v_v_5894_) == 0)
{
v___y_5898_ = v_v_5894_;
goto v___jp_5897_;
}
else
{
lean_object* v_val_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
v_val_5903_ = lean_ctor_get(v_v_5894_, 0);
lean_inc(v_val_5903_);
lean_dec_ref_known(v_v_5894_, 1);
v___x_5904_ = lean_box(0);
v___x_5905_ = lean_array_get_borrowed(v___x_5904_, v___x_5889_, v_val_5903_);
lean_dec(v_val_5903_);
lean_inc(v___x_5905_);
v___y_5898_ = v___x_5905_;
goto v___jp_5897_;
}
v___jp_5897_:
{
size_t v___x_5899_; size_t v___x_5900_; lean_object* v___x_5901_; 
v___x_5899_ = ((size_t)1ULL);
v___x_5900_ = lean_usize_add(v_i_5891_, v___x_5899_);
v___x_5901_ = lean_array_uset(v_bs_x27_5896_, v_i_5891_, v___y_5898_);
v_i_5891_ = v___x_5900_;
v_bs_5892_ = v___x_5901_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5906_, lean_object* v_sz_5907_, lean_object* v_i_5908_, lean_object* v_bs_5909_){
_start:
{
size_t v_sz_boxed_5910_; size_t v_i_boxed_5911_; lean_object* v_res_5912_; 
v_sz_boxed_5910_ = lean_unbox_usize(v_sz_5907_);
lean_dec(v_sz_5907_);
v_i_boxed_5911_ = lean_unbox_usize(v_i_5908_);
lean_dec(v_i_5908_);
v_res_5912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5906_, v_sz_boxed_5910_, v_i_boxed_5911_, v_bs_5909_);
lean_dec_ref(v___x_5906_);
return v_res_5912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5913_, size_t v_sz_5914_, size_t v_i_5915_, lean_object* v_bs_5916_){
_start:
{
uint8_t v___x_5917_; 
v___x_5917_ = lean_usize_dec_lt(v_i_5915_, v_sz_5914_);
if (v___x_5917_ == 0)
{
return v_bs_5916_;
}
else
{
lean_object* v_v_5918_; lean_object* v___x_5919_; lean_object* v_bs_x27_5920_; size_t v_sz_5921_; size_t v___x_5922_; lean_object* v___x_5923_; size_t v___x_5924_; size_t v___x_5925_; lean_object* v___x_5926_; 
v_v_5918_ = lean_array_uget(v_bs_5916_, v_i_5915_);
v___x_5919_ = lean_unsigned_to_nat(0u);
v_bs_x27_5920_ = lean_array_uset(v_bs_5916_, v_i_5915_, v___x_5919_);
v_sz_5921_ = lean_array_size(v_v_5918_);
v___x_5922_ = ((size_t)0ULL);
v___x_5923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5913_, v_sz_5921_, v___x_5922_, v_v_5918_);
v___x_5924_ = ((size_t)1ULL);
v___x_5925_ = lean_usize_add(v_i_5915_, v___x_5924_);
v___x_5926_ = lean_array_uset(v_bs_x27_5920_, v_i_5915_, v___x_5923_);
v_i_5915_ = v___x_5925_;
v_bs_5916_ = v___x_5926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5928_, lean_object* v_sz_5929_, lean_object* v_i_5930_, lean_object* v_bs_5931_){
_start:
{
size_t v_sz_boxed_5932_; size_t v_i_boxed_5933_; lean_object* v_res_5934_; 
v_sz_boxed_5932_ = lean_unbox_usize(v_sz_5929_);
lean_dec(v_sz_5929_);
v_i_boxed_5933_ = lean_unbox_usize(v_i_5930_);
lean_dec(v_i_5930_);
v_res_5934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5928_, v_sz_boxed_5932_, v_i_boxed_5933_, v_bs_5931_);
lean_dec_ref(v___x_5928_);
return v_res_5934_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; 
v___x_5937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5938_ = lean_unsigned_to_nat(6u);
v___x_5939_ = lean_unsigned_to_nat(463u);
v___x_5940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5941_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5942_ = l_mkPanicMessageWithDecl(v___x_5941_, v___x_5940_, v___x_5939_, v___x_5938_, v___x_5937_);
return v___x_5942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5943_, lean_object* v___x_5944_, lean_object* v___x_5945_, lean_object* v_as_5946_, size_t v_sz_5947_, size_t v_i_5948_, lean_object* v_b_5949_){
_start:
{
lean_object* v_a_5951_; uint8_t v___x_5955_; 
v___x_5955_ = lean_usize_dec_lt(v_i_5948_, v_sz_5947_);
if (v___x_5955_ == 0)
{
return v_b_5949_;
}
else
{
lean_object* v_a_5956_; lean_object* v___x_5957_; uint8_t v___x_5958_; 
v_a_5956_ = lean_array_uget_borrowed(v_as_5946_, v_i_5948_);
v___x_5957_ = lean_array_get_size(v___x_5943_);
v___x_5958_ = lean_nat_dec_lt(v_a_5956_, v___x_5957_);
if (v___x_5958_ == 0)
{
lean_object* v___x_5959_; lean_object* v___x_5960_; 
lean_dec_ref(v_b_5949_);
v___x_5959_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5960_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5959_);
if (lean_obj_tag(v___x_5960_) == 0)
{
lean_object* v_a_5961_; 
v_a_5961_ = lean_ctor_get(v___x_5960_, 0);
lean_inc(v_a_5961_);
lean_dec_ref_known(v___x_5960_, 1);
return v_a_5961_;
}
else
{
lean_object* v_a_5962_; 
v_a_5962_ = lean_ctor_get(v___x_5960_, 0);
lean_inc(v_a_5962_);
lean_dec_ref_known(v___x_5960_, 1);
v_a_5951_ = v_a_5962_;
goto v___jp_5950_;
}
}
else
{
lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5963_ = lean_box(0);
v___x_5964_ = lean_array_get_borrowed(v___x_5963_, v___x_5943_, v_a_5956_);
if (lean_obj_tag(v___x_5964_) == 1)
{
lean_object* v_val_5965_; uint8_t v_changed_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; 
v_val_5965_ = lean_ctor_get(v___x_5964_, 0);
v_changed_5966_ = lean_nat_dec_eq(v___x_5944_, v___x_5945_);
v___x_5967_ = lean_box(v_changed_5966_);
v___x_5968_ = lean_array_set(v_b_5949_, v_val_5965_, v___x_5967_);
v_a_5951_ = v___x_5968_;
goto v___jp_5950_;
}
else
{
v_a_5951_ = v_b_5949_;
goto v___jp_5950_;
}
}
}
v___jp_5950_:
{
size_t v___x_5952_; size_t v___x_5953_; 
v___x_5952_ = ((size_t)1ULL);
v___x_5953_ = lean_usize_add(v_i_5948_, v___x_5952_);
v_i_5948_ = v___x_5953_;
v_b_5949_ = v_a_5951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5969_, lean_object* v___x_5970_, lean_object* v___x_5971_, lean_object* v_as_5972_, lean_object* v_sz_5973_, lean_object* v_i_5974_, lean_object* v_b_5975_){
_start:
{
size_t v_sz_boxed_5976_; size_t v_i_boxed_5977_; lean_object* v_res_5978_; 
v_sz_boxed_5976_ = lean_unbox_usize(v_sz_5973_);
lean_dec(v_sz_5973_);
v_i_boxed_5977_ = lean_unbox_usize(v_i_5974_);
lean_dec(v_i_5974_);
v_res_5978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5969_, v___x_5970_, v___x_5971_, v_as_5972_, v_sz_boxed_5976_, v_i_boxed_5977_, v_b_5975_);
lean_dec_ref(v_as_5972_);
lean_dec(v___x_5971_);
lean_dec(v___x_5970_);
lean_dec_ref(v___x_5969_);
return v_res_5978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5979_, lean_object* v___x_5980_, lean_object* v___x_5981_, lean_object* v_a_5982_, lean_object* v_b_5983_){
_start:
{
uint8_t v___x_5984_; 
v___x_5984_ = lean_nat_dec_lt(v_a_5982_, v_upperBound_5979_);
if (v___x_5984_ == 0)
{
lean_dec(v_a_5982_);
return v_b_5983_;
}
else
{
lean_object* v_snd_5985_; lean_object* v_snd_5986_; lean_object* v_fst_5987_; lean_object* v___x_5989_; uint8_t v_isShared_5990_; uint8_t v_isSharedCheck_6053_; 
v_snd_5985_ = lean_ctor_get(v_b_5983_, 1);
lean_inc(v_snd_5985_);
v_snd_5986_ = lean_ctor_get(v_snd_5985_, 1);
lean_inc(v_snd_5986_);
v_fst_5987_ = lean_ctor_get(v_b_5983_, 0);
v_isSharedCheck_6053_ = !lean_is_exclusive(v_b_5983_);
if (v_isSharedCheck_6053_ == 0)
{
lean_object* v_unused_6054_; 
v_unused_6054_ = lean_ctor_get(v_b_5983_, 1);
lean_dec(v_unused_6054_);
v___x_5989_ = v_b_5983_;
v_isShared_5990_ = v_isSharedCheck_6053_;
goto v_resetjp_5988_;
}
else
{
lean_inc(v_fst_5987_);
lean_dec(v_b_5983_);
v___x_5989_ = lean_box(0);
v_isShared_5990_ = v_isSharedCheck_6053_;
goto v_resetjp_5988_;
}
v_resetjp_5988_:
{
lean_object* v_fst_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_6051_; 
v_fst_5991_ = lean_ctor_get(v_snd_5985_, 0);
v_isSharedCheck_6051_ = !lean_is_exclusive(v_snd_5985_);
if (v_isSharedCheck_6051_ == 0)
{
lean_object* v_unused_6052_; 
v_unused_6052_ = lean_ctor_get(v_snd_5985_, 1);
lean_dec(v_unused_6052_);
v___x_5993_ = v_snd_5985_;
v_isShared_5994_ = v_isSharedCheck_6051_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_fst_5991_);
lean_dec(v_snd_5985_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_6051_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v_array_5995_; lean_object* v_start_5996_; lean_object* v_stop_5997_; uint8_t v___x_5998_; 
v_array_5995_ = lean_ctor_get(v_snd_5986_, 0);
v_start_5996_ = lean_ctor_get(v_snd_5986_, 1);
v_stop_5997_ = lean_ctor_get(v_snd_5986_, 2);
v___x_5998_ = lean_nat_dec_lt(v_start_5996_, v_stop_5997_);
if (v___x_5998_ == 0)
{
lean_object* v___x_6000_; 
lean_dec(v_a_5982_);
if (v_isShared_5994_ == 0)
{
v___x_6000_ = v___x_5993_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_fst_5991_);
lean_ctor_set(v_reuseFailAlloc_6004_, 1, v_snd_5986_);
v___x_6000_ = v_reuseFailAlloc_6004_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
lean_object* v___x_6002_; 
if (v_isShared_5990_ == 0)
{
lean_ctor_set(v___x_5989_, 1, v___x_6000_);
v___x_6002_ = v___x_5989_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v_fst_5987_);
lean_ctor_set(v_reuseFailAlloc_6003_, 1, v___x_6000_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
return v___x_6002_;
}
}
}
else
{
lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6047_; 
lean_inc(v_stop_5997_);
lean_inc(v_start_5996_);
lean_inc_ref(v_array_5995_);
v_isSharedCheck_6047_ = !lean_is_exclusive(v_snd_5986_);
if (v_isSharedCheck_6047_ == 0)
{
lean_object* v_unused_6048_; lean_object* v_unused_6049_; lean_object* v_unused_6050_; 
v_unused_6048_ = lean_ctor_get(v_snd_5986_, 2);
lean_dec(v_unused_6048_);
v_unused_6049_ = lean_ctor_get(v_snd_5986_, 1);
lean_dec(v_unused_6049_);
v_unused_6050_ = lean_ctor_get(v_snd_5986_, 0);
lean_dec(v_unused_6050_);
v___x_6006_ = v_snd_5986_;
v_isShared_6007_ = v_isSharedCheck_6047_;
goto v_resetjp_6005_;
}
else
{
lean_dec(v_snd_5986_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6047_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v_array_6008_; lean_object* v_start_6009_; lean_object* v_stop_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6015_; 
v_array_6008_ = lean_ctor_get(v_fst_5991_, 0);
v_start_6009_ = lean_ctor_get(v_fst_5991_, 1);
v_stop_6010_ = lean_ctor_get(v_fst_5991_, 2);
v___x_6011_ = lean_array_fget(v_array_5995_, v_start_5996_);
v___x_6012_ = lean_unsigned_to_nat(1u);
v___x_6013_ = lean_nat_add(v_start_5996_, v___x_6012_);
lean_dec(v_start_5996_);
if (v_isShared_6007_ == 0)
{
lean_ctor_set(v___x_6006_, 1, v___x_6013_);
v___x_6015_ = v___x_6006_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_array_5995_);
lean_ctor_set(v_reuseFailAlloc_6046_, 1, v___x_6013_);
lean_ctor_set(v_reuseFailAlloc_6046_, 2, v_stop_5997_);
v___x_6015_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
uint8_t v___x_6016_; 
v___x_6016_ = lean_nat_dec_lt(v_start_6009_, v_stop_6010_);
if (v___x_6016_ == 0)
{
lean_object* v___x_6018_; 
lean_dec(v___x_6011_);
lean_dec(v_a_5982_);
if (v_isShared_5994_ == 0)
{
lean_ctor_set(v___x_5993_, 1, v___x_6015_);
v___x_6018_ = v___x_5993_;
goto v_reusejp_6017_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_fst_5991_);
lean_ctor_set(v_reuseFailAlloc_6022_, 1, v___x_6015_);
v___x_6018_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6017_;
}
v_reusejp_6017_:
{
lean_object* v___x_6020_; 
if (v_isShared_5990_ == 0)
{
lean_ctor_set(v___x_5989_, 1, v___x_6018_);
v___x_6020_ = v___x_5989_;
goto v_reusejp_6019_;
}
else
{
lean_object* v_reuseFailAlloc_6021_; 
v_reuseFailAlloc_6021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6021_, 0, v_fst_5987_);
lean_ctor_set(v_reuseFailAlloc_6021_, 1, v___x_6018_);
v___x_6020_ = v_reuseFailAlloc_6021_;
goto v_reusejp_6019_;
}
v_reusejp_6019_:
{
return v___x_6020_;
}
}
}
else
{
lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6042_; 
lean_inc(v_stop_6010_);
lean_inc(v_start_6009_);
lean_inc_ref(v_array_6008_);
v_isSharedCheck_6042_ = !lean_is_exclusive(v_fst_5991_);
if (v_isSharedCheck_6042_ == 0)
{
lean_object* v_unused_6043_; lean_object* v_unused_6044_; lean_object* v_unused_6045_; 
v_unused_6043_ = lean_ctor_get(v_fst_5991_, 2);
lean_dec(v_unused_6043_);
v_unused_6044_ = lean_ctor_get(v_fst_5991_, 1);
lean_dec(v_unused_6044_);
v_unused_6045_ = lean_ctor_get(v_fst_5991_, 0);
lean_dec(v_unused_6045_);
v___x_6024_ = v_fst_5991_;
v_isShared_6025_ = v_isSharedCheck_6042_;
goto v_resetjp_6023_;
}
else
{
lean_dec(v_fst_5991_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6042_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6029_; 
v___x_6026_ = lean_array_fget(v_array_6008_, v_start_6009_);
v___x_6027_ = lean_nat_add(v_start_6009_, v___x_6012_);
lean_dec(v_start_6009_);
if (v_isShared_6025_ == 0)
{
lean_ctor_set(v___x_6024_, 1, v___x_6027_);
v___x_6029_ = v___x_6024_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6041_; 
v_reuseFailAlloc_6041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6041_, 0, v_array_6008_);
lean_ctor_set(v_reuseFailAlloc_6041_, 1, v___x_6027_);
lean_ctor_set(v_reuseFailAlloc_6041_, 2, v_stop_6010_);
v___x_6029_ = v_reuseFailAlloc_6041_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
size_t v_sz_6030_; size_t v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6034_; 
v_sz_6030_ = lean_array_size(v___x_6026_);
v___x_6031_ = ((size_t)0ULL);
v___x_6032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_6011_, v___x_5980_, v___x_5981_, v___x_6026_, v_sz_6030_, v___x_6031_, v_fst_5987_);
lean_dec(v___x_6026_);
lean_dec(v___x_6011_);
if (v_isShared_5994_ == 0)
{
lean_ctor_set(v___x_5993_, 1, v___x_6015_);
lean_ctor_set(v___x_5993_, 0, v___x_6029_);
v___x_6034_ = v___x_5993_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6040_; 
v_reuseFailAlloc_6040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6040_, 0, v___x_6029_);
lean_ctor_set(v_reuseFailAlloc_6040_, 1, v___x_6015_);
v___x_6034_ = v_reuseFailAlloc_6040_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
lean_object* v___x_6036_; 
if (v_isShared_5990_ == 0)
{
lean_ctor_set(v___x_5989_, 1, v___x_6034_);
lean_ctor_set(v___x_5989_, 0, v___x_6032_);
v___x_6036_ = v___x_5989_;
goto v_reusejp_6035_;
}
else
{
lean_object* v_reuseFailAlloc_6039_; 
v_reuseFailAlloc_6039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6039_, 0, v___x_6032_);
lean_ctor_set(v_reuseFailAlloc_6039_, 1, v___x_6034_);
v___x_6036_ = v_reuseFailAlloc_6039_;
goto v_reusejp_6035_;
}
v_reusejp_6035_:
{
lean_object* v___x_6037_; 
v___x_6037_ = lean_nat_add(v_a_5982_, v___x_6012_);
lean_dec(v_a_5982_);
v_a_5982_ = v___x_6037_;
v_b_5983_ = v___x_6036_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6055_, lean_object* v___x_6056_, lean_object* v___x_6057_, lean_object* v_a_6058_, lean_object* v_b_6059_){
_start:
{
lean_object* v_res_6060_; 
v_res_6060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6055_, v___x_6056_, v___x_6057_, v_a_6058_, v_b_6059_);
lean_dec(v___x_6057_);
lean_dec(v___x_6056_);
lean_dec(v_upperBound_6055_);
return v_res_6060_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; 
v___x_6062_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6063_ = lean_unsigned_to_nat(2u);
v___x_6064_ = lean_unsigned_to_nat(457u);
v___x_6065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6066_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6067_ = l_mkPanicMessageWithDecl(v___x_6066_, v___x_6065_, v___x_6064_, v___x_6063_, v___x_6062_);
return v___x_6067_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6069_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6070_ = lean_unsigned_to_nat(2u);
v___x_6071_ = lean_unsigned_to_nat(458u);
v___x_6072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6073_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6074_ = l_mkPanicMessageWithDecl(v___x_6073_, v___x_6072_, v___x_6071_, v___x_6070_, v___x_6069_);
return v___x_6074_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; 
v___x_6076_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6077_ = lean_unsigned_to_nat(2u);
v___x_6078_ = lean_unsigned_to_nat(456u);
v___x_6079_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6080_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6081_ = l_mkPanicMessageWithDecl(v___x_6080_, v___x_6079_, v___x_6078_, v___x_6077_, v___x_6076_);
return v___x_6081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6082_, lean_object* v_xs_6083_, lean_object* v_toErase_6084_){
_start:
{
lean_object* v___x_6085_; lean_object* v___x_6086_; uint8_t v___x_6170_; 
v___x_6085_ = lean_unsigned_to_nat(0u);
v___x_6086_ = lean_array_get_size(v_xs_6083_);
v___x_6170_ = lean_nat_dec_lt(v___x_6085_, v___x_6086_);
if (v___x_6170_ == 0)
{
goto v___jp_6087_;
}
else
{
if (v___x_6170_ == 0)
{
goto v___jp_6087_;
}
else
{
size_t v___x_6171_; size_t v___x_6172_; uint8_t v___x_6173_; 
v___x_6171_ = ((size_t)0ULL);
v___x_6172_ = lean_usize_of_nat(v___x_6086_);
v___x_6173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6083_, v___x_6171_, v___x_6172_);
if (v___x_6173_ == 0)
{
goto v___jp_6087_;
}
else
{
lean_object* v___x_6174_; lean_object* v___x_6175_; 
lean_dec_ref(v_toErase_6084_);
lean_dec_ref(v_xs_6083_);
lean_dec_ref(v_fixedParamPerms_6082_);
v___x_6174_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6175_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6174_);
return v___x_6175_;
}
}
}
v___jp_6087_:
{
lean_object* v_numFixed_6088_; lean_object* v_perms_6089_; lean_object* v_revDeps_6090_; uint8_t v___x_6091_; 
v_numFixed_6088_ = lean_ctor_get(v_fixedParamPerms_6082_, 0);
v_perms_6089_ = lean_ctor_get(v_fixedParamPerms_6082_, 1);
lean_inc_ref(v_perms_6089_);
v_revDeps_6090_ = lean_ctor_get(v_fixedParamPerms_6082_, 2);
lean_inc_ref(v_revDeps_6090_);
v___x_6091_ = lean_nat_dec_eq(v_numFixed_6088_, v___x_6086_);
if (v___x_6091_ == 0)
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
lean_dec_ref(v_revDeps_6090_);
lean_dec_ref(v_perms_6089_);
lean_dec_ref(v_toErase_6084_);
lean_dec_ref(v_xs_6083_);
lean_dec_ref(v_fixedParamPerms_6082_);
v___x_6092_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6093_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6092_);
return v___x_6093_;
}
else
{
lean_object* v___x_6094_; lean_object* v___x_6095_; uint8_t v_changed_6096_; 
v___x_6094_ = lean_array_get_size(v_toErase_6084_);
v___x_6095_ = lean_array_get_size(v_perms_6089_);
v_changed_6096_ = lean_nat_dec_eq(v___x_6094_, v___x_6095_);
if (v_changed_6096_ == 0)
{
lean_object* v___x_6097_; lean_object* v___x_6098_; 
lean_dec_ref(v_revDeps_6090_);
lean_dec_ref(v_perms_6089_);
lean_dec_ref(v_toErase_6084_);
lean_dec_ref(v_xs_6083_);
lean_dec_ref(v_fixedParamPerms_6082_);
v___x_6097_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6098_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6097_);
return v___x_6098_;
}
else
{
uint8_t v_changed_6099_; lean_object* v___x_6100_; lean_object* v_mask_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v_fst_6107_; lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6168_; 
v_changed_6099_ = 0;
v___x_6100_ = lean_box(v_changed_6099_);
lean_inc(v_numFixed_6088_);
v_mask_6101_ = lean_mk_array(v_numFixed_6088_, v___x_6100_);
v___x_6102_ = l_Array_toSubarray___redArg(v_toErase_6084_, v___x_6085_, v___x_6094_);
lean_inc_ref(v_perms_6089_);
v___x_6103_ = l_Array_toSubarray___redArg(v_perms_6089_, v___x_6085_, v___x_6095_);
v___x_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6102_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
v___x_6105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6105_, 0, v_mask_6101_);
lean_ctor_set(v___x_6105_, 1, v___x_6104_);
v___x_6106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6094_, v___x_6094_, v___x_6095_, v___x_6085_, v___x_6105_);
v_fst_6107_ = lean_ctor_get(v___x_6106_, 0);
v_isSharedCheck_6168_ = !lean_is_exclusive(v___x_6106_);
if (v_isSharedCheck_6168_ == 0)
{
lean_object* v_unused_6169_; 
v_unused_6169_ = lean_ctor_get(v___x_6106_, 1);
lean_dec(v_unused_6169_);
v___x_6109_ = v___x_6106_;
v_isShared_6110_ = v_isSharedCheck_6168_;
goto v_resetjp_6108_;
}
else
{
lean_inc(v_fst_6107_);
lean_dec(v___x_6106_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6168_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v___x_6111_; lean_object* v___x_6113_; 
v___x_6111_ = lean_box(v_changed_6096_);
if (v_isShared_6110_ == 0)
{
lean_ctor_set(v___x_6109_, 1, v___x_6111_);
v___x_6113_ = v___x_6109_;
goto v_reusejp_6112_;
}
else
{
lean_object* v_reuseFailAlloc_6167_; 
v_reuseFailAlloc_6167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6167_, 0, v_fst_6107_);
lean_ctor_set(v_reuseFailAlloc_6167_, 1, v___x_6111_);
v___x_6113_ = v_reuseFailAlloc_6167_;
goto v_reusejp_6112_;
}
v_reusejp_6112_:
{
lean_object* v___x_6114_; lean_object* v___x_6116_; uint8_t v_isShared_6117_; uint8_t v_isSharedCheck_6163_; 
v___x_6114_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6095_, v_perms_6089_, v___x_6094_, v_fixedParamPerms_6082_, v___x_6113_);
v_isSharedCheck_6163_ = !lean_is_exclusive(v_fixedParamPerms_6082_);
if (v_isSharedCheck_6163_ == 0)
{
lean_object* v_unused_6164_; lean_object* v_unused_6165_; lean_object* v_unused_6166_; 
v_unused_6164_ = lean_ctor_get(v_fixedParamPerms_6082_, 2);
lean_dec(v_unused_6164_);
v_unused_6165_ = lean_ctor_get(v_fixedParamPerms_6082_, 1);
lean_dec(v_unused_6165_);
v_unused_6166_ = lean_ctor_get(v_fixedParamPerms_6082_, 0);
lean_dec(v_unused_6166_);
v___x_6116_ = v_fixedParamPerms_6082_;
v_isShared_6117_ = v_isSharedCheck_6163_;
goto v_resetjp_6115_;
}
else
{
lean_dec(v_fixedParamPerms_6082_);
v___x_6116_ = lean_box(0);
v_isShared_6117_ = v_isSharedCheck_6163_;
goto v_resetjp_6115_;
}
v_resetjp_6115_:
{
lean_object* v_fst_6118_; lean_object* v___x_6120_; uint8_t v_isShared_6121_; uint8_t v_isSharedCheck_6161_; 
v_fst_6118_ = lean_ctor_get(v___x_6114_, 0);
v_isSharedCheck_6161_ = !lean_is_exclusive(v___x_6114_);
if (v_isSharedCheck_6161_ == 0)
{
lean_object* v_unused_6162_; 
v_unused_6162_ = lean_ctor_get(v___x_6114_, 1);
lean_dec(v_unused_6162_);
v___x_6120_ = v___x_6114_;
v_isShared_6121_ = v_isSharedCheck_6161_;
goto v_resetjp_6119_;
}
else
{
lean_inc(v_fst_6118_);
lean_dec(v___x_6114_);
v___x_6120_ = lean_box(0);
v_isShared_6121_ = v_isSharedCheck_6161_;
goto v_resetjp_6119_;
}
v_resetjp_6119_:
{
lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6127_; 
v___x_6122_ = lean_array_get_size(v_fst_6118_);
v___x_6123_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6124_ = l_Array_toSubarray___redArg(v_fst_6118_, v___x_6085_, v___x_6122_);
v___x_6125_ = l_Array_toSubarray___redArg(v_xs_6083_, v___x_6085_, v___x_6086_);
if (v_isShared_6121_ == 0)
{
lean_ctor_set(v___x_6120_, 1, v___x_6125_);
lean_ctor_set(v___x_6120_, 0, v___x_6124_);
v___x_6127_ = v___x_6120_;
goto v_reusejp_6126_;
}
else
{
lean_object* v_reuseFailAlloc_6160_; 
v_reuseFailAlloc_6160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6160_, 0, v___x_6124_);
lean_ctor_set(v_reuseFailAlloc_6160_, 1, v___x_6125_);
v___x_6127_ = v_reuseFailAlloc_6160_;
goto v_reusejp_6126_;
}
v_reusejp_6126_:
{
lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v_snd_6132_; lean_object* v_snd_6133_; lean_object* v_fst_6134_; lean_object* v_fst_6135_; lean_object* v___x_6137_; uint8_t v_isShared_6138_; uint8_t v_isSharedCheck_6158_; 
v___x_6128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6128_, 0, v___x_6123_);
lean_ctor_set(v___x_6128_, 1, v___x_6127_);
v___x_6129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6123_);
lean_ctor_set(v___x_6129_, 1, v___x_6128_);
v___x_6130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6123_);
lean_ctor_set(v___x_6130_, 1, v___x_6129_);
v___x_6131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6122_, v___x_6085_, v___x_6130_);
v_snd_6132_ = lean_ctor_get(v___x_6131_, 1);
lean_inc(v_snd_6132_);
v_snd_6133_ = lean_ctor_get(v_snd_6132_, 1);
lean_inc(v_snd_6133_);
v_fst_6134_ = lean_ctor_get(v___x_6131_, 0);
lean_inc(v_fst_6134_);
lean_dec_ref(v___x_6131_);
v_fst_6135_ = lean_ctor_get(v_snd_6132_, 0);
v_isSharedCheck_6158_ = !lean_is_exclusive(v_snd_6132_);
if (v_isSharedCheck_6158_ == 0)
{
lean_object* v_unused_6159_; 
v_unused_6159_ = lean_ctor_get(v_snd_6132_, 1);
lean_dec(v_unused_6159_);
v___x_6137_ = v_snd_6132_;
v_isShared_6138_ = v_isSharedCheck_6158_;
goto v_resetjp_6136_;
}
else
{
lean_inc(v_fst_6135_);
lean_dec(v_snd_6132_);
v___x_6137_ = lean_box(0);
v_isShared_6138_ = v_isSharedCheck_6158_;
goto v_resetjp_6136_;
}
v_resetjp_6136_:
{
lean_object* v_fst_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6156_; 
v_fst_6139_ = lean_ctor_get(v_snd_6133_, 0);
v_isSharedCheck_6156_ = !lean_is_exclusive(v_snd_6133_);
if (v_isSharedCheck_6156_ == 0)
{
lean_object* v_unused_6157_; 
v_unused_6157_ = lean_ctor_get(v_snd_6133_, 1);
lean_dec(v_unused_6157_);
v___x_6141_ = v_snd_6133_;
v_isShared_6142_ = v_isSharedCheck_6156_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_fst_6139_);
lean_dec(v_snd_6133_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6156_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v___x_6143_; size_t v_sz_6144_; size_t v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6148_; 
v___x_6143_ = lean_array_get_size(v_fst_6139_);
v_sz_6144_ = lean_array_size(v_perms_6089_);
v___x_6145_ = ((size_t)0ULL);
v___x_6146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6134_, v_sz_6144_, v___x_6145_, v_perms_6089_);
lean_dec(v_fst_6134_);
if (v_isShared_6117_ == 0)
{
lean_ctor_set(v___x_6116_, 1, v___x_6146_);
lean_ctor_set(v___x_6116_, 0, v___x_6143_);
v___x_6148_ = v___x_6116_;
goto v_reusejp_6147_;
}
else
{
lean_object* v_reuseFailAlloc_6155_; 
v_reuseFailAlloc_6155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6155_, 0, v___x_6143_);
lean_ctor_set(v_reuseFailAlloc_6155_, 1, v___x_6146_);
lean_ctor_set(v_reuseFailAlloc_6155_, 2, v_revDeps_6090_);
v___x_6148_ = v_reuseFailAlloc_6155_;
goto v_reusejp_6147_;
}
v_reusejp_6147_:
{
lean_object* v___x_6150_; 
if (v_isShared_6142_ == 0)
{
lean_ctor_set(v___x_6141_, 1, v_fst_6135_);
v___x_6150_ = v___x_6141_;
goto v_reusejp_6149_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_fst_6139_);
lean_ctor_set(v_reuseFailAlloc_6154_, 1, v_fst_6135_);
v___x_6150_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6149_;
}
v_reusejp_6149_:
{
lean_object* v___x_6152_; 
if (v_isShared_6138_ == 0)
{
lean_ctor_set(v___x_6137_, 1, v___x_6150_);
lean_ctor_set(v___x_6137_, 0, v___x_6148_);
v___x_6152_ = v___x_6137_;
goto v_reusejp_6151_;
}
else
{
lean_object* v_reuseFailAlloc_6153_; 
v_reuseFailAlloc_6153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6153_, 0, v___x_6148_);
lean_ctor_set(v_reuseFailAlloc_6153_, 1, v___x_6150_);
v___x_6152_ = v_reuseFailAlloc_6153_;
goto v_reusejp_6151_;
}
v_reusejp_6151_:
{
return v___x_6152_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6176_, lean_object* v___x_6177_, lean_object* v_fixedParamPerms_6178_, lean_object* v_next_6179_, lean_object* v___x_6180_, lean_object* v___x_6181_, lean_object* v_inst_6182_, lean_object* v_R_6183_, lean_object* v_a_6184_, lean_object* v_b_6185_, lean_object* v_c_6186_){
_start:
{
lean_object* v___x_6187_; 
v___x_6187_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6176_, v___x_6177_, v_fixedParamPerms_6178_, v_next_6179_, v___x_6180_, v___x_6181_, v_a_6184_, v_b_6185_);
return v___x_6187_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6188_, lean_object* v___x_6189_, lean_object* v_fixedParamPerms_6190_, lean_object* v_next_6191_, lean_object* v___x_6192_, lean_object* v___x_6193_, lean_object* v_inst_6194_, lean_object* v_R_6195_, lean_object* v_a_6196_, lean_object* v_b_6197_, lean_object* v_c_6198_){
_start:
{
lean_object* v_res_6199_; 
v_res_6199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6188_, v___x_6189_, v_fixedParamPerms_6190_, v_next_6191_, v___x_6192_, v___x_6193_, v_inst_6194_, v_R_6195_, v_a_6196_, v_b_6197_, v_c_6198_);
lean_dec(v___x_6193_);
lean_dec(v___x_6192_);
lean_dec(v_next_6191_);
lean_dec_ref(v_fixedParamPerms_6190_);
lean_dec_ref(v___x_6189_);
lean_dec(v_upperBound_6188_);
return v_res_6199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6200_, lean_object* v___x_6201_, lean_object* v___x_6202_, lean_object* v___x_6203_, lean_object* v_fixedParamPerms_6204_, lean_object* v_inst_6205_, lean_object* v_R_6206_, lean_object* v_a_6207_, lean_object* v_b_6208_, lean_object* v_c_6209_){
_start:
{
lean_object* v___x_6210_; 
v___x_6210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6200_, v___x_6201_, v___x_6202_, v___x_6203_, v_fixedParamPerms_6204_, v_a_6207_, v_b_6208_);
return v___x_6210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6211_, lean_object* v___x_6212_, lean_object* v___x_6213_, lean_object* v___x_6214_, lean_object* v_fixedParamPerms_6215_, lean_object* v_inst_6216_, lean_object* v_R_6217_, lean_object* v_a_6218_, lean_object* v_b_6219_, lean_object* v_c_6220_){
_start:
{
lean_object* v_res_6221_; 
v_res_6221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6211_, v___x_6212_, v___x_6213_, v___x_6214_, v_fixedParamPerms_6215_, v_inst_6216_, v_R_6217_, v_a_6218_, v_b_6219_, v_c_6220_);
lean_dec(v_a_6218_);
lean_dec_ref(v_fixedParamPerms_6215_);
lean_dec(v___x_6214_);
lean_dec(v___x_6213_);
lean_dec_ref(v___x_6212_);
lean_dec(v_upperBound_6211_);
return v_res_6221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6222_, lean_object* v___x_6223_, lean_object* v___x_6224_, lean_object* v_fixedParamPerms_6225_, lean_object* v_inst_6226_, lean_object* v_a_6227_){
_start:
{
lean_object* v___x_6228_; 
v___x_6228_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6222_, v___x_6223_, v___x_6224_, v_fixedParamPerms_6225_, v_a_6227_);
return v___x_6228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6229_, lean_object* v___x_6230_, lean_object* v___x_6231_, lean_object* v_fixedParamPerms_6232_, lean_object* v_inst_6233_, lean_object* v_a_6234_){
_start:
{
lean_object* v_res_6235_; 
v_res_6235_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6229_, v___x_6230_, v___x_6231_, v_fixedParamPerms_6232_, v_inst_6233_, v_a_6234_);
lean_dec_ref(v_fixedParamPerms_6232_);
lean_dec(v___x_6231_);
lean_dec_ref(v___x_6230_);
lean_dec(v___x_6229_);
return v_res_6235_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6236_, lean_object* v_inst_6237_, lean_object* v_R_6238_, lean_object* v_a_6239_, lean_object* v_b_6240_, lean_object* v_c_6241_){
_start:
{
lean_object* v___x_6242_; 
v___x_6242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6236_, v_a_6239_, v_b_6240_);
return v___x_6242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6243_, lean_object* v_inst_6244_, lean_object* v_R_6245_, lean_object* v_a_6246_, lean_object* v_b_6247_, lean_object* v_c_6248_){
_start:
{
lean_object* v_res_6249_; 
v_res_6249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6243_, v_inst_6244_, v_R_6245_, v_a_6246_, v_b_6247_, v_c_6248_);
lean_dec(v_upperBound_6243_);
return v_res_6249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6250_, lean_object* v___x_6251_, lean_object* v___x_6252_, lean_object* v_inst_6253_, lean_object* v_R_6254_, lean_object* v_a_6255_, lean_object* v_b_6256_, lean_object* v_c_6257_){
_start:
{
lean_object* v___x_6258_; 
v___x_6258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6250_, v___x_6251_, v___x_6252_, v_a_6255_, v_b_6256_);
return v___x_6258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6259_, lean_object* v___x_6260_, lean_object* v___x_6261_, lean_object* v_inst_6262_, lean_object* v_R_6263_, lean_object* v_a_6264_, lean_object* v_b_6265_, lean_object* v_c_6266_){
_start:
{
lean_object* v_res_6267_; 
v_res_6267_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6259_, v___x_6260_, v___x_6261_, v_inst_6262_, v_R_6263_, v_a_6264_, v_b_6265_, v_c_6266_);
lean_dec(v___x_6261_);
lean_dec(v___x_6260_);
lean_dec(v_upperBound_6259_);
return v_res_6267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7(lean_object* v_upperBound_6268_, lean_object* v___x_6269_, lean_object* v_fixedParamPerms_6270_, lean_object* v___x_6271_, lean_object* v___x_6272_, lean_object* v_inst_6273_, lean_object* v_R_6274_, lean_object* v_a_6275_, lean_object* v_b_6276_, lean_object* v_c_6277_){
_start:
{
lean_object* v___x_6278_; 
v___x_6278_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___redArg(v_upperBound_6268_, v___x_6269_, v_fixedParamPerms_6270_, v___x_6271_, v___x_6272_, v_a_6275_, v_b_6276_);
return v___x_6278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7___boxed(lean_object* v_upperBound_6279_, lean_object* v___x_6280_, lean_object* v_fixedParamPerms_6281_, lean_object* v___x_6282_, lean_object* v___x_6283_, lean_object* v_inst_6284_, lean_object* v_R_6285_, lean_object* v_a_6286_, lean_object* v_b_6287_, lean_object* v_c_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7_spec__7(v_upperBound_6279_, v___x_6280_, v_fixedParamPerms_6281_, v___x_6282_, v___x_6283_, v_inst_6284_, v_R_6285_, v_a_6286_, v_b_6287_, v_c_6288_);
lean_dec(v___x_6283_);
lean_dec(v___x_6282_);
lean_dec_ref(v_fixedParamPerms_6281_);
lean_dec_ref(v___x_6280_);
lean_dec(v_upperBound_6279_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6347_; uint8_t v___x_6348_; lean_object* v___x_6349_; lean_object* v___x_6350_; 
v___x_6347_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6348_ = 0;
v___x_6349_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6350_ = l_Lean_registerTraceClass(v___x_6347_, v___x_6348_, v___x_6349_);
return v___x_6350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6351_){
_start:
{
lean_object* v_res_6352_; 
v_res_6352_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6352_;
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
