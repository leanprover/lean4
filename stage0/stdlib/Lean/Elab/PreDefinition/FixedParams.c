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
lean_inc_ref(v_revDeps_200_);
v___x_201_ = lean_array_get(v___x_192_, v_revDeps_200_, v_funIdx_183_);
lean_dec_ref(v_revDeps_200_);
v___x_202_ = lean_array_get(v___x_192_, v___x_201_, v_paramIdx_184_);
lean_dec(v_paramIdx_184_);
lean_dec(v___x_201_);
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
lean_object* v___f_1008_; lean_object* v___x_27166__overap_1009_; lean_object* v___x_1010_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_27166__overap_1009_ = lean_panic_fn_borrowed(v___f_1008_, v_msg_1002_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1010_ = lean_apply_5(v___x_27166__overap_1009_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, lean_box(0));
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
lean_object* v___x_1081_; lean_object* v_env_1082_; lean_object* v___x_1083_; lean_object* v_toCold_1084_; lean_object* v_mctx_1085_; lean_object* v_lctx_1086_; lean_object* v_options_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1081_ = lean_st_ref_get(v___y_1079_);
v_env_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc_ref(v_env_1082_);
lean_dec(v___x_1081_);
v___x_1083_ = lean_st_ref_get(v___y_1077_);
v_toCold_1084_ = lean_ctor_get(v___y_1078_, 0);
v_mctx_1085_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_mctx_1085_);
lean_dec(v___x_1083_);
v_lctx_1086_ = lean_ctor_get(v___y_1076_, 2);
v_options_1087_ = lean_ctor_get(v_toCold_1084_, 2);
lean_inc_ref(v_options_1087_);
lean_inc_ref(v_lctx_1086_);
v___x_1088_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1088_, 0, v_env_1082_);
lean_ctor_set(v___x_1088_, 1, v_mctx_1085_);
lean_ctor_set(v___x_1088_, 2, v_lctx_1086_);
lean_ctor_set(v___x_1088_, 3, v_options_1087_);
v___x_1089_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_msgData_1075_);
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
v_ref_1110_ = lean_ctor_get(v___y_1107_, 2);
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
lean_object* v___x_1134_; lean_object* v___x_1135_; double v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_1137_ = 0;
v___x_1138_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_1139_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1139_, 0, v_cls_1103_);
lean_ctor_set(v___x_1139_, 1, v___x_1135_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
lean_ctor_set_float(v___x_1139_, sizeof(void*)*3, v___x_1136_);
lean_ctor_set_float(v___x_1139_, sizeof(void*)*3 + 8, v___x_1136_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*3 + 16, v___x_1137_);
v___x_1140_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_1141_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v_a_1112_);
lean_ctor_set(v___x_1141_, 2, v___x_1140_);
lean_inc(v_ref_1110_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_ref_1110_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_PersistentArray_push___redArg(v_traces_1130_, v___x_1142_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1143_);
v___x_1145_ = v___x_1132_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1143_);
lean_ctor_set_uint64(v_reuseFailAlloc_1153_, sizeof(void*)*1, v_tid_1129_);
v___x_1145_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 4, v___x_1145_);
v___x_1147_ = v___x_1127_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_env_1118_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_nextMacroScope_1119_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_ngen_1120_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_auxDeclNGen_1121_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1152_, 5, v_cache_1122_);
lean_ctor_set(v_reuseFailAlloc_1152_, 6, v_messages_1123_);
lean_ctor_set(v_reuseFailAlloc_1152_, 7, v_infoState_1124_);
lean_ctor_set(v_reuseFailAlloc_1152_, 8, v_snapshotTasks_1125_);
v___x_1147_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_st_ref_put(v___y_1108_, v___x_1147_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1134_);
v___x_1150_ = v___x_1114_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1134_);
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
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_nbuckets_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1223_ = lean_array_get_size(v_data_1222_);
v___x_1224_ = lean_unsigned_to_nat(2u);
v_nbuckets_1225_ = lean_nat_mul(v___x_1223_, v___x_1224_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_mk_array(v_nbuckets_1225_, v___x_1227_);
v___x_1229_ = lean_array_propagate_mark(v_data_1222_, v___x_1228_);
v___x_1230_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v___x_1226_, v_data_1222_, v___x_1229_);
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
v___x_1313_ = lean_box(0);
v___x_1314_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1312_, v_e_1309_, v_a_1310_);
v___x_1315_ = lean_st_ref_put(v_a_1308_, v___x_1314_);
return v___x_1313_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_1535_, lean_object* v_pre_1536_, lean_object* v_post_1537_, lean_object* v_usedLetOnly_1538_, lean_object* v_skipConstInApp_1539_, lean_object* v_skipInstances_1540_, lean_object* v_body_1541_, lean_object* v_x_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v_usedLetOnly_boxed_1549_; uint8_t v_skipConstInApp_boxed_1550_; uint8_t v_skipInstances_boxed_1551_; lean_object* v_res_1552_; 
v_usedLetOnly_boxed_1549_ = lean_unbox(v_usedLetOnly_1538_);
v_skipConstInApp_boxed_1550_ = lean_unbox(v_skipConstInApp_1539_);
v_skipInstances_boxed_1551_ = lean_unbox(v_skipInstances_1540_);
v_res_1552_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_1535_, v_pre_1536_, v_post_1537_, v_usedLetOnly_boxed_1549_, v_skipConstInApp_boxed_1550_, v_skipInstances_boxed_1551_, v_body_1541_, v_x_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1556_, lean_object* v_pre_1557_, lean_object* v_post_1558_, uint8_t v_usedLetOnly_1559_, uint8_t v_skipConstInApp_1560_, uint8_t v_skipInstances_1561_, lean_object* v_body_1562_, lean_object* v_x_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = lean_array_push(v_fvars_1556_, v_x_1563_);
v___x_1571_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1557_, v_post_1558_, v_usedLetOnly_1559_, v_skipConstInApp_1560_, v_skipInstances_1561_, v___x_1570_, v_body_1562_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1572_, lean_object* v_pre_1573_, lean_object* v_post_1574_, lean_object* v_usedLetOnly_1575_, lean_object* v_skipConstInApp_1576_, lean_object* v_skipInstances_1577_, lean_object* v_body_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v_usedLetOnly_boxed_1586_; uint8_t v_skipConstInApp_boxed_1587_; uint8_t v_skipInstances_boxed_1588_; lean_object* v_res_1589_; 
v_usedLetOnly_boxed_1586_ = lean_unbox(v_usedLetOnly_1575_);
v_skipConstInApp_boxed_1587_ = lean_unbox(v_skipConstInApp_1576_);
v_skipInstances_boxed_1588_ = lean_unbox(v_skipInstances_1577_);
v_res_1589_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1572_, v_pre_1573_, v_post_1574_, v_usedLetOnly_boxed_1586_, v_skipConstInApp_boxed_1587_, v_skipInstances_boxed_1588_, v_body_1578_, v_x_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1590_, lean_object* v_post_1591_, uint8_t v_usedLetOnly_1592_, uint8_t v_skipConstInApp_1593_, uint8_t v_skipInstances_1594_, lean_object* v_e_1595_, lean_object* v_a_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
lean_inc_ref(v_post_1591_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc(v___y_1598_);
lean_inc_ref(v___y_1597_);
lean_inc_ref(v_e_1595_);
v___x_1602_ = lean_apply_6(v_post_1591_, v_e_1595_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, lean_box(0));
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1621_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1621_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1621_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
switch(lean_obj_tag(v_a_1603_))
{
case 0:
{
lean_object* v_e_1607_; lean_object* v___x_1609_; 
lean_dec_ref(v_e_1595_);
lean_dec_ref(v_post_1591_);
lean_dec_ref(v_pre_1590_);
v_e_1607_ = lean_ctor_get(v_a_1603_, 0);
lean_inc_ref(v_e_1607_);
lean_dec_ref_known(v_a_1603_, 1);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v_e_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_e_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
case 1:
{
lean_object* v_e_1611_; lean_object* v___x_1612_; 
lean_del_object(v___x_1605_);
lean_dec_ref(v_e_1595_);
v_e_1611_ = lean_ctor_get(v_a_1603_, 0);
lean_inc_ref(v_e_1611_);
lean_dec_ref_known(v_a_1603_, 1);
v___x_1612_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1590_, v_post_1591_, v_usedLetOnly_1592_, v_skipConstInApp_1593_, v_skipInstances_1594_, v_e_1611_, v_a_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
return v___x_1612_;
}
default: 
{
lean_object* v_e_x3f_1613_; 
lean_dec_ref(v_post_1591_);
lean_dec_ref(v_pre_1590_);
v_e_x3f_1613_ = lean_ctor_get(v_a_1603_, 0);
lean_inc(v_e_x3f_1613_);
lean_dec_ref_known(v_a_1603_, 1);
if (lean_obj_tag(v_e_x3f_1613_) == 0)
{
lean_object* v___x_1615_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v_e_1595_);
v___x_1615_ = v___x_1605_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_e_1595_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
else
{
lean_object* v_val_1617_; lean_object* v___x_1619_; 
lean_dec_ref(v_e_1595_);
v_val_1617_ = lean_ctor_get(v_e_x3f_1613_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v_e_x3f_1613_, 1);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v_val_1617_);
v___x_1619_ = v___x_1605_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_val_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_e_1595_);
lean_dec_ref(v_post_1591_);
lean_dec_ref(v_pre_1590_);
v_a_1622_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1602_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1602_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1630_, lean_object* v_post_1631_, uint8_t v_usedLetOnly_1632_, uint8_t v_skipConstInApp_1633_, uint8_t v_skipInstances_1634_, lean_object* v_fvars_1635_, lean_object* v_e_1636_, lean_object* v_a_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
if (lean_obj_tag(v_e_1636_) == 6)
{
lean_object* v_binderName_1643_; lean_object* v_binderType_1644_; lean_object* v_body_1645_; uint8_t v_binderInfo_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_binderName_1643_ = lean_ctor_get(v_e_1636_, 0);
lean_inc(v_binderName_1643_);
v_binderType_1644_ = lean_ctor_get(v_e_1636_, 1);
lean_inc_ref(v_binderType_1644_);
v_body_1645_ = lean_ctor_get(v_e_1636_, 2);
lean_inc_ref(v_body_1645_);
v_binderInfo_1646_ = lean_ctor_get_uint8(v_e_1636_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1636_, 3);
v___x_1647_ = lean_box(v_usedLetOnly_1632_);
v___x_1648_ = lean_box(v_skipConstInApp_1633_);
v___x_1649_ = lean_box(v_skipInstances_1634_);
lean_inc_ref(v_post_1631_);
lean_inc_ref(v_pre_1630_);
lean_inc_ref(v_fvars_1635_);
v___f_1650_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1650_, 0, v_fvars_1635_);
lean_closure_set(v___f_1650_, 1, v_pre_1630_);
lean_closure_set(v___f_1650_, 2, v_post_1631_);
lean_closure_set(v___f_1650_, 3, v___x_1647_);
lean_closure_set(v___f_1650_, 4, v___x_1648_);
lean_closure_set(v___f_1650_, 5, v___x_1649_);
lean_closure_set(v___f_1650_, 6, v_body_1645_);
v___x_1651_ = lean_expr_instantiate_rev(v_binderType_1644_, v_fvars_1635_);
lean_dec_ref(v_fvars_1635_);
lean_dec_ref(v_binderType_1644_);
v___x_1652_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v___x_1651_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = 0;
v___x_1655_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1643_, v_binderInfo_1646_, v_a_1653_, v___f_1650_, v___x_1654_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1655_;
}
else
{
lean_dec_ref(v___f_1650_);
lean_dec(v_binderName_1643_);
return v___x_1652_;
}
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_expr_instantiate_rev(v_e_1636_, v_fvars_1635_);
lean_dec_ref(v_e_1636_);
lean_inc_ref(v_post_1631_);
lean_inc_ref(v_pre_1630_);
v___x_1657_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v___x_1656_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; uint8_t v___x_1659_; uint8_t v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = 0;
v___x_1660_ = 1;
v___x_1661_ = 1;
v___x_1662_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1635_, v_a_1658_, v___x_1659_, v_usedLetOnly_1632_, v___x_1659_, v___x_1660_, v___x_1661_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
lean_dec_ref(v_fvars_1635_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1664_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
v___x_1664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1630_, v_post_1631_, v_usedLetOnly_1632_, v_skipConstInApp_1633_, v_skipInstances_1634_, v_a_1663_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v___x_1664_;
}
else
{
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
return v___x_1662_;
}
}
else
{
lean_dec_ref(v_fvars_1635_);
lean_dec_ref(v_post_1631_);
lean_dec_ref(v_pre_1630_);
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1665_, lean_object* v_pre_1666_, lean_object* v_post_1667_, uint8_t v_usedLetOnly_1668_, uint8_t v_skipConstInApp_1669_, uint8_t v_skipInstances_1670_, lean_object* v_body_1671_, lean_object* v_x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_array_push(v_fvars_1665_, v_x_1672_);
v___x_1680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1666_, v_post_1667_, v_usedLetOnly_1668_, v_skipConstInApp_1669_, v_skipInstances_1670_, v___x_1679_, v_body_1671_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1681_, lean_object* v_pre_1682_, lean_object* v_post_1683_, lean_object* v_usedLetOnly_1684_, lean_object* v_skipConstInApp_1685_, lean_object* v_skipInstances_1686_, lean_object* v_body_1687_, lean_object* v_x_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v_usedLetOnly_boxed_1695_; uint8_t v_skipConstInApp_boxed_1696_; uint8_t v_skipInstances_boxed_1697_; lean_object* v_res_1698_; 
v_usedLetOnly_boxed_1695_ = lean_unbox(v_usedLetOnly_1684_);
v_skipConstInApp_boxed_1696_ = lean_unbox(v_skipConstInApp_1685_);
v_skipInstances_boxed_1697_ = lean_unbox(v_skipInstances_1686_);
v_res_1698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1681_, v_pre_1682_, v_post_1683_, v_usedLetOnly_boxed_1695_, v_skipConstInApp_boxed_1696_, v_skipInstances_boxed_1697_, v_body_1687_, v_x_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1699_, lean_object* v_post_1700_, uint8_t v_usedLetOnly_1701_, uint8_t v_skipConstInApp_1702_, uint8_t v_skipInstances_1703_, lean_object* v_fvars_1704_, lean_object* v_e_1705_, lean_object* v_a_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
if (lean_obj_tag(v_e_1705_) == 8)
{
lean_object* v_declName_1712_; lean_object* v_type_1713_; lean_object* v_value_1714_; lean_object* v_body_1715_; uint8_t v_nondep_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___f_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_declName_1712_ = lean_ctor_get(v_e_1705_, 0);
lean_inc(v_declName_1712_);
v_type_1713_ = lean_ctor_get(v_e_1705_, 1);
lean_inc_ref(v_type_1713_);
v_value_1714_ = lean_ctor_get(v_e_1705_, 2);
lean_inc_ref(v_value_1714_);
v_body_1715_ = lean_ctor_get(v_e_1705_, 3);
lean_inc_ref(v_body_1715_);
v_nondep_1716_ = lean_ctor_get_uint8(v_e_1705_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1705_, 4);
v___x_1717_ = lean_box(v_usedLetOnly_1701_);
v___x_1718_ = lean_box(v_skipConstInApp_1702_);
v___x_1719_ = lean_box(v_skipInstances_1703_);
lean_inc_ref_n(v_post_1700_, 2);
lean_inc_ref_n(v_pre_1699_, 2);
lean_inc_ref(v_fvars_1704_);
v___f_1720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1720_, 0, v_fvars_1704_);
lean_closure_set(v___f_1720_, 1, v_pre_1699_);
lean_closure_set(v___f_1720_, 2, v_post_1700_);
lean_closure_set(v___f_1720_, 3, v___x_1717_);
lean_closure_set(v___f_1720_, 4, v___x_1718_);
lean_closure_set(v___f_1720_, 5, v___x_1719_);
lean_closure_set(v___f_1720_, 6, v_body_1715_);
v___x_1721_ = lean_expr_instantiate_rev(v_type_1713_, v_fvars_1704_);
lean_dec_ref(v_type_1713_);
v___x_1722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1699_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v___x_1721_, v_a_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = lean_expr_instantiate_rev(v_value_1714_, v_fvars_1704_);
lean_dec_ref(v_fvars_1704_);
lean_dec_ref(v_value_1714_);
v___x_1725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1699_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v___x_1724_, v_a_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = 0;
v___x_1728_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1712_, v_a_1723_, v_a_1726_, v___f_1720_, v_nondep_1716_, v___x_1727_, v_a_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1728_;
}
else
{
lean_dec(v_a_1723_);
lean_dec_ref(v___f_1720_);
lean_dec(v_declName_1712_);
return v___x_1725_;
}
}
else
{
lean_dec_ref(v___f_1720_);
lean_dec_ref(v_value_1714_);
lean_dec(v_declName_1712_);
lean_dec_ref(v_fvars_1704_);
lean_dec_ref(v_post_1700_);
lean_dec_ref(v_pre_1699_);
return v___x_1722_;
}
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_expr_instantiate_rev(v_e_1705_, v_fvars_1704_);
lean_dec_ref(v_e_1705_);
lean_inc_ref(v_post_1700_);
lean_inc_ref(v_pre_1699_);
v___x_1730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1699_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v___x_1729_, v_a_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; uint8_t v___x_1732_; uint8_t v___x_1733_; lean_object* v___x_1734_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = 0;
v___x_1733_ = 1;
v___x_1734_ = l_Lean_Meta_mkLetFVars(v_fvars_1704_, v_a_1731_, v_usedLetOnly_1701_, v___x_1732_, v___x_1733_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec_ref(v_fvars_1704_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1699_, v_post_1700_, v_usedLetOnly_1701_, v_skipConstInApp_1702_, v_skipInstances_1703_, v_a_1735_, v_a_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1736_;
}
else
{
lean_dec_ref(v_post_1700_);
lean_dec_ref(v_pre_1699_);
return v___x_1734_;
}
}
else
{
lean_dec_ref(v_fvars_1704_);
lean_dec_ref(v_post_1700_);
lean_dec_ref(v_pre_1699_);
return v___x_1730_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1737_; lean_object* v_dummy_1738_; 
v___x_1737_ = lean_box(0);
v_dummy_1738_ = l_Lean_Expr_sort___override(v___x_1737_);
return v_dummy_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1739_, lean_object* v_post_1740_, uint8_t v_usedLetOnly_1741_, uint8_t v_skipConstInApp_1742_, uint8_t v_skipInstances_1743_, size_t v_sz_1744_, size_t v_i_1745_, lean_object* v_bs_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_lt(v_i_1745_, v_sz_1744_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
lean_dec_ref(v_post_1740_);
lean_dec_ref(v_pre_1739_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_bs_1746_);
return v___x_1754_;
}
else
{
lean_object* v_v_1755_; lean_object* v___x_1756_; lean_object* v_bs_x27_1757_; lean_object* v___x_1758_; 
v_v_1755_ = lean_array_uget(v_bs_1746_, v_i_1745_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v_bs_x27_1757_ = lean_array_uset(v_bs_1746_, v_i_1745_, v___x_1756_);
lean_inc_ref(v_post_1740_);
lean_inc_ref(v_pre_1739_);
v___x_1758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1739_, v_post_1740_, v_usedLetOnly_1741_, v_skipConstInApp_1742_, v_skipInstances_1743_, v_v_1755_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_add(v_i_1745_, v___x_1760_);
v___x_1762_ = lean_array_uset(v_bs_x27_1757_, v_i_1745_, v_a_1759_);
v_i_1745_ = v___x_1761_;
v_bs_1746_ = v___x_1762_;
goto _start;
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_bs_x27_1757_);
lean_dec_ref(v_post_1740_);
lean_dec_ref(v_pre_1739_);
v_a_1764_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1758_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1758_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1772_, lean_object* v_post_1773_, uint8_t v_usedLetOnly_1774_, uint8_t v_skipConstInApp_1775_, uint8_t v_skipInstances_1776_, lean_object* v___x_1777_, lean_object* v___y_1778_, lean_object* v_b_1779_, lean_object* v_a_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1772_, v_post_1773_, v_usedLetOnly_1774_, v_skipConstInApp_1775_, v_skipInstances_1776_, v___x_1777_, v___y_1778_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1796_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1796_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1796_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1791_ = lean_array_fset(v_b_1779_, v_a_1780_, v_a_1787_);
v___x_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1792_);
v___x_1794_ = v___x_1789_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec_ref(v_b_1779_);
v_a_1797_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1786_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1786_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1805_, lean_object* v_post_1806_, lean_object* v_usedLetOnly_1807_, lean_object* v_skipConstInApp_1808_, lean_object* v_skipInstances_1809_, lean_object* v___x_1810_, lean_object* v___y_1811_, lean_object* v_b_1812_, lean_object* v_a_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v_usedLetOnly_boxed_1819_; uint8_t v_skipConstInApp_boxed_1820_; uint8_t v_skipInstances_boxed_1821_; lean_object* v_res_1822_; 
v_usedLetOnly_boxed_1819_ = lean_unbox(v_usedLetOnly_1807_);
v_skipConstInApp_boxed_1820_ = lean_unbox(v_skipConstInApp_1808_);
v_skipInstances_boxed_1821_ = lean_unbox(v_skipInstances_1809_);
v_res_1822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1805_, v_post_1806_, v_usedLetOnly_boxed_1819_, v_skipConstInApp_boxed_1820_, v_skipInstances_boxed_1821_, v___x_1810_, v___y_1811_, v_b_1812_, v_a_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v_a_1813_);
lean_dec(v___y_1811_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1823_, lean_object* v___x_1824_, lean_object* v_pre_1825_, lean_object* v_post_1826_, uint8_t v_usedLetOnly_1827_, uint8_t v_skipConstInApp_1828_, uint8_t v_skipInstances_1829_, lean_object* v_a_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___y_1839_; uint8_t v___x_1862_; 
v___x_1862_ = lean_nat_dec_lt(v_a_1830_, v_upperBound_1823_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; 
lean_dec(v_a_1830_);
lean_dec_ref(v_post_1826_);
lean_dec_ref(v_pre_1825_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_b_1831_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1864_ = lean_array_fget_borrowed(v_b_1831_, v_a_1830_);
v___x_1865_ = lean_array_get_size(v___x_1824_);
v___x_1866_ = lean_nat_dec_lt(v_a_1830_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___f_1870_; 
lean_inc(v___x_1864_);
v___x_1867_ = lean_box(v_usedLetOnly_1827_);
v___x_1868_ = lean_box(v_skipConstInApp_1828_);
v___x_1869_ = lean_box(v_skipInstances_1829_);
lean_inc(v_a_1830_);
lean_inc(v___y_1832_);
lean_inc_ref(v_post_1826_);
lean_inc_ref(v_pre_1825_);
v___f_1870_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1870_, 0, v_pre_1825_);
lean_closure_set(v___f_1870_, 1, v_post_1826_);
lean_closure_set(v___f_1870_, 2, v___x_1867_);
lean_closure_set(v___f_1870_, 3, v___x_1868_);
lean_closure_set(v___f_1870_, 4, v___x_1869_);
lean_closure_set(v___f_1870_, 5, v___x_1864_);
lean_closure_set(v___f_1870_, 6, v___y_1832_);
lean_closure_set(v___f_1870_, 7, v_b_1831_);
lean_closure_set(v___f_1870_, 8, v_a_1830_);
v___y_1839_ = v___f_1870_;
goto v___jp_1838_;
}
else
{
lean_object* v___x_1871_; uint8_t v_isInstance_1872_; 
v___x_1871_ = lean_array_fget_borrowed(v___x_1824_, v_a_1830_);
v_isInstance_1872_ = lean_ctor_get_uint8(v___x_1871_, sizeof(void*)*1 + 4);
if (v_isInstance_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___f_1876_; 
lean_inc(v___x_1864_);
v___x_1873_ = lean_box(v_usedLetOnly_1827_);
v___x_1874_ = lean_box(v_skipConstInApp_1828_);
v___x_1875_ = lean_box(v_skipInstances_1829_);
lean_inc(v_a_1830_);
lean_inc(v___y_1832_);
lean_inc_ref(v_post_1826_);
lean_inc_ref(v_pre_1825_);
v___f_1876_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1876_, 0, v_pre_1825_);
lean_closure_set(v___f_1876_, 1, v_post_1826_);
lean_closure_set(v___f_1876_, 2, v___x_1873_);
lean_closure_set(v___f_1876_, 3, v___x_1874_);
lean_closure_set(v___f_1876_, 4, v___x_1875_);
lean_closure_set(v___f_1876_, 5, v___x_1864_);
lean_closure_set(v___f_1876_, 6, v___y_1832_);
lean_closure_set(v___f_1876_, 7, v_b_1831_);
lean_closure_set(v___f_1876_, 8, v_a_1830_);
v___y_1839_ = v___f_1876_;
goto v___jp_1838_;
}
else
{
lean_object* v___x_1877_; lean_object* v___f_1878_; 
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v_b_1831_);
v___f_1878_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1878_, 0, v___x_1877_);
v___y_1839_ = v___f_1878_;
goto v___jp_1838_;
}
}
}
v___jp_1838_:
{
lean_object* v___x_1840_; 
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
v___x_1840_ = lean_apply_5(v___y_1839_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, lean_box(0));
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1853_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1853_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1853_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
if (lean_obj_tag(v_a_1841_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1847_; 
lean_dec(v_a_1830_);
lean_dec_ref(v_post_1826_);
lean_dec_ref(v_pre_1825_);
v_a_1845_ = lean_ctor_get(v_a_1841_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v_a_1841_, 1);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v_a_1845_);
v___x_1847_ = v___x_1843_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1843_);
v_a_1849_ = lean_ctor_get(v_a_1841_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v_a_1841_, 1);
v___x_1850_ = lean_unsigned_to_nat(1u);
v___x_1851_ = lean_nat_add(v_a_1830_, v___x_1850_);
lean_dec(v_a_1830_);
v_a_1830_ = v___x_1851_;
v_b_1831_ = v_a_1849_;
goto _start;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_a_1830_);
lean_dec_ref(v_post_1826_);
lean_dec_ref(v_pre_1825_);
v_a_1854_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1840_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1840_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1879_, lean_object* v_pre_1880_, lean_object* v_post_1881_, uint8_t v_usedLetOnly_1882_, uint8_t v_skipConstInApp_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_f_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; 
if (lean_obj_tag(v_x_1884_) == 5)
{
lean_object* v_fn_1942_; lean_object* v_arg_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_fn_1942_ = lean_ctor_get(v_x_1884_, 0);
lean_inc_ref(v_fn_1942_);
v_arg_1943_ = lean_ctor_get(v_x_1884_, 1);
lean_inc_ref(v_arg_1943_);
lean_dec_ref_known(v_x_1884_, 2);
v___x_1944_ = lean_array_set(v_x_1885_, v_x_1886_, v_arg_1943_);
v___x_1945_ = lean_unsigned_to_nat(1u);
v___x_1946_ = lean_nat_sub(v_x_1886_, v___x_1945_);
lean_dec(v_x_1886_);
v_x_1884_ = v_fn_1942_;
v_x_1885_ = v___x_1944_;
v_x_1886_ = v___x_1946_;
goto _start;
}
else
{
lean_dec(v_x_1886_);
if (v_skipConstInApp_1883_ == 0)
{
goto v___jp_1939_;
}
else
{
uint8_t v___x_1948_; 
v___x_1948_ = l_Lean_Expr_isConst(v_x_1884_);
if (v___x_1948_ == 0)
{
goto v___jp_1939_;
}
else
{
v_f_1894_ = v_x_1884_;
v___y_1895_ = v___y_1887_;
v___y_1896_ = v___y_1888_;
v___y_1897_ = v___y_1889_;
v___y_1898_ = v___y_1890_;
v___y_1899_ = v___y_1891_;
goto v___jp_1893_;
}
}
}
v___jp_1893_:
{
if (v_skipInstances_1879_ == 0)
{
size_t v_sz_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v_sz_1900_ = lean_array_size(v_x_1885_);
v___x_1901_ = ((size_t)0ULL);
lean_inc_ref(v_post_1881_);
lean_inc_ref(v_pre_1880_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1880_, v_post_1881_, v_usedLetOnly_1882_, v_skipConstInApp_1883_, v_skipInstances_1879_, v_sz_1900_, v___x_1901_, v_x_1885_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = l_Lean_mkAppN(v_f_1894_, v_a_1903_);
lean_dec(v_a_1903_);
v___x_1905_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1880_, v_post_1881_, v_usedLetOnly_1882_, v_skipConstInApp_1883_, v_skipInstances_1879_, v___x_1904_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v___x_1905_;
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref(v_f_1894_);
lean_dec_ref(v_post_1881_);
lean_dec_ref(v_pre_1880_);
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
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_array_get_size(v_x_1885_);
lean_inc_ref(v_f_1894_);
v___x_1915_ = l_Lean_Meta_getFunInfoNArgs(v_f_1894_, v___x_1914_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v_paramInfo_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v_paramInfo_1917_ = lean_ctor_get(v_a_1916_, 0);
lean_inc_ref(v_paramInfo_1917_);
lean_dec(v_a_1916_);
v___x_1918_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1881_);
lean_inc_ref(v_pre_1880_);
v___x_1919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1914_, v_paramInfo_1917_, v_pre_1880_, v_post_1881_, v_usedLetOnly_1882_, v_skipConstInApp_1883_, v_skipInstances_1879_, v___x_1918_, v_x_1885_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec_ref(v_paramInfo_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l_Lean_mkAppN(v_f_1894_, v_a_1920_);
lean_dec(v_a_1920_);
v___x_1922_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1880_, v_post_1881_, v_usedLetOnly_1882_, v_skipConstInApp_1883_, v_skipInstances_1879_, v___x_1921_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v___x_1922_;
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v_f_1894_);
lean_dec_ref(v_post_1881_);
lean_dec_ref(v_pre_1880_);
v_a_1923_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1919_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1919_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_f_1894_);
lean_dec_ref(v_x_1885_);
lean_dec_ref(v_post_1881_);
lean_dec_ref(v_pre_1880_);
v_a_1931_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1915_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1915_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
v___jp_1939_:
{
lean_object* v___x_1940_; 
lean_inc_ref(v_post_1881_);
lean_inc_ref(v_pre_1880_);
v___x_1940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1880_, v_post_1881_, v_usedLetOnly_1882_, v_skipConstInApp_1883_, v_skipInstances_1879_, v_x_1884_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v_f_1894_ = v_a_1941_;
v___y_1895_ = v___y_1887_;
v___y_1896_ = v___y_1888_;
v___y_1897_ = v___y_1889_;
v___y_1898_ = v___y_1890_;
v___y_1899_ = v___y_1891_;
goto v___jp_1893_;
}
else
{
lean_dec_ref(v_x_1885_);
lean_dec_ref(v_post_1881_);
lean_dec_ref(v_pre_1880_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1949_, lean_object* v_pre_1950_, lean_object* v_e_1951_, lean_object* v_post_1952_, uint8_t v_usedLetOnly_1953_, uint8_t v_skipConstInApp_1954_, uint8_t v_skipInstances_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Core_checkSystem(v___x_1949_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1963_; 
lean_dec_ref_known(v___x_1962_, 1);
lean_inc_ref(v_pre_1950_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc(v___y_1958_);
lean_inc_ref(v___y_1957_);
lean_inc_ref(v_e_1951_);
v___x_1963_ = lean_apply_6(v_pre_1950_, v_e_1951_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, lean_box(0));
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_2012_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_2012_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_2012_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___y_1969_; 
switch(lean_obj_tag(v_a_1964_))
{
case 0:
{
lean_object* v_e_2004_; lean_object* v___x_2006_; 
lean_dec_ref(v_post_1952_);
lean_dec_ref(v_e_1951_);
lean_dec_ref(v_pre_1950_);
v_e_2004_ = lean_ctor_get(v_a_1964_, 0);
lean_inc_ref(v_e_2004_);
lean_dec_ref_known(v_a_1964_, 1);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_e_2004_);
v___x_2006_ = v___x_1966_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_e_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
case 1:
{
lean_object* v_e_2008_; lean_object* v___x_2009_; 
lean_del_object(v___x_1966_);
lean_dec_ref(v_e_1951_);
v_e_2008_ = lean_ctor_get(v_a_1964_, 0);
lean_inc_ref(v_e_2008_);
lean_dec_ref_known(v_a_1964_, 1);
v___x_2009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v_e_2008_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_2009_;
}
default: 
{
lean_object* v_e_x3f_2010_; 
lean_del_object(v___x_1966_);
v_e_x3f_2010_ = lean_ctor_get(v_a_1964_, 0);
lean_inc(v_e_x3f_2010_);
lean_dec_ref_known(v_a_1964_, 1);
if (lean_obj_tag(v_e_x3f_2010_) == 0)
{
v___y_1969_ = v_e_1951_;
goto v___jp_1968_;
}
else
{
lean_object* v_val_2011_; 
lean_dec_ref(v_e_1951_);
v_val_2011_ = lean_ctor_get(v_e_x3f_2010_, 0);
lean_inc(v_val_2011_);
lean_dec_ref_known(v_e_x3f_2010_, 1);
v___y_1969_ = v_val_2011_;
goto v___jp_1968_;
}
}
}
v___jp_1968_:
{
switch(lean_obj_tag(v___y_1969_))
{
case 7:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1971_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v___x_1970_, v___y_1969_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1971_;
}
case 6:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v___x_1972_, v___y_1969_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1973_;
}
case 8:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1975_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v___x_1974_, v___y_1969_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1975_;
}
case 5:
{
lean_object* v_dummy_1976_; lean_object* v_nargs_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_dummy_1976_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1977_ = l_Lean_Expr_getAppNumArgs(v___y_1969_);
lean_inc(v_nargs_1977_);
v___x_1978_ = lean_mk_array(v_nargs_1977_, v_dummy_1976_);
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_sub(v_nargs_1977_, v___x_1979_);
lean_dec(v_nargs_1977_);
v___x_1981_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1955_, v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v___y_1969_, v___x_1978_, v___x_1980_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1981_;
}
case 10:
{
lean_object* v_data_1982_; lean_object* v_expr_1983_; lean_object* v___x_1984_; 
v_data_1982_ = lean_ctor_get(v___y_1969_, 0);
v_expr_1983_ = lean_ctor_get(v___y_1969_, 1);
lean_inc_ref(v_expr_1983_);
lean_inc_ref(v_post_1952_);
lean_inc_ref(v_pre_1950_);
v___x_1984_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v_expr_1983_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; size_t v___x_1986_; size_t v___x_1987_; uint8_t v___x_1988_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = lean_ptr_addr(v_expr_1983_);
v___x_1987_ = lean_ptr_addr(v_a_1985_);
v___x_1988_ = lean_usize_dec_eq(v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_inc(v_data_1982_);
lean_dec_ref_known(v___y_1969_, 2);
v___x_1989_ = l_Lean_Expr_mdata___override(v_data_1982_, v_a_1985_);
v___x_1990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v___x_1989_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; 
lean_dec(v_a_1985_);
v___x_1991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v___y_1969_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1991_;
}
}
else
{
lean_dec_ref_known(v___y_1969_, 2);
lean_dec_ref(v_post_1952_);
lean_dec_ref(v_pre_1950_);
return v___x_1984_;
}
}
case 11:
{
lean_object* v_typeName_1992_; lean_object* v_idx_1993_; lean_object* v_struct_1994_; lean_object* v___x_1995_; 
v_typeName_1992_ = lean_ctor_get(v___y_1969_, 0);
v_idx_1993_ = lean_ctor_get(v___y_1969_, 1);
v_struct_1994_ = lean_ctor_get(v___y_1969_, 2);
lean_inc_ref(v_struct_1994_);
lean_inc_ref(v_post_1952_);
lean_inc_ref(v_pre_1950_);
v___x_1995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v_struct_1994_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; size_t v___x_1997_; size_t v___x_1998_; uint8_t v___x_1999_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = lean_ptr_addr(v_struct_1994_);
v___x_1998_ = lean_ptr_addr(v_a_1996_);
v___x_1999_ = lean_usize_dec_eq(v___x_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_inc(v_idx_1993_);
lean_inc(v_typeName_1992_);
lean_dec_ref_known(v___y_1969_, 3);
v___x_2000_ = l_Lean_Expr_proj___override(v_typeName_1992_, v_idx_1993_, v_a_1996_);
v___x_2001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v___x_2000_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_2001_;
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_a_1996_);
v___x_2002_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v___y_1969_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_2002_;
}
}
else
{
lean_dec_ref_known(v___y_1969_, 3);
lean_dec_ref(v_post_1952_);
lean_dec_ref(v_pre_1950_);
return v___x_1995_;
}
}
default: 
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1950_, v_post_1952_, v_usedLetOnly_1953_, v_skipConstInApp_1954_, v_skipInstances_1955_, v___y_1969_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_2003_;
}
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_post_1952_);
lean_dec_ref(v_e_1951_);
lean_dec_ref(v_pre_1950_);
v_a_2013_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1963_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1963_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v_post_1952_);
lean_dec_ref(v_e_1951_);
lean_dec_ref(v_pre_1950_);
v_a_2021_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1962_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_1962_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2029_, lean_object* v_pre_2030_, lean_object* v_e_2031_, lean_object* v_post_2032_, lean_object* v_usedLetOnly_2033_, lean_object* v_skipConstInApp_2034_, lean_object* v_skipInstances_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
uint8_t v_usedLetOnly_boxed_2042_; uint8_t v_skipConstInApp_boxed_2043_; uint8_t v_skipInstances_boxed_2044_; lean_object* v_res_2045_; 
v_usedLetOnly_boxed_2042_ = lean_unbox(v_usedLetOnly_2033_);
v_skipConstInApp_boxed_2043_ = lean_unbox(v_skipConstInApp_2034_);
v_skipInstances_boxed_2044_ = lean_unbox(v_skipInstances_2035_);
v_res_2045_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2029_, v_pre_2030_, v_e_2031_, v_post_2032_, v_usedLetOnly_boxed_2042_, v_skipConstInApp_boxed_2043_, v_skipInstances_boxed_2044_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2046_, lean_object* v_post_2047_, uint8_t v_usedLetOnly_2048_, uint8_t v_skipConstInApp_2049_, uint8_t v_skipInstances_2050_, lean_object* v_e_2051_, lean_object* v_a_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_inc(v_a_2052_);
v___x_2058_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2058_, 0, lean_box(0));
lean_closure_set(v___x_2058_, 1, lean_box(0));
lean_closure_set(v___x_2058_, 2, v_a_2052_);
v___x_2059_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2058_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2094_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2094_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2094_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2060_, v_e_2051_);
lean_dec(v_a_2060_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___f_2069_; lean_object* v___x_2070_; 
lean_del_object(v___x_2062_);
v___x_2065_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2066_ = lean_box(v_usedLetOnly_2048_);
v___x_2067_ = lean_box(v_skipConstInApp_2049_);
v___x_2068_ = lean_box(v_skipInstances_2050_);
lean_inc_ref(v_e_2051_);
v___f_2069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2069_, 0, v___x_2065_);
lean_closure_set(v___f_2069_, 1, v_pre_2046_);
lean_closure_set(v___f_2069_, 2, v_e_2051_);
lean_closure_set(v___f_2069_, 3, v_post_2047_);
lean_closure_set(v___f_2069_, 4, v___x_2066_);
lean_closure_set(v___f_2069_, 5, v___x_2067_);
lean_closure_set(v___f_2069_, 6, v___x_2068_);
v___x_2070_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2069_, v_a_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___f_2072_; lean_object* v___x_2073_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc_n(v_a_2071_, 2);
lean_dec_ref_known(v___x_2070_, 1);
lean_inc(v_a_2052_);
v___f_2072_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2072_, 0, v_a_2052_);
lean_closure_set(v___f_2072_, 1, v_e_2051_);
lean_closure_set(v___f_2072_, 2, v_a_2071_);
v___x_2073_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2072_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v___x_2073_, 0);
lean_dec(v_unused_2081_);
v___x_2075_ = v___x_2073_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_dec(v___x_2073_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v_a_2071_);
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2071_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v_a_2071_);
v_a_2082_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2073_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2073_);
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
else
{
lean_dec_ref(v_e_2051_);
return v___x_2070_;
}
}
else
{
lean_object* v_val_2090_; lean_object* v___x_2092_; 
lean_dec_ref(v_e_2051_);
lean_dec_ref(v_post_2047_);
lean_dec_ref(v_pre_2046_);
v_val_2090_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v___x_2064_, 1);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v_val_2090_);
v___x_2092_ = v___x_2062_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_val_2090_);
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
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_e_2051_);
lean_dec_ref(v_post_2047_);
lean_dec_ref(v_pre_2046_);
v_a_2095_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2059_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2059_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2103_, lean_object* v_post_2104_, uint8_t v_usedLetOnly_2105_, uint8_t v_skipConstInApp_2106_, uint8_t v_skipInstances_2107_, lean_object* v_fvars_2108_, lean_object* v_e_2109_, lean_object* v_a_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
if (lean_obj_tag(v_e_2109_) == 7)
{
lean_object* v_binderName_2116_; lean_object* v_binderType_2117_; lean_object* v_body_2118_; uint8_t v_binderInfo_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___f_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_binderName_2116_ = lean_ctor_get(v_e_2109_, 0);
lean_inc(v_binderName_2116_);
v_binderType_2117_ = lean_ctor_get(v_e_2109_, 1);
lean_inc_ref(v_binderType_2117_);
v_body_2118_ = lean_ctor_get(v_e_2109_, 2);
lean_inc_ref(v_body_2118_);
v_binderInfo_2119_ = lean_ctor_get_uint8(v_e_2109_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2109_, 3);
v___x_2120_ = lean_box(v_usedLetOnly_2105_);
v___x_2121_ = lean_box(v_skipConstInApp_2106_);
v___x_2122_ = lean_box(v_skipInstances_2107_);
lean_inc_ref(v_post_2104_);
lean_inc_ref(v_pre_2103_);
lean_inc_ref(v_fvars_2108_);
v___f_2123_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2123_, 0, v_fvars_2108_);
lean_closure_set(v___f_2123_, 1, v_pre_2103_);
lean_closure_set(v___f_2123_, 2, v_post_2104_);
lean_closure_set(v___f_2123_, 3, v___x_2120_);
lean_closure_set(v___f_2123_, 4, v___x_2121_);
lean_closure_set(v___f_2123_, 5, v___x_2122_);
lean_closure_set(v___f_2123_, 6, v_body_2118_);
v___x_2124_ = lean_expr_instantiate_rev(v_binderType_2117_, v_fvars_2108_);
lean_dec_ref(v_fvars_2108_);
lean_dec_ref(v_binderType_2117_);
v___x_2125_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2103_, v_post_2104_, v_usedLetOnly_2105_, v_skipConstInApp_2106_, v_skipInstances_2107_, v___x_2124_, v_a_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = 0;
v___x_2128_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2116_, v_binderInfo_2119_, v_a_2126_, v___f_2123_, v___x_2127_, v_a_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
return v___x_2128_;
}
else
{
lean_dec_ref(v___f_2123_);
lean_dec(v_binderName_2116_);
return v___x_2125_;
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
uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_a_2309_; lean_object* v___x_2310_; 
v___x_2306_ = 0;
v___x_2307_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2308_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2307_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2297_, v_post_2298_, v_usedLetOnly_2299_, v_skipConstInApp_2300_, v___x_2306_, v_input_2296_, v_a_2309_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2312_, 0, lean_box(0));
lean_closure_set(v___x_2312_, 1, lean_box(0));
lean_closure_set(v___x_2312_, 2, v_a_2309_);
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
lean_dec(v_a_2309_);
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
uint8_t v___x_2417_; lean_object* v___y_2419_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2417_ = lean_nat_dec_eq(v___x_2397_, v___x_2398_);
v___x_2433_ = lean_st_ref_get(v_val_2393_);
v___x_2434_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2396_, v_a_2402_, v___x_2433_);
lean_dec(v___x_2433_);
if (v___x_2434_ == 0)
{
v_a_2410_ = v_b_2403_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2435_; uint8_t v_foApprox_2436_; uint8_t v_ctxApprox_2437_; uint8_t v_quasiPatternApprox_2438_; uint8_t v_constApprox_2439_; uint8_t v_isDefEqStuckEx_2440_; uint8_t v_unificationHints_2441_; uint8_t v_assignSyntheticOpaque_2442_; uint8_t v_offsetCnstrs_2443_; uint8_t v_transparency_2444_; uint8_t v_etaStruct_2445_; uint8_t v_univApprox_2446_; uint8_t v_iota_2447_; uint8_t v_beta_2448_; uint8_t v_proj_2449_; uint8_t v_zeta_2450_; uint8_t v_zetaDelta_2451_; uint8_t v_zetaUnused_2452_; uint8_t v_zetaHave_2453_; uint8_t v_canUnfoldPredicateConfig_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2484_; 
v___x_2435_ = l_Lean_Meta_Context_config(v___y_2404_);
v_foApprox_2436_ = lean_ctor_get_uint8(v___x_2435_, 0);
v_ctxApprox_2437_ = lean_ctor_get_uint8(v___x_2435_, 1);
v_quasiPatternApprox_2438_ = lean_ctor_get_uint8(v___x_2435_, 2);
v_constApprox_2439_ = lean_ctor_get_uint8(v___x_2435_, 3);
v_isDefEqStuckEx_2440_ = lean_ctor_get_uint8(v___x_2435_, 4);
v_unificationHints_2441_ = lean_ctor_get_uint8(v___x_2435_, 5);
v_assignSyntheticOpaque_2442_ = lean_ctor_get_uint8(v___x_2435_, 7);
v_offsetCnstrs_2443_ = lean_ctor_get_uint8(v___x_2435_, 8);
v_transparency_2444_ = lean_ctor_get_uint8(v___x_2435_, 9);
v_etaStruct_2445_ = lean_ctor_get_uint8(v___x_2435_, 10);
v_univApprox_2446_ = lean_ctor_get_uint8(v___x_2435_, 11);
v_iota_2447_ = lean_ctor_get_uint8(v___x_2435_, 12);
v_beta_2448_ = lean_ctor_get_uint8(v___x_2435_, 13);
v_proj_2449_ = lean_ctor_get_uint8(v___x_2435_, 14);
v_zeta_2450_ = lean_ctor_get_uint8(v___x_2435_, 15);
v_zetaDelta_2451_ = lean_ctor_get_uint8(v___x_2435_, 16);
v_zetaUnused_2452_ = lean_ctor_get_uint8(v___x_2435_, 17);
v_zetaHave_2453_ = lean_ctor_get_uint8(v___x_2435_, 18);
v_canUnfoldPredicateConfig_2454_ = lean_ctor_get_uint8(v___x_2435_, 19);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2456_ = v___x_2435_;
v_isShared_2457_ = v_isSharedCheck_2484_;
goto v_resetjp_2455_;
}
else
{
lean_dec(v___x_2435_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2484_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
uint8_t v_trackZetaDelta_2458_; lean_object* v_zetaDeltaSet_2459_; lean_object* v_lctx_2460_; lean_object* v_localInstances_2461_; lean_object* v_defEqCtx_x3f_2462_; lean_object* v_synthPendingDepth_2463_; lean_object* v_customCanUnfoldPredicate_x3f_2464_; uint8_t v_univApprox_2465_; uint8_t v_inTypeClassResolution_2466_; uint8_t v_cacheInferType_2467_; uint8_t v___x_2468_; lean_object* v___x_2470_; 
v_trackZetaDelta_2458_ = lean_ctor_get_uint8(v___y_2404_, sizeof(void*)*7);
v_zetaDeltaSet_2459_ = lean_ctor_get(v___y_2404_, 1);
v_lctx_2460_ = lean_ctor_get(v___y_2404_, 2);
v_localInstances_2461_ = lean_ctor_get(v___y_2404_, 3);
v_defEqCtx_x3f_2462_ = lean_ctor_get(v___y_2404_, 4);
v_synthPendingDepth_2463_ = lean_ctor_get(v___y_2404_, 5);
v_customCanUnfoldPredicate_x3f_2464_ = lean_ctor_get(v___y_2404_, 6);
v_univApprox_2465_ = lean_ctor_get_uint8(v___y_2404_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2466_ = lean_ctor_get_uint8(v___y_2404_, sizeof(void*)*7 + 2);
v_cacheInferType_2467_ = lean_ctor_get_uint8(v___y_2404_, sizeof(void*)*7 + 3);
v___x_2468_ = 0;
if (v_isShared_2457_ == 0)
{
v___x_2470_ = v___x_2456_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 0, v_foApprox_2436_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 1, v_ctxApprox_2437_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 2, v_quasiPatternApprox_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 3, v_constApprox_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 4, v_isDefEqStuckEx_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 5, v_unificationHints_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 7, v_assignSyntheticOpaque_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 8, v_offsetCnstrs_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 9, v_transparency_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 10, v_etaStruct_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 11, v_univApprox_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 12, v_iota_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 13, v_beta_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 14, v_proj_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 15, v_zeta_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 16, v_zetaDelta_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 17, v_zetaUnused_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 18, v_zetaHave_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2483_, 19, v_canUnfoldPredicateConfig_2454_);
v___x_2470_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
uint64_t v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v_transparency_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; uint8_t v___x_2478_; 
lean_ctor_set_uint8(v___x_2470_, 6, v___x_2468_);
v___x_2471_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2470_);
v___x_2472_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set_uint64(v___x_2472_, sizeof(void*)*1, v___x_2471_);
lean_inc(v_customCanUnfoldPredicate_x3f_2464_);
lean_inc(v_synthPendingDepth_2463_);
lean_inc(v_defEqCtx_x3f_2462_);
lean_inc_ref(v_localInstances_2461_);
lean_inc_ref(v_lctx_2460_);
lean_inc(v_zetaDeltaSet_2459_);
lean_inc_ref(v___x_2472_);
v___x_2473_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v_zetaDeltaSet_2459_);
lean_ctor_set(v___x_2473_, 2, v_lctx_2460_);
lean_ctor_set(v___x_2473_, 3, v_localInstances_2461_);
lean_ctor_set(v___x_2473_, 4, v_defEqCtx_x3f_2462_);
lean_ctor_set(v___x_2473_, 5, v_synthPendingDepth_2463_);
lean_ctor_set(v___x_2473_, 6, v_customCanUnfoldPredicate_x3f_2464_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*7, v_trackZetaDelta_2458_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*7 + 1, v_univApprox_2465_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2466_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*7 + 3, v_cacheInferType_2467_);
v___x_2474_ = l_Lean_Meta_Context_config(v___x_2473_);
v_transparency_2475_ = lean_ctor_get_uint8(v___x_2474_, 9);
lean_dec_ref(v___x_2474_);
v___x_2476_ = lean_array_fget_borrowed(v_params_2400_, v_a_2402_);
v___x_2477_ = 2;
v___x_2478_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2475_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec_ref_known(v___x_2473_, 7);
v___x_2479_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2477_, v___x_2472_);
lean_inc(v_customCanUnfoldPredicate_x3f_2464_);
lean_inc(v_synthPendingDepth_2463_);
lean_inc(v_defEqCtx_x3f_2462_);
lean_inc_ref(v_localInstances_2461_);
lean_inc_ref(v_lctx_2460_);
lean_inc(v_zetaDeltaSet_2459_);
v___x_2480_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v_zetaDeltaSet_2459_);
lean_ctor_set(v___x_2480_, 2, v_lctx_2460_);
lean_ctor_set(v___x_2480_, 3, v_localInstances_2461_);
lean_ctor_set(v___x_2480_, 4, v_defEqCtx_x3f_2462_);
lean_ctor_set(v___x_2480_, 5, v_synthPendingDepth_2463_);
lean_ctor_set(v___x_2480_, 6, v_customCanUnfoldPredicate_x3f_2464_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*7, v_trackZetaDelta_2458_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*7 + 1, v_univApprox_2465_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2466_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*7 + 3, v_cacheInferType_2467_);
lean_inc_ref(v___x_2401_);
lean_inc(v___x_2476_);
v___x_2481_ = l_Lean_Meta_isExprDefEq(v___x_2476_, v___x_2401_, v___x_2480_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref_known(v___x_2480_, 7);
v___y_2419_ = v___x_2481_;
goto v___jp_2418_;
}
else
{
lean_object* v___x_2482_; 
lean_dec_ref_known(v___x_2472_, 1);
lean_inc_ref(v___x_2401_);
lean_inc(v___x_2476_);
v___x_2482_ = l_Lean_Meta_isExprDefEq(v___x_2476_, v___x_2401_, v___x_2473_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref_known(v___x_2473_, 7);
v___y_2419_ = v___x_2482_;
goto v___jp_2418_;
}
}
}
}
v___jp_2418_:
{
if (lean_obj_tag(v___y_2419_) == 0)
{
lean_object* v_a_2420_; uint8_t v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___y_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___y_2419_, 1);
v___x_2421_ = lean_unbox(v_a_2420_);
lean_dec(v_a_2420_);
if (v___x_2421_ == 0)
{
v_a_2410_ = v_b_2403_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = lean_st_ref_take(v_val_2393_);
lean_inc(v_a_2402_);
lean_inc(v_next_2395_);
v___x_2423_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2394_, v_next_2395_, v_next_2396_, v_a_2402_, v___x_2422_);
v___x_2424_ = lean_st_ref_put(v_val_2393_, v___x_2423_);
v_a_2410_ = v___x_2417_;
goto v___jp_2409_;
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_a_2402_);
lean_dec_ref(v___x_2401_);
lean_dec(v_next_2395_);
v_a_2425_ = lean_ctor_get(v___y_2419_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___y_2419_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___y_2419_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___y_2419_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
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
lean_object* v___x_2579_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2579_ = lean_box(0);
v___x_2586_ = l_Lean_instInhabitedExpr;
v___x_2587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2536_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; uint8_t v___x_2589_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v___x_2589_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2537_, v_a_2545_, v_a_2588_);
lean_dec(v_a_2588_);
if (v___x_2589_ == 0)
{
v_a_2553_ = v___x_2579_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2590_ = lean_array_get_size(v_args_2539_);
v___x_2591_ = lean_nat_dec_lt(v_a_2545_, v___x_2590_);
if (v___x_2591_ == 0)
{
lean_object* v_toCold_2592_; lean_object* v_options_2593_; uint8_t v_hasTrace_2594_; 
v_toCold_2592_ = lean_ctor_get(v___y_2549_, 0);
v_options_2593_ = lean_ctor_get(v_toCold_2592_, 2);
v_hasTrace_2594_ = lean_ctor_get_uint8(v_options_2593_, sizeof(void*)*1);
if (v_hasTrace_2594_ == 0)
{
goto v___jp_2582_;
}
else
{
lean_object* v_inheritedTraceOptions_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v_inheritedTraceOptions_2595_ = lean_ctor_get(v_toCold_2592_, 11);
v___x_2596_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2597_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2598_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2595_, v_options_2593_, v___x_2597_);
if (v___x_2598_ == 0)
{
goto v___jp_2582_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2599_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2537_);
v___x_2600_ = l_Nat_reprFast(v_val_2537_);
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
lean_inc(v_a_2545_);
v___x_2606_ = l_Nat_reprFast(v_a_2545_);
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
lean_inc_ref(v_e_2540_);
v___x_2612_ = l_Lean_MessageData_ofExpr(v_e_2540_);
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
v___x_2617_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2596_, v___x_2616_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2619_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2617_, 1);
lean_inc(v_a_2545_);
v___x_2619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2579_, v_a_2618_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2619_;
goto v___jp_2557_;
}
else
{
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
return v___x_2617_;
}
}
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_array_fget_borrowed(v_args_2539_, v_a_2545_);
v___x_2621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2536_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2623_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v___x_2623_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2537_, v_a_2545_, v_next_2541_, v_a_2622_);
lean_dec(v_a_2622_);
if (lean_obj_tag(v___x_2623_) == 1)
{
lean_object* v_val_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2725_; 
v_val_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2725_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_val_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2725_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; uint8_t v_foApprox_2629_; uint8_t v_ctxApprox_2630_; uint8_t v_quasiPatternApprox_2631_; uint8_t v_constApprox_2632_; uint8_t v_isDefEqStuckEx_2633_; uint8_t v_unificationHints_2634_; uint8_t v_assignSyntheticOpaque_2635_; uint8_t v_offsetCnstrs_2636_; uint8_t v_transparency_2637_; uint8_t v_etaStruct_2638_; uint8_t v_univApprox_2639_; uint8_t v_iota_2640_; uint8_t v_beta_2641_; uint8_t v_proj_2642_; uint8_t v_zeta_2643_; uint8_t v_zetaDelta_2644_; uint8_t v_zetaUnused_2645_; uint8_t v_zetaHave_2646_; uint8_t v_canUnfoldPredicateConfig_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2724_; 
v___x_2628_ = l_Lean_Meta_Context_config(v___y_2547_);
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
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2649_ = v___x_2628_;
v_isShared_2650_ = v_isSharedCheck_2724_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v___x_2628_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2724_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
uint8_t v_trackZetaDelta_2651_; lean_object* v_zetaDeltaSet_2652_; lean_object* v_lctx_2653_; lean_object* v_localInstances_2654_; lean_object* v_defEqCtx_x3f_2655_; lean_object* v_synthPendingDepth_2656_; lean_object* v_customCanUnfoldPredicate_x3f_2657_; uint8_t v_univApprox_2658_; uint8_t v_inTypeClassResolution_2659_; uint8_t v_cacheInferType_2660_; uint8_t v___x_2661_; lean_object* v___x_2663_; 
v_trackZetaDelta_2651_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7);
v_zetaDeltaSet_2652_ = lean_ctor_get(v___y_2547_, 1);
v_lctx_2653_ = lean_ctor_get(v___y_2547_, 2);
v_localInstances_2654_ = lean_ctor_get(v___y_2547_, 3);
v_defEqCtx_x3f_2655_ = lean_ctor_get(v___y_2547_, 4);
v_synthPendingDepth_2656_ = lean_ctor_get(v___y_2547_, 5);
v_customCanUnfoldPredicate_x3f_2657_ = lean_ctor_get(v___y_2547_, 6);
v_univApprox_2658_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2659_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 2);
v_cacheInferType_2660_ = lean_ctor_get_uint8(v___y_2547_, sizeof(void*)*7 + 3);
v___x_2661_ = 0;
if (v_isShared_2650_ == 0)
{
v___x_2663_ = v___x_2649_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 0, v_foApprox_2629_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 1, v_ctxApprox_2630_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 2, v_quasiPatternApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 3, v_constApprox_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 4, v_isDefEqStuckEx_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 5, v_unificationHints_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 7, v_assignSyntheticOpaque_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 8, v_offsetCnstrs_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 9, v_transparency_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 10, v_etaStruct_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 11, v_univApprox_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 12, v_iota_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 13, v_beta_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 14, v_proj_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 15, v_zeta_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 16, v_zetaDelta_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 17, v_zetaUnused_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 18, v_zetaHave_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2723_, 19, v_canUnfoldPredicateConfig_2647_);
v___x_2663_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
uint64_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v_transparency_2668_; lean_object* v___x_2669_; lean_object* v___y_2671_; uint8_t v___x_2717_; uint8_t v___x_2718_; 
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
v___x_2669_ = lean_array_get_borrowed(v___x_2586_, v_params_2542_, v_val_2624_);
lean_dec(v_val_2624_);
v___x_2717_ = 2;
v___x_2718_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2668_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
lean_dec_ref_known(v___x_2666_, 7);
v___x_2719_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2717_, v___x_2665_);
lean_inc(v_customCanUnfoldPredicate_x3f_2657_);
lean_inc(v_synthPendingDepth_2656_);
lean_inc(v_defEqCtx_x3f_2655_);
lean_inc_ref(v_localInstances_2654_);
lean_inc_ref(v_lctx_2653_);
lean_inc(v_zetaDeltaSet_2652_);
v___x_2720_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v_zetaDeltaSet_2652_);
lean_ctor_set(v___x_2720_, 2, v_lctx_2653_);
lean_ctor_set(v___x_2720_, 3, v_localInstances_2654_);
lean_ctor_set(v___x_2720_, 4, v_defEqCtx_x3f_2655_);
lean_ctor_set(v___x_2720_, 5, v_synthPendingDepth_2656_);
lean_ctor_set(v___x_2720_, 6, v_customCanUnfoldPredicate_x3f_2657_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7, v_trackZetaDelta_2651_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 1, v_univApprox_2658_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2659_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*7 + 3, v_cacheInferType_2660_);
lean_inc(v___x_2620_);
lean_inc(v___x_2669_);
v___x_2721_ = l_Lean_Meta_isExprDefEq(v___x_2669_, v___x_2620_, v___x_2720_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref_known(v___x_2720_, 7);
v___y_2671_ = v___x_2721_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2722_; 
lean_dec_ref_known(v___x_2665_, 1);
lean_inc(v___x_2620_);
lean_inc(v___x_2669_);
v___x_2722_ = l_Lean_Meta_isExprDefEq(v___x_2669_, v___x_2620_, v___x_2666_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref_known(v___x_2666_, 7);
v___y_2671_ = v___x_2722_;
goto v___jp_2670_;
}
v___jp_2670_:
{
if (lean_obj_tag(v___y_2671_) == 0)
{
lean_object* v_a_2672_; uint8_t v___x_2673_; 
v_a_2672_ = lean_ctor_get(v___y_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___y_2671_, 1);
v___x_2673_ = lean_unbox(v_a_2672_);
lean_dec(v_a_2672_);
if (v___x_2673_ == 0)
{
lean_object* v_toCold_2674_; lean_object* v_options_2675_; uint8_t v_hasTrace_2676_; 
v_toCold_2674_ = lean_ctor_get(v___y_2549_, 0);
v_options_2675_ = lean_ctor_get(v_toCold_2674_, 2);
v_hasTrace_2676_ = lean_ctor_get_uint8(v_options_2675_, sizeof(void*)*1);
if (v_hasTrace_2676_ == 0)
{
lean_del_object(v___x_2626_);
goto v___jp_2584_;
}
else
{
lean_object* v_inheritedTraceOptions_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v_inheritedTraceOptions_2677_ = lean_ctor_get(v_toCold_2674_, 11);
v___x_2678_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2679_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2677_, v_options_2675_, v___x_2679_);
if (v___x_2680_ == 0)
{
lean_del_object(v___x_2626_);
goto v___jp_2584_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2681_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2537_);
v___x_2682_ = l_Nat_reprFast(v_val_2537_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set_tag(v___x_2626_, 3);
lean_ctor_set(v___x_2626_, 0, v___x_2682_);
v___x_2684_ = v___x_2626_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2685_ = l_Lean_MessageData_ofFormat(v___x_2684_);
v___x_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2681_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2686_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
lean_inc(v_a_2545_);
v___x_2689_ = l_Nat_reprFast(v_a_2545_);
v___x_2690_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
v___x_2691_ = l_Lean_MessageData_ofFormat(v___x_2690_);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2688_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
lean_inc_ref(v_e_2540_);
v___x_2695_ = l_Lean_MessageData_ofExpr(v_e_2540_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
lean_inc(v___x_2669_);
v___x_2699_ = l_Lean_MessageData_ofExpr(v___x_2669_);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_inc(v___x_2620_);
v___x_2703_ = l_Lean_MessageData_ofExpr(v___x_2620_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2678_, v___x_2704_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; lean_object* v___x_2707_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
lean_inc(v_a_2545_);
v___x_2707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2579_, v_a_2706_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2707_;
goto v___jp_2557_;
}
else
{
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
return v___x_2705_;
}
}
}
}
}
else
{
lean_del_object(v___x_2626_);
v_a_2553_ = v___x_2579_;
goto v___jp_2552_;
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_del_object(v___x_2626_);
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v_a_2709_ = lean_ctor_get(v___y_2671_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___y_2671_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___y_2671_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___y_2671_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
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
lean_object* v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; 
lean_dec(v___x_2623_);
v___x_2726_ = lean_unsigned_to_nat(0u);
v___x_2727_ = 0;
lean_inc(v___x_2620_);
lean_inc(v_a_2545_);
v___x_2728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2536_, v_val_2537_, v_a_2545_, v_next_2541_, v___x_2543_, v___x_2544_, v___x_2543_, v_params_2542_, v___x_2620_, v___x_2726_, v___x_2727_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; uint8_t v___x_2730_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = lean_unbox(v_a_2729_);
lean_dec(v_a_2729_);
if (v___x_2730_ == 0)
{
lean_object* v_toCold_2731_; lean_object* v_options_2732_; uint8_t v_hasTrace_2733_; 
v_toCold_2731_ = lean_ctor_get(v___y_2549_, 0);
v_options_2732_ = lean_ctor_get(v_toCold_2731_, 2);
v_hasTrace_2733_ = lean_ctor_get_uint8(v_options_2732_, sizeof(void*)*1);
if (v_hasTrace_2733_ == 0)
{
goto v___jp_2580_;
}
else
{
lean_object* v_inheritedTraceOptions_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v_inheritedTraceOptions_2734_ = lean_ctor_get(v_toCold_2731_, 11);
v___x_2735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2736_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2734_, v_options_2732_, v___x_2736_);
if (v___x_2737_ == 0)
{
goto v___jp_2580_;
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
lean_inc(v___x_2620_);
v___x_2755_ = l_Lean_MessageData_ofExpr(v___x_2620_);
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
v___x_2761_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2579_, v_a_2760_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
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
}
else
{
v_a_2553_ = v___x_2579_;
goto v___jp_2552_;
}
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2545_);
lean_dec_ref(v_e_2540_);
lean_dec(v_val_2537_);
v_a_2762_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2728_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2728_);
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
v_a_2770_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2621_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2621_);
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
v_a_2778_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2587_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2587_);
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
v___jp_2580_:
{
lean_object* v___x_2581_; 
lean_inc(v_a_2545_);
v___x_2581_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2579_, v___x_2579_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2581_;
goto v___jp_2557_;
}
v___jp_2582_:
{
lean_object* v___x_2583_; 
lean_inc(v_a_2545_);
v___x_2583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2579_, v___x_2579_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2583_;
goto v___jp_2557_;
}
v___jp_2584_:
{
lean_object* v___x_2585_; 
lean_inc(v_a_2545_);
v___x_2585_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2536_, v_val_2537_, v_a_2545_, v___x_2579_, v___x_2579_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
v___y_2558_ = v___x_2585_;
goto v___jp_2557_;
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
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4192_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4193_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
lean_inc_ref(v_preDefs_4186_);
v___x_4194_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v_value_4198_; lean_object* v___f_4199_; uint8_t v___x_4200_; lean_object* v___x_4201_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = lean_array_get(v___x_4192_, v_preDefs_4186_, v___x_4196_);
lean_dec_ref(v_preDefs_4186_);
v_value_4198_ = lean_ctor_get(v___x_4197_, 7);
lean_inc_ref(v_value_4198_);
lean_dec(v___x_4197_);
v___f_4199_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4199_, 0, v_a_4195_);
lean_closure_set(v___f_4199_, 1, v___x_4193_);
lean_closure_set(v___f_4199_, 2, v___x_4196_);
v___x_4200_ = 0;
v___x_4201_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4198_, v___f_4199_, v___x_4200_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_);
return v___x_4201_;
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v_preDefs_4186_);
v_a_4202_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4194_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4194_);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(lean_object* v_msg_5004_){
_start:
{
lean_object* v___f_5005_; lean_object* v___f_5006_; lean_object* v___f_5007_; lean_object* v___f_5008_; lean_object* v___f_5009_; lean_object* v___f_5010_; lean_object* v___f_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___f_5005_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5006_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5007_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5008_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5009_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5010_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5011_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5012_, 0, v___f_5005_);
lean_ctor_set(v___x_5012_, 1, v___f_5006_);
v___x_5013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5013_, 0, v___x_5012_);
lean_ctor_set(v___x_5013_, 1, v___f_5007_);
lean_ctor_set(v___x_5013_, 2, v___f_5008_);
lean_ctor_set(v___x_5013_, 3, v___f_5009_);
lean_ctor_set(v___x_5013_, 4, v___f_5010_);
v___x_5014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5013_);
lean_ctor_set(v___x_5014_, 1, v___f_5011_);
v___x_5015_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5016_ = l_instInhabitedOfMonad___redArg(v___x_5014_, v___x_5015_);
v___x_5017_ = lean_panic_fn_borrowed(v___x_5016_, v_msg_5004_);
lean_dec(v___x_5016_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0(lean_object* v_00_u03b1_5018_, lean_object* v_msg_5019_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v_msg_5019_);
return v___x_5020_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; 
v___x_5023_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__1));
v___x_5024_ = lean_unsigned_to_nat(8u);
v___x_5025_ = lean_unsigned_to_nat(394u);
v___x_5026_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__0));
v___x_5027_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5028_ = l_mkPanicMessageWithDecl(v___x_5027_, v___x_5026_, v___x_5025_, v___x_5024_, v___x_5023_);
return v___x_5028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(lean_object* v_x_5029_, lean_object* v_x_5030_){
_start:
{
if (lean_obj_tag(v_x_5029_) == 0)
{
return v_x_5030_;
}
else
{
lean_object* v_head_5031_; lean_object* v_fst_5032_; 
v_head_5031_ = lean_ctor_get(v_x_5029_, 0);
v_fst_5032_ = lean_ctor_get(v_head_5031_, 0);
if (lean_obj_tag(v_fst_5032_) == 0)
{
lean_object* v_tail_5033_; 
v_tail_5033_ = lean_ctor_get(v_x_5029_, 1);
lean_inc(v_tail_5033_);
lean_dec_ref_known(v_x_5029_, 2);
v_x_5029_ = v_tail_5033_;
goto _start;
}
else
{
lean_object* v_tail_5035_; lean_object* v_snd_5036_; lean_object* v_val_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
lean_inc_ref(v_fst_5032_);
lean_inc(v_head_5031_);
v_tail_5035_ = lean_ctor_get(v_x_5029_, 1);
lean_inc(v_tail_5035_);
lean_dec_ref_known(v_x_5029_, 2);
v_snd_5036_ = lean_ctor_get(v_head_5031_, 1);
lean_inc(v_snd_5036_);
lean_dec(v_head_5031_);
v_val_5037_ = lean_ctor_get(v_fst_5032_, 0);
lean_inc(v_val_5037_);
lean_dec_ref_known(v_fst_5032_, 1);
v___x_5038_ = lean_array_get_size(v_x_5030_);
v___x_5039_ = lean_nat_dec_lt(v_val_5037_, v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
lean_dec(v_val_5037_);
lean_dec(v_snd_5036_);
lean_dec(v_tail_5035_);
lean_dec_ref(v_x_5030_);
v___x_5040_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg___closed__2);
v___x_5041_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5040_);
return v___x_5041_;
}
else
{
lean_object* v___x_5042_; 
v___x_5042_ = lean_array_set(v_x_5030_, v_val_5037_, v_snd_5036_);
lean_dec(v_val_5037_);
v_x_5029_ = v_tail_5035_;
v_x_5030_ = v___x_5042_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go(lean_object* v_00_u03b1_5044_, lean_object* v_x_5045_, lean_object* v_x_5046_){
_start:
{
lean_object* v___x_5047_; 
v___x_5047_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v_x_5045_, v_x_5046_);
return v___x_5047_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2(void){
_start:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5050_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__1));
v___x_5051_ = lean_unsigned_to_nat(2u);
v___x_5052_ = lean_unsigned_to_nat(384u);
v___x_5053_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__0));
v___x_5054_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5055_ = l_mkPanicMessageWithDecl(v___x_5054_, v___x_5053_, v___x_5052_, v___x_5051_, v___x_5050_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object* v_perm_5058_, lean_object* v_xs_5059_){
_start:
{
lean_object* v___x_5060_; lean_object* v___x_5061_; uint8_t v___x_5062_; 
v___x_5060_ = lean_array_get_size(v_xs_5059_);
v___x_5061_ = lean_array_get_size(v_perm_5058_);
v___x_5062_ = lean_nat_dec_eq(v___x_5060_, v___x_5061_);
if (v___x_5062_ == 0)
{
lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5063_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__2);
v___x_5064_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg(v___x_5063_);
return v___x_5064_;
}
else
{
lean_object* v___x_5065_; uint8_t v___x_5066_; 
v___x_5065_ = lean_unsigned_to_nat(0u);
v___x_5066_ = lean_nat_dec_eq(v___x_5060_, v___x_5065_);
if (v___x_5066_ == 0)
{
lean_object* v_dummy_5067_; lean_object* v___x_5068_; lean_object* v_ys_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v_dummy_5067_ = lean_array_fget_borrowed(v_xs_5059_, v___x_5065_);
v___x_5068_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5058_);
lean_inc(v_dummy_5067_);
v_ys_5069_ = lean_mk_array(v___x_5068_, v_dummy_5067_);
v___x_5070_ = l_Array_zip___redArg(v_perm_5058_, v_xs_5059_);
v___x_5071_ = lean_array_to_list(v___x_5070_);
v___x_5072_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go___redArg(v___x_5071_, v_ys_5069_);
return v___x_5072_;
}
else
{
lean_object* v___x_5073_; 
v___x_5073_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
return v___x_5073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg___boxed(lean_object* v_perm_5074_, lean_object* v_xs_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5074_, v_xs_5075_);
lean_dec_ref(v_xs_5075_);
lean_dec_ref(v_perm_5074_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed(lean_object* v_00_u03b1_5077_, lean_object* v_perm_5078_, lean_object* v_xs_5079_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v_perm_5078_, v_xs_5079_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___boxed(lean_object* v_00_u03b1_5081_, lean_object* v_perm_5082_, lean_object* v_xs_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lean_Elab_FixedParamPerm_pickFixed(v_00_u03b1_5081_, v_perm_5082_, v_xs_5083_);
lean_dec_ref(v_xs_5083_);
lean_dec_ref(v_perm_5082_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(lean_object* v_xs_5085_, lean_object* v_upperBound_5086_, lean_object* v_perm_5087_, lean_object* v_a_5088_, lean_object* v_b_5089_){
_start:
{
lean_object* v_a_5091_; uint8_t v___x_5098_; 
v___x_5098_ = lean_nat_dec_lt(v_a_5088_, v_upperBound_5086_);
if (v___x_5098_ == 0)
{
lean_dec(v_a_5088_);
return v_b_5089_;
}
else
{
lean_object* v___x_5099_; uint8_t v___x_5100_; 
v___x_5099_ = lean_array_get_size(v_perm_5087_);
v___x_5100_ = lean_nat_dec_lt(v_a_5088_, v___x_5099_);
if (v___x_5100_ == 0)
{
goto v___jp_5095_;
}
else
{
lean_object* v___x_5101_; 
v___x_5101_ = lean_array_fget_borrowed(v_perm_5087_, v_a_5088_);
if (lean_obj_tag(v___x_5101_) == 0)
{
goto v___jp_5095_;
}
else
{
v_a_5091_ = v_b_5089_;
goto v___jp_5090_;
}
}
}
v___jp_5090_:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5092_ = lean_unsigned_to_nat(1u);
v___x_5093_ = lean_nat_add(v_a_5088_, v___x_5092_);
lean_dec(v_a_5088_);
v_a_5088_ = v___x_5093_;
v_b_5089_ = v_a_5091_;
goto _start;
}
v___jp_5095_:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5096_ = lean_array_fget_borrowed(v_xs_5085_, v_a_5088_);
lean_inc(v___x_5096_);
v___x_5097_ = lean_array_push(v_b_5089_, v___x_5096_);
v_a_5091_ = v___x_5097_;
goto v___jp_5090_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg___boxed(lean_object* v_xs_5102_, lean_object* v_upperBound_5103_, lean_object* v_perm_5104_, lean_object* v_a_5105_, lean_object* v_b_5106_){
_start:
{
lean_object* v_res_5107_; 
v_res_5107_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5102_, v_upperBound_5103_, v_perm_5104_, v_a_5105_, v_b_5106_);
lean_dec_ref(v_perm_5104_);
lean_dec(v_upperBound_5103_);
lean_dec_ref(v_xs_5102_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object* v_perm_5108_, lean_object* v_xs_5109_){
_start:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v_ys_5112_; lean_object* v___x_5113_; 
v___x_5110_ = lean_array_get_size(v_xs_5109_);
v___x_5111_ = lean_unsigned_to_nat(0u);
v_ys_5112_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5109_, v___x_5110_, v_perm_5108_, v___x_5111_, v_ys_5112_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg___boxed(lean_object* v_perm_5114_, lean_object* v_xs_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5114_, v_xs_5115_);
lean_dec_ref(v_xs_5115_);
lean_dec_ref(v_perm_5114_);
return v_res_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying(lean_object* v_00_u03b1_5117_, lean_object* v_perm_5118_, lean_object* v_xs_5119_){
_start:
{
lean_object* v___x_5120_; 
v___x_5120_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_perm_5118_, v_xs_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___boxed(lean_object* v_00_u03b1_5121_, lean_object* v_perm_5122_, lean_object* v_xs_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Elab_FixedParamPerm_pickVarying(v_00_u03b1_5121_, v_perm_5122_, v_xs_5123_);
lean_dec_ref(v_xs_5123_);
lean_dec_ref(v_perm_5122_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(lean_object* v_00_u03b1_5125_, lean_object* v_xs_5126_, lean_object* v_upperBound_5127_, lean_object* v_perm_5128_, lean_object* v_inst_5129_, lean_object* v_R_5130_, lean_object* v_a_5131_, lean_object* v_b_5132_, lean_object* v_c_5133_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___redArg(v_xs_5126_, v_upperBound_5127_, v_perm_5128_, v_a_5131_, v_b_5132_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0___boxed(lean_object* v_00_u03b1_5135_, lean_object* v_xs_5136_, lean_object* v_upperBound_5137_, lean_object* v_perm_5138_, lean_object* v_inst_5139_, lean_object* v_R_5140_, lean_object* v_a_5141_, lean_object* v_b_5142_, lean_object* v_c_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerm_pickVarying_spec__0(v_00_u03b1_5135_, v_xs_5136_, v_upperBound_5137_, v_perm_5138_, v_inst_5139_, v_R_5140_, v_a_5141_, v_b_5142_, v_c_5143_);
lean_dec_ref(v_perm_5138_);
lean_dec(v_upperBound_5137_);
lean_dec_ref(v_xs_5136_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(lean_object* v_msg_5145_){
_start:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5146_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5147_ = lean_panic_fn_borrowed(v___x_5146_, v_msg_5145_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0(lean_object* v_00_u03b1_5148_, lean_object* v_msg_5149_){
_start:
{
lean_object* v___x_5150_; 
v___x_5150_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v_msg_5149_);
return v___x_5150_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(lean_object* v_j_5151_, lean_object* v___x_5152_, lean_object* v_i_5153_, lean_object* v___x_5154_, lean_object* v_as_5155_, size_t v_i_5156_, size_t v_stop_5157_){
_start:
{
uint8_t v___x_5158_; 
v___x_5158_ = lean_usize_dec_eq(v_i_5156_, v_stop_5157_);
if (v___x_5158_ == 0)
{
uint8_t v___x_5159_; uint8_t v___y_5161_; lean_object* v___x_5165_; 
v___x_5159_ = 1;
v___x_5165_ = lean_array_uget_borrowed(v_as_5155_, v_i_5156_);
if (lean_obj_tag(v___x_5165_) == 0)
{
uint8_t v___x_5166_; 
v___x_5166_ = lean_nat_dec_lt(v_j_5151_, v___x_5152_);
v___y_5161_ = v___x_5166_;
goto v___jp_5160_;
}
else
{
uint8_t v___x_5167_; 
v___x_5167_ = lean_nat_dec_lt(v_i_5153_, v___x_5154_);
v___y_5161_ = v___x_5167_;
goto v___jp_5160_;
}
v___jp_5160_:
{
if (v___y_5161_ == 0)
{
size_t v___x_5162_; size_t v___x_5163_; 
v___x_5162_ = ((size_t)1ULL);
v___x_5163_ = lean_usize_add(v_i_5156_, v___x_5162_);
v_i_5156_ = v___x_5163_;
goto _start;
}
else
{
return v___x_5159_;
}
}
}
else
{
uint8_t v___x_5168_; 
v___x_5168_ = 0;
return v___x_5168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1___boxed(lean_object* v_j_5169_, lean_object* v___x_5170_, lean_object* v_i_5171_, lean_object* v___x_5172_, lean_object* v_as_5173_, lean_object* v_i_5174_, lean_object* v_stop_5175_){
_start:
{
size_t v_i_boxed_5176_; size_t v_stop_boxed_5177_; uint8_t v_res_5178_; lean_object* v_r_5179_; 
v_i_boxed_5176_ = lean_unbox_usize(v_i_5174_);
lean_dec(v_i_5174_);
v_stop_boxed_5177_ = lean_unbox_usize(v_stop_5175_);
lean_dec(v_stop_5175_);
v_res_5178_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5169_, v___x_5170_, v_i_5171_, v___x_5172_, v_as_5173_, v_i_boxed_5176_, v_stop_boxed_5177_);
lean_dec_ref(v_as_5173_);
lean_dec(v___x_5172_);
lean_dec(v_i_5171_);
lean_dec(v___x_5170_);
lean_dec(v_j_5169_);
v_r_5179_ = lean_box(v_res_5178_);
return v_r_5179_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5182_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__1));
v___x_5183_ = lean_unsigned_to_nat(10u);
v___x_5184_ = lean_unsigned_to_nat(425u);
v___x_5185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5186_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5187_ = l_mkPanicMessageWithDecl(v___x_5186_, v___x_5185_, v___x_5184_, v___x_5183_, v___x_5182_);
return v___x_5187_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v___x_5189_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__3));
v___x_5190_ = lean_unsigned_to_nat(12u);
v___x_5191_ = lean_unsigned_to_nat(433u);
v___x_5192_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__0));
v___x_5193_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5194_ = l_mkPanicMessageWithDecl(v___x_5193_, v___x_5192_, v___x_5191_, v___x_5190_, v___x_5189_);
return v___x_5194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(lean_object* v_perm_5195_, lean_object* v_fixedArgs_5196_, lean_object* v_varyingArgs_5197_, lean_object* v_i_5198_, lean_object* v_j_5199_, lean_object* v_xs_5200_){
_start:
{
lean_object* v_lower_5202_; lean_object* v_upper_5203_; lean_object* v___x_5207_; uint8_t v___x_5208_; 
v___x_5207_ = lean_array_get_size(v_perm_5195_);
v___x_5208_ = lean_nat_dec_lt(v_i_5198_, v___x_5207_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; lean_object* v___x_5210_; uint8_t v___x_5211_; 
lean_dec(v_i_5198_);
lean_dec_ref(v_perm_5195_);
v___x_5209_ = lean_unsigned_to_nat(0u);
v___x_5210_ = lean_array_get_size(v_varyingArgs_5197_);
v___x_5211_ = lean_nat_dec_le(v_j_5199_, v___x_5209_);
if (v___x_5211_ == 0)
{
v_lower_5202_ = v_j_5199_;
v_upper_5203_ = v___x_5210_;
goto v___jp_5201_;
}
else
{
lean_dec(v_j_5199_);
v_lower_5202_ = v___x_5209_;
v_upper_5203_ = v___x_5210_;
goto v___jp_5201_;
}
}
else
{
lean_object* v___x_5212_; 
v___x_5212_ = lean_array_fget_borrowed(v_perm_5195_, v_i_5198_);
if (lean_obj_tag(v___x_5212_) == 1)
{
lean_object* v_val_5213_; lean_object* v___x_5214_; uint8_t v___x_5215_; 
v_val_5213_ = lean_ctor_get(v___x_5212_, 0);
v___x_5214_ = lean_array_get_size(v_fixedArgs_5196_);
v___x_5215_ = lean_nat_dec_lt(v_val_5213_, v___x_5214_);
if (v___x_5215_ == 0)
{
lean_object* v___x_5216_; lean_object* v___x_5217_; 
lean_dec_ref(v_xs_5200_);
lean_dec(v_j_5199_);
lean_dec(v_i_5198_);
lean_dec_ref(v_varyingArgs_5197_);
lean_dec_ref(v_perm_5195_);
v___x_5216_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__2);
v___x_5217_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5216_);
return v___x_5217_;
}
else
{
lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; 
v___x_5218_ = lean_unsigned_to_nat(1u);
v___x_5219_ = lean_nat_add(v_i_5198_, v___x_5218_);
lean_dec(v_i_5198_);
v___x_5220_ = lean_array_fget_borrowed(v_fixedArgs_5196_, v_val_5213_);
lean_inc(v___x_5220_);
v___x_5221_ = lean_array_push(v_xs_5200_, v___x_5220_);
v_i_5198_ = v___x_5219_;
v_xs_5200_ = v___x_5221_;
goto _start;
}
}
else
{
lean_object* v___x_5223_; lean_object* v___y_5225_; lean_object* v___y_5226_; lean_object* v___y_5227_; lean_object* v_lower_5235_; lean_object* v_upper_5236_; uint8_t v___x_5244_; 
v___x_5223_ = lean_array_get_size(v_varyingArgs_5197_);
v___x_5244_ = lean_nat_dec_lt(v_j_5199_, v___x_5223_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; uint8_t v___x_5246_; 
lean_dec_ref(v_varyingArgs_5197_);
v___x_5245_ = lean_unsigned_to_nat(0u);
v___x_5246_ = lean_nat_dec_le(v_i_5198_, v___x_5245_);
if (v___x_5246_ == 0)
{
lean_inc(v_i_5198_);
v_lower_5235_ = v_i_5198_;
v_upper_5236_ = v___x_5207_;
goto v___jp_5234_;
}
else
{
v_lower_5235_ = v___x_5245_;
v_upper_5236_ = v___x_5207_;
goto v___jp_5234_;
}
}
else
{
lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; 
v___x_5247_ = lean_unsigned_to_nat(1u);
v___x_5248_ = lean_nat_add(v_i_5198_, v___x_5247_);
lean_dec(v_i_5198_);
v___x_5249_ = lean_nat_add(v_j_5199_, v___x_5247_);
v___x_5250_ = lean_array_fget_borrowed(v_varyingArgs_5197_, v_j_5199_);
lean_dec(v_j_5199_);
lean_inc(v___x_5250_);
v___x_5251_ = lean_array_push(v_xs_5200_, v___x_5250_);
v_i_5198_ = v___x_5248_;
v_j_5199_ = v___x_5249_;
v_xs_5200_ = v___x_5251_;
goto _start;
}
v___jp_5224_:
{
uint8_t v___x_5228_; 
v___x_5228_ = lean_nat_dec_lt(v___y_5225_, v___y_5227_);
if (v___x_5228_ == 0)
{
lean_dec(v___y_5227_);
lean_dec_ref(v___y_5226_);
lean_dec(v___y_5225_);
lean_dec(v_j_5199_);
lean_dec(v_i_5198_);
return v_xs_5200_;
}
else
{
size_t v___x_5229_; size_t v___x_5230_; uint8_t v___x_5231_; 
v___x_5229_ = lean_usize_of_nat(v___y_5225_);
lean_dec(v___y_5225_);
v___x_5230_ = lean_usize_of_nat(v___y_5227_);
lean_dec(v___y_5227_);
v___x_5231_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5199_, v___x_5223_, v_i_5198_, v___x_5207_, v___y_5226_, v___x_5229_, v___x_5230_);
lean_dec_ref(v___y_5226_);
lean_dec(v_i_5198_);
lean_dec(v_j_5199_);
if (v___x_5231_ == 0)
{
return v_xs_5200_;
}
else
{
lean_object* v___x_5232_; lean_object* v___x_5233_; 
lean_dec_ref(v_xs_5200_);
v___x_5232_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___closed__4);
v___x_5233_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5232_);
return v___x_5233_;
}
}
}
v___jp_5234_:
{
lean_object* v___x_5237_; lean_object* v_array_5238_; lean_object* v_start_5239_; lean_object* v_stop_5240_; uint8_t v___x_5241_; 
v___x_5237_ = l_Array_toSubarray___redArg(v_perm_5195_, v_lower_5235_, v_upper_5236_);
v_array_5238_ = lean_ctor_get(v___x_5237_, 0);
lean_inc_ref(v_array_5238_);
v_start_5239_ = lean_ctor_get(v___x_5237_, 1);
lean_inc(v_start_5239_);
v_stop_5240_ = lean_ctor_get(v___x_5237_, 2);
lean_inc(v_stop_5240_);
lean_dec_ref(v___x_5237_);
v___x_5241_ = lean_nat_dec_lt(v_start_5239_, v_stop_5240_);
if (v___x_5241_ == 0)
{
lean_dec(v_stop_5240_);
lean_dec(v_start_5239_);
lean_dec_ref(v_array_5238_);
lean_dec(v_j_5199_);
lean_dec(v_i_5198_);
return v_xs_5200_;
}
else
{
lean_object* v___x_5242_; uint8_t v___x_5243_; 
v___x_5242_ = lean_array_get_size(v_array_5238_);
v___x_5243_ = lean_nat_dec_le(v_stop_5240_, v___x_5242_);
if (v___x_5243_ == 0)
{
lean_dec(v_stop_5240_);
v___y_5225_ = v_start_5239_;
v___y_5226_ = v_array_5238_;
v___y_5227_ = v___x_5242_;
goto v___jp_5224_;
}
else
{
v___y_5225_ = v_start_5239_;
v___y_5226_ = v_array_5238_;
v___y_5227_ = v_stop_5240_;
goto v___jp_5224_;
}
}
}
}
}
v___jp_5201_:
{
lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
v___x_5204_ = l_Array_toSubarray___redArg(v_varyingArgs_5197_, v_lower_5202_, v_upper_5203_);
v___x_5205_ = l_Subarray_copy___redArg(v___x_5204_);
v___x_5206_ = l_Array_append___redArg(v_xs_5200_, v___x_5205_);
lean_dec_ref(v___x_5205_);
return v___x_5206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg___boxed(lean_object* v_perm_5253_, lean_object* v_fixedArgs_5254_, lean_object* v_varyingArgs_5255_, lean_object* v_i_5256_, lean_object* v_j_5257_, lean_object* v_xs_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5253_, v_fixedArgs_5254_, v_varyingArgs_5255_, v_i_5256_, v_j_5257_, v_xs_5258_);
lean_dec_ref(v_fixedArgs_5254_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(lean_object* v_00_u03b1_5260_, lean_object* v_perm_5261_, lean_object* v_fixedArgs_5262_, lean_object* v_varyingArgs_5263_, lean_object* v_i_5264_, lean_object* v_j_5265_, lean_object* v_xs_5266_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5261_, v_fixedArgs_5262_, v_varyingArgs_5263_, v_i_5264_, v_j_5265_, v_xs_5266_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___boxed(lean_object* v_00_u03b1_5268_, lean_object* v_perm_5269_, lean_object* v_fixedArgs_5270_, lean_object* v_varyingArgs_5271_, lean_object* v_i_5272_, lean_object* v_j_5273_, lean_object* v_xs_5274_){
_start:
{
lean_object* v_res_5275_; 
v_res_5275_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go(v_00_u03b1_5268_, v_perm_5269_, v_fixedArgs_5270_, v_varyingArgs_5271_, v_i_5272_, v_j_5273_, v_xs_5274_);
lean_dec_ref(v_fixedArgs_5270_);
return v_res_5275_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2(void){
_start:
{
lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___x_5278_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__1));
v___x_5279_ = lean_unsigned_to_nat(2u);
v___x_5280_ = lean_unsigned_to_nat(416u);
v___x_5281_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__0));
v___x_5282_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5283_ = l_mkPanicMessageWithDecl(v___x_5282_, v___x_5281_, v___x_5280_, v___x_5279_, v___x_5278_);
return v___x_5283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object* v_perm_5284_, lean_object* v_fixedArgs_5285_, lean_object* v_varyingArgs_5286_){
_start:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; uint8_t v___x_5289_; 
v___x_5287_ = lean_array_get_size(v_fixedArgs_5285_);
v___x_5288_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_5284_);
v___x_5289_ = lean_nat_dec_eq(v___x_5287_, v___x_5288_);
lean_dec(v___x_5288_);
if (v___x_5289_ == 0)
{
lean_object* v___x_5290_; lean_object* v___x_5291_; 
lean_dec_ref(v_varyingArgs_5286_);
lean_dec_ref(v_perm_5284_);
v___x_5290_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2, &l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_buildArgs___redArg___closed__2);
v___x_5291_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__0___redArg(v___x_5290_);
return v___x_5291_;
}
else
{
lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5292_ = lean_unsigned_to_nat(0u);
v___x_5293_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_pickFixed___redArg___closed__3));
v___x_5294_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go___redArg(v_perm_5284_, v_fixedArgs_5285_, v_varyingArgs_5286_, v___x_5292_, v___x_5292_, v___x_5293_);
return v___x_5294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg___boxed(lean_object* v_perm_5295_, lean_object* v_fixedArgs_5296_, lean_object* v_varyingArgs_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5295_, v_fixedArgs_5296_, v_varyingArgs_5297_);
lean_dec_ref(v_fixedArgs_5296_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs(lean_object* v_00_u03b1_5299_, lean_object* v_perm_5300_, lean_object* v_fixedArgs_5301_, lean_object* v_varyingArgs_5302_){
_start:
{
lean_object* v___x_5303_; 
v___x_5303_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v_perm_5300_, v_fixedArgs_5301_, v_varyingArgs_5302_);
return v___x_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___boxed(lean_object* v_00_u03b1_5304_, lean_object* v_perm_5305_, lean_object* v_fixedArgs_5306_, lean_object* v_varyingArgs_5307_){
_start:
{
lean_object* v_res_5308_; 
v_res_5308_ = l_Lean_Elab_FixedParamPerm_buildArgs(v_00_u03b1_5304_, v_perm_5305_, v_fixedArgs_5306_, v_varyingArgs_5307_);
lean_dec_ref(v_fixedArgs_5306_);
return v_res_5308_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(lean_object* v_x_5309_, lean_object* v_x_5310_){
_start:
{
if (lean_obj_tag(v_x_5309_) == 0)
{
if (lean_obj_tag(v_x_5310_) == 0)
{
uint8_t v___x_5311_; 
v___x_5311_ = 1;
return v___x_5311_;
}
else
{
uint8_t v___x_5312_; 
v___x_5312_ = 0;
return v___x_5312_;
}
}
else
{
if (lean_obj_tag(v_x_5310_) == 0)
{
uint8_t v___x_5313_; 
v___x_5313_ = 0;
return v___x_5313_;
}
else
{
lean_object* v_val_5314_; lean_object* v_val_5315_; uint8_t v___x_5316_; 
v_val_5314_ = lean_ctor_get(v_x_5309_, 0);
v_val_5315_ = lean_ctor_get(v_x_5310_, 0);
v___x_5316_ = lean_nat_dec_eq(v_val_5314_, v_val_5315_);
return v___x_5316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1___boxed(lean_object* v_x_5317_, lean_object* v_x_5318_){
_start:
{
uint8_t v_res_5319_; lean_object* v_r_5320_; 
v_res_5319_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v_x_5317_, v_x_5318_);
lean_dec(v_x_5318_);
lean_dec(v_x_5317_);
v_r_5320_ = lean_box(v_res_5319_);
return v_r_5320_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(lean_object* v_xs_5321_, lean_object* v_ys_5322_, lean_object* v_x_5323_){
_start:
{
lean_object* v_zero_5324_; uint8_t v_isZero_5325_; 
v_zero_5324_ = lean_unsigned_to_nat(0u);
v_isZero_5325_ = lean_nat_dec_eq(v_x_5323_, v_zero_5324_);
if (v_isZero_5325_ == 1)
{
lean_dec(v_x_5323_);
return v_isZero_5325_;
}
else
{
lean_object* v_one_5326_; lean_object* v_n_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; uint8_t v___x_5330_; 
v_one_5326_ = lean_unsigned_to_nat(1u);
v_n_5327_ = lean_nat_sub(v_x_5323_, v_one_5326_);
lean_dec(v_x_5323_);
v___x_5328_ = lean_array_fget_borrowed(v_xs_5321_, v_n_5327_);
v___x_5329_ = lean_array_fget_borrowed(v_ys_5322_, v_n_5327_);
v___x_5330_ = l_Option_instBEq_beq___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__1(v___x_5328_, v___x_5329_);
if (v___x_5330_ == 0)
{
lean_dec(v_n_5327_);
return v___x_5330_;
}
else
{
v_x_5323_ = v_n_5327_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg___boxed(lean_object* v_xs_5332_, lean_object* v_ys_5333_, lean_object* v_x_5334_){
_start:
{
uint8_t v_res_5335_; lean_object* v_r_5336_; 
v_res_5335_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5332_, v_ys_5333_, v_x_5334_);
lean_dec_ref(v_ys_5333_);
lean_dec_ref(v_xs_5332_);
v_r_5336_ = lean_box(v_res_5335_);
return v_r_5336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(size_t v_sz_5337_, size_t v_i_5338_, lean_object* v_bs_5339_){
_start:
{
uint8_t v___x_5340_; 
v___x_5340_ = lean_usize_dec_lt(v_i_5338_, v_sz_5337_);
if (v___x_5340_ == 0)
{
return v_bs_5339_;
}
else
{
lean_object* v_v_5341_; lean_object* v___x_5342_; lean_object* v_bs_x27_5343_; lean_object* v___x_5344_; size_t v___x_5345_; size_t v___x_5346_; lean_object* v___x_5347_; 
v_v_5341_ = lean_array_uget(v_bs_5339_, v_i_5338_);
v___x_5342_ = lean_unsigned_to_nat(0u);
v_bs_x27_5343_ = lean_array_uset(v_bs_5339_, v_i_5338_, v___x_5342_);
v___x_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5344_, 0, v_v_5341_);
v___x_5345_ = ((size_t)1ULL);
v___x_5346_ = lean_usize_add(v_i_5338_, v___x_5345_);
v___x_5347_ = lean_array_uset(v_bs_x27_5343_, v_i_5338_, v___x_5344_);
v_i_5338_ = v___x_5346_;
v_bs_5339_ = v___x_5347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0___boxed(lean_object* v_sz_5349_, lean_object* v_i_5350_, lean_object* v_bs_5351_){
_start:
{
size_t v_sz_boxed_5352_; size_t v_i_boxed_5353_; lean_object* v_res_5354_; 
v_sz_boxed_5352_ = lean_unbox_usize(v_sz_5349_);
lean_dec(v_sz_5349_);
v_i_boxed_5353_ = lean_unbox_usize(v_i_5350_);
lean_dec(v_i_5350_);
v_res_5354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_boxed_5352_, v_i_boxed_5353_, v_bs_5351_);
return v_res_5354_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(lean_object* v_fixedParamPerms_5355_, lean_object* v_as_5356_, size_t v_i_5357_, size_t v_stop_5358_){
_start:
{
uint8_t v___x_5359_; 
v___x_5359_ = lean_usize_dec_eq(v_i_5357_, v_stop_5358_);
if (v___x_5359_ == 0)
{
lean_object* v_numFixed_5360_; uint8_t v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; size_t v_sz_5364_; size_t v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; uint8_t v___x_5373_; 
v_numFixed_5360_ = lean_ctor_get(v_fixedParamPerms_5355_, 0);
v___x_5361_ = 1;
v___x_5362_ = lean_array_uget_borrowed(v_as_5356_, v_i_5357_);
lean_inc(v_numFixed_5360_);
v___x_5363_ = l_Array_range(v_numFixed_5360_);
v_sz_5364_ = lean_array_size(v___x_5363_);
v___x_5365_ = ((size_t)0ULL);
v___x_5366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__0(v_sz_5364_, v___x_5365_, v___x_5363_);
v___x_5367_ = lean_array_get_size(v___x_5362_);
v___x_5368_ = lean_nat_sub(v___x_5367_, v_numFixed_5360_);
v___x_5369_ = lean_box(0);
v___x_5370_ = lean_mk_array(v___x_5368_, v___x_5369_);
v___x_5371_ = l_Array_append___redArg(v___x_5366_, v___x_5370_);
lean_dec_ref(v___x_5370_);
v___x_5372_ = lean_array_get_size(v___x_5371_);
v___x_5373_ = lean_nat_dec_eq(v___x_5367_, v___x_5372_);
if (v___x_5373_ == 0)
{
lean_dec_ref(v___x_5371_);
lean_dec_ref(v_fixedParamPerms_5355_);
return v___x_5361_;
}
else
{
uint8_t v___x_5374_; 
v___x_5374_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v___x_5362_, v___x_5371_, v___x_5367_);
lean_dec_ref(v___x_5371_);
if (v___x_5374_ == 0)
{
lean_dec_ref(v_fixedParamPerms_5355_);
return v___x_5361_;
}
else
{
size_t v___x_5375_; size_t v___x_5376_; 
v___x_5375_ = ((size_t)1ULL);
v___x_5376_ = lean_usize_add(v_i_5357_, v___x_5375_);
v_i_5357_ = v___x_5376_;
goto _start;
}
}
}
else
{
uint8_t v___x_5378_; 
lean_dec_ref(v_fixedParamPerms_5355_);
v___x_5378_ = 0;
return v___x_5378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3___boxed(lean_object* v_fixedParamPerms_5379_, lean_object* v_as_5380_, lean_object* v_i_5381_, lean_object* v_stop_5382_){
_start:
{
size_t v_i_boxed_5383_; size_t v_stop_boxed_5384_; uint8_t v_res_5385_; lean_object* v_r_5386_; 
v_i_boxed_5383_ = lean_unbox_usize(v_i_5381_);
lean_dec(v_i_5381_);
v_stop_boxed_5384_ = lean_unbox_usize(v_stop_5382_);
lean_dec(v_stop_5382_);
v_res_5385_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5379_, v_as_5380_, v_i_boxed_5383_, v_stop_boxed_5384_);
lean_dec_ref(v_as_5380_);
v_r_5386_ = lean_box(v_res_5385_);
return v_r_5386_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object* v_fixedParamPerms_5387_){
_start:
{
lean_object* v_perms_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; 
v_perms_5388_ = lean_ctor_get(v_fixedParamPerms_5387_, 1);
lean_inc_ref(v_perms_5388_);
v___x_5389_ = lean_unsigned_to_nat(0u);
v___x_5390_ = lean_array_get_size(v_perms_5388_);
v___x_5391_ = lean_nat_dec_lt(v___x_5389_, v___x_5390_);
if (v___x_5391_ == 0)
{
uint8_t v___x_5392_; 
lean_dec_ref(v_perms_5388_);
lean_dec_ref(v_fixedParamPerms_5387_);
v___x_5392_ = 1;
return v___x_5392_;
}
else
{
if (v___x_5391_ == 0)
{
lean_dec_ref(v_perms_5388_);
lean_dec_ref(v_fixedParamPerms_5387_);
return v___x_5391_;
}
else
{
size_t v___x_5393_; size_t v___x_5394_; uint8_t v___x_5395_; 
v___x_5393_ = ((size_t)0ULL);
v___x_5394_ = lean_usize_of_nat(v___x_5390_);
v___x_5395_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__3(v_fixedParamPerms_5387_, v_perms_5388_, v___x_5393_, v___x_5394_);
lean_dec_ref(v_perms_5388_);
if (v___x_5395_ == 0)
{
return v___x_5391_;
}
else
{
uint8_t v___x_5396_; 
v___x_5396_ = 0;
return v___x_5396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_fixedArePrefix___boxed(lean_object* v_fixedParamPerms_5397_){
_start:
{
uint8_t v_res_5398_; lean_object* v_r_5399_; 
v_res_5398_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_fixedParamPerms_5397_);
v_r_5399_ = lean_box(v_res_5398_);
return v_r_5399_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(lean_object* v_xs_5400_, lean_object* v_ys_5401_, lean_object* v_hsz_5402_, lean_object* v_x_5403_, lean_object* v_x_5404_){
_start:
{
uint8_t v___x_5405_; 
v___x_5405_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___redArg(v_xs_5400_, v_ys_5401_, v_x_5403_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2___boxed(lean_object* v_xs_5406_, lean_object* v_ys_5407_, lean_object* v_hsz_5408_, lean_object* v_x_5409_, lean_object* v_x_5410_){
_start:
{
uint8_t v_res_5411_; lean_object* v_r_5412_; 
v_res_5411_ = l_Array_isEqvAux___at___00Lean_Elab_FixedParamPerms_fixedArePrefix_spec__2(v_xs_5406_, v_ys_5407_, v_hsz_5408_, v_x_5409_, v_x_5410_);
lean_dec_ref(v_ys_5407_);
lean_dec_ref(v_xs_5406_);
v_r_5412_ = lean_box(v_res_5411_);
return v_r_5412_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; 
v___x_5413_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5414_, 0, v___x_5413_);
lean_ctor_set(v___x_5414_, 1, v___x_5413_);
return v___x_5414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5415_){
_start:
{
lean_object* v___f_5416_; lean_object* v___f_5417_; lean_object* v___f_5418_; lean_object* v___f_5419_; lean_object* v___f_5420_; lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; 
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
lean_ctor_set(v___x_5428_, 0, v___x_5426_);
lean_ctor_set(v___x_5428_, 1, v___x_5427_);
v___x_5429_ = l_instInhabitedOfMonad___redArg(v___x_5425_, v___x_5428_);
v___x_5430_ = lean_panic_fn_borrowed(v___x_5429_, v_msg_5415_);
lean_dec(v___x_5429_);
return v___x_5430_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5431_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5431_);
return v___x_5432_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5433_){
_start:
{
lean_object* v___f_5434_; lean_object* v___f_5435_; lean_object* v___f_5436_; lean_object* v___f_5437_; lean_object* v___f_5438_; lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
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
v___x_5445_ = l_instInhabitedOfMonad___redArg(v___x_5443_, v___x_5444_);
v___x_5446_ = lean_panic_fn_borrowed(v___x_5445_, v_msg_5433_);
lean_dec(v___x_5445_);
return v___x_5446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(lean_object* v___x_5447_, uint8_t v___x_5448_, lean_object* v___x_5449_, lean_object* v___x_5450_, lean_object* v_as_5451_, size_t v_sz_5452_, size_t v_i_5453_, lean_object* v_b_5454_){
_start:
{
lean_object* v_a_5456_; uint8_t v___x_5460_; 
v___x_5460_ = lean_usize_dec_lt(v_i_5453_, v_sz_5452_);
if (v___x_5460_ == 0)
{
return v_b_5454_;
}
else
{
lean_object* v_fst_5461_; lean_object* v_snd_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5484_; 
v_fst_5461_ = lean_ctor_get(v_b_5454_, 0);
v_snd_5462_ = lean_ctor_get(v_b_5454_, 1);
v_isSharedCheck_5484_ = !lean_is_exclusive(v_b_5454_);
if (v_isSharedCheck_5484_ == 0)
{
v___x_5464_ = v_b_5454_;
v_isShared_5465_ = v_isSharedCheck_5484_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_snd_5462_);
lean_inc(v_fst_5461_);
lean_dec(v_b_5454_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5484_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5470_; lean_object* v_a_5471_; lean_object* v___x_5472_; 
v___x_5470_ = lean_box(0);
v_a_5471_ = lean_array_uget_borrowed(v_as_5451_, v_i_5453_);
v___x_5472_ = lean_array_get_borrowed(v___x_5470_, v___x_5447_, v_a_5471_);
if (lean_obj_tag(v___x_5472_) == 1)
{
lean_object* v_val_5473_; uint8_t v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; uint8_t v___x_5477_; 
v_val_5473_ = lean_ctor_get(v___x_5472_, 0);
v___x_5474_ = 0;
v___x_5475_ = lean_box(v___x_5474_);
v___x_5476_ = lean_array_get(v___x_5475_, v_fst_5461_, v_val_5473_);
lean_dec(v___x_5475_);
v___x_5477_ = lean_unbox(v___x_5476_);
lean_dec(v___x_5476_);
if (v___x_5477_ == 0)
{
if (v___x_5448_ == 0)
{
goto v___jp_5466_;
}
else
{
uint8_t v_changed_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; 
lean_del_object(v___x_5464_);
lean_dec(v_snd_5462_);
v_changed_5478_ = lean_nat_dec_eq(v___x_5449_, v___x_5450_);
v___x_5479_ = lean_box(v_changed_5478_);
v___x_5480_ = lean_array_set(v_fst_5461_, v_val_5473_, v___x_5479_);
v___x_5481_ = lean_box(v_changed_5478_);
v___x_5482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5480_);
lean_ctor_set(v___x_5482_, 1, v___x_5481_);
v_a_5456_ = v___x_5482_;
goto v___jp_5455_;
}
}
else
{
goto v___jp_5466_;
}
}
else
{
lean_object* v___x_5483_; 
lean_del_object(v___x_5464_);
v___x_5483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5483_, 0, v_fst_5461_);
lean_ctor_set(v___x_5483_, 1, v_snd_5462_);
v_a_5456_ = v___x_5483_;
goto v___jp_5455_;
}
v___jp_5466_:
{
lean_object* v___x_5468_; 
if (v_isShared_5465_ == 0)
{
v___x_5468_ = v___x_5464_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_fst_5461_);
lean_ctor_set(v_reuseFailAlloc_5469_, 1, v_snd_5462_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
v_a_5456_ = v___x_5468_;
goto v___jp_5455_;
}
}
}
}
v___jp_5455_:
{
size_t v___x_5457_; size_t v___x_5458_; 
v___x_5457_ = ((size_t)1ULL);
v___x_5458_ = lean_usize_add(v_i_5453_, v___x_5457_);
v_i_5453_ = v___x_5458_;
v_b_5454_ = v_a_5456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5___boxed(lean_object* v___x_5485_, lean_object* v___x_5486_, lean_object* v___x_5487_, lean_object* v___x_5488_, lean_object* v_as_5489_, lean_object* v_sz_5490_, lean_object* v_i_5491_, lean_object* v_b_5492_){
_start:
{
uint8_t v___x_7006__boxed_5493_; size_t v_sz_boxed_5494_; size_t v_i_boxed_5495_; lean_object* v_res_5496_; 
v___x_7006__boxed_5493_ = lean_unbox(v___x_5486_);
v_sz_boxed_5494_ = lean_unbox_usize(v_sz_5490_);
lean_dec(v_sz_5490_);
v_i_boxed_5495_ = lean_unbox_usize(v_i_5491_);
lean_dec(v_i_5491_);
v_res_5496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5485_, v___x_7006__boxed_5493_, v___x_5487_, v___x_5488_, v_as_5489_, v_sz_boxed_5494_, v_i_boxed_5495_, v_b_5492_);
lean_dec_ref(v_as_5489_);
lean_dec(v___x_5488_);
lean_dec(v___x_5487_);
lean_dec_ref(v___x_5485_);
return v_res_5496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(lean_object* v_upperBound_5497_, lean_object* v___x_5498_, lean_object* v_fixedParamPerms_5499_, lean_object* v_next_5500_, lean_object* v___x_5501_, lean_object* v___x_5502_, lean_object* v_a_5503_, lean_object* v_b_5504_){
_start:
{
lean_object* v_a_5506_; uint8_t v___x_5510_; 
v___x_5510_ = lean_nat_dec_lt(v_a_5503_, v_upperBound_5497_);
if (v___x_5510_ == 0)
{
lean_dec(v_a_5503_);
return v_b_5504_;
}
else
{
lean_object* v_fst_5511_; lean_object* v_snd_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5548_; 
v_fst_5511_ = lean_ctor_get(v_b_5504_, 0);
v_snd_5512_ = lean_ctor_get(v_b_5504_, 1);
v_isSharedCheck_5548_ = !lean_is_exclusive(v_b_5504_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5514_ = v_b_5504_;
v_isShared_5515_ = v_isSharedCheck_5548_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_snd_5512_);
lean_inc(v_fst_5511_);
lean_dec(v_b_5504_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5548_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5516_; 
v___x_5516_ = lean_array_fget_borrowed(v___x_5498_, v_a_5503_);
if (lean_obj_tag(v___x_5516_) == 1)
{
lean_object* v_val_5517_; uint8_t v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; uint8_t v___x_5521_; 
v_val_5517_ = lean_ctor_get(v___x_5516_, 0);
v___x_5518_ = 0;
v___x_5519_ = lean_box(v___x_5518_);
v___x_5520_ = lean_array_get(v___x_5519_, v_fst_5511_, v_val_5517_);
lean_dec(v___x_5519_);
v___x_5521_ = lean_unbox(v___x_5520_);
if (v___x_5521_ == 0)
{
lean_object* v___x_5523_; 
lean_dec(v___x_5520_);
if (v_isShared_5515_ == 0)
{
v___x_5523_ = v___x_5514_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_fst_5511_);
lean_ctor_set(v_reuseFailAlloc_5524_, 1, v_snd_5512_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
v_a_5506_ = v___x_5523_;
goto v___jp_5505_;
}
}
else
{
lean_object* v_revDeps_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5530_; 
v_revDeps_5525_ = lean_ctor_get(v_fixedParamPerms_5499_, 2);
v___x_5526_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5527_ = lean_array_get_borrowed(v___x_5526_, v_revDeps_5525_, v_next_5500_);
v___x_5528_ = lean_array_get_borrowed(v___x_5526_, v___x_5527_, v_a_5503_);
if (v_isShared_5515_ == 0)
{
v___x_5530_ = v___x_5514_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_fst_5511_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v_snd_5512_);
v___x_5530_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
size_t v_sz_5531_; size_t v___x_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; lean_object* v_fst_5535_; lean_object* v_snd_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5543_; 
v_sz_5531_ = lean_array_size(v___x_5528_);
v___x_5532_ = ((size_t)0ULL);
v___x_5533_ = lean_unbox(v___x_5520_);
lean_dec(v___x_5520_);
v___x_5534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5498_, v___x_5533_, v___x_5501_, v___x_5502_, v___x_5528_, v_sz_5531_, v___x_5532_, v___x_5530_);
v_fst_5535_ = lean_ctor_get(v___x_5534_, 0);
v_snd_5536_ = lean_ctor_get(v___x_5534_, 1);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5538_ = v___x_5534_;
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_snd_5536_);
lean_inc(v_fst_5535_);
lean_dec(v___x_5534_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
if (v_isShared_5539_ == 0)
{
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_fst_5535_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v_snd_5536_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
v_a_5506_ = v___x_5541_;
goto v___jp_5505_;
}
}
}
}
}
else
{
lean_object* v___x_5546_; 
if (v_isShared_5515_ == 0)
{
v___x_5546_ = v___x_5514_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_fst_5511_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_snd_5512_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
v_a_5506_ = v___x_5546_;
goto v___jp_5505_;
}
}
}
}
v___jp_5505_:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; 
v___x_5507_ = lean_unsigned_to_nat(1u);
v___x_5508_ = lean_nat_add(v_a_5503_, v___x_5507_);
lean_dec(v_a_5503_);
v_a_5503_ = v___x_5508_;
v_b_5504_ = v_a_5506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg___boxed(lean_object* v_upperBound_5549_, lean_object* v___x_5550_, lean_object* v_fixedParamPerms_5551_, lean_object* v_next_5552_, lean_object* v___x_5553_, lean_object* v___x_5554_, lean_object* v_a_5555_, lean_object* v_b_5556_){
_start:
{
lean_object* v_res_5557_; 
v_res_5557_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5549_, v___x_5550_, v_fixedParamPerms_5551_, v_next_5552_, v___x_5553_, v___x_5554_, v_a_5555_, v_b_5556_);
lean_dec(v___x_5554_);
lean_dec(v___x_5553_);
lean_dec(v_next_5552_);
lean_dec_ref(v_fixedParamPerms_5551_);
lean_dec_ref(v___x_5550_);
lean_dec(v_upperBound_5549_);
return v_res_5557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(lean_object* v_upperBound_5558_, lean_object* v___x_5559_, lean_object* v___x_5560_, lean_object* v___x_5561_, lean_object* v_fixedParamPerms_5562_, lean_object* v_next_5563_, lean_object* v_a_5564_, lean_object* v_b_5565_){
_start:
{
lean_object* v_a_5567_; uint8_t v___x_5571_; 
v___x_5571_ = lean_nat_dec_lt(v_a_5564_, v_upperBound_5558_);
if (v___x_5571_ == 0)
{
return v_b_5565_;
}
else
{
lean_object* v_fst_5572_; lean_object* v_snd_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5609_; 
v_fst_5572_ = lean_ctor_get(v_b_5565_, 0);
v_snd_5573_ = lean_ctor_get(v_b_5565_, 1);
v_isSharedCheck_5609_ = !lean_is_exclusive(v_b_5565_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5575_ = v_b_5565_;
v_isShared_5576_ = v_isSharedCheck_5609_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_snd_5573_);
lean_inc(v_fst_5572_);
lean_dec(v_b_5565_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5609_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5577_; 
v___x_5577_ = lean_array_fget_borrowed(v___x_5559_, v_a_5564_);
if (lean_obj_tag(v___x_5577_) == 1)
{
lean_object* v_val_5578_; uint8_t v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; uint8_t v___x_5582_; 
v_val_5578_ = lean_ctor_get(v___x_5577_, 0);
v___x_5579_ = 0;
v___x_5580_ = lean_box(v___x_5579_);
v___x_5581_ = lean_array_get(v___x_5580_, v_fst_5572_, v_val_5578_);
lean_dec(v___x_5580_);
v___x_5582_ = lean_unbox(v___x_5581_);
if (v___x_5582_ == 0)
{
lean_object* v___x_5584_; 
lean_dec(v___x_5581_);
if (v_isShared_5576_ == 0)
{
v___x_5584_ = v___x_5575_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_fst_5572_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_snd_5573_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
v_a_5567_ = v___x_5584_;
goto v___jp_5566_;
}
}
else
{
lean_object* v_revDeps_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5591_; 
v_revDeps_5586_ = lean_ctor_get(v_fixedParamPerms_5562_, 2);
v___x_5587_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5588_ = lean_array_get_borrowed(v___x_5587_, v_revDeps_5586_, v_next_5563_);
v___x_5589_ = lean_array_get_borrowed(v___x_5587_, v___x_5588_, v_a_5564_);
if (v_isShared_5576_ == 0)
{
v___x_5591_ = v___x_5575_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_fst_5572_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v_snd_5573_);
v___x_5591_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
size_t v_sz_5592_; size_t v___x_5593_; uint8_t v___x_5594_; lean_object* v___x_5595_; lean_object* v_fst_5596_; lean_object* v_snd_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5604_; 
v_sz_5592_ = lean_array_size(v___x_5589_);
v___x_5593_ = ((size_t)0ULL);
v___x_5594_ = lean_unbox(v___x_5581_);
lean_dec(v___x_5581_);
v___x_5595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5559_, v___x_5594_, v___x_5560_, v___x_5561_, v___x_5589_, v_sz_5592_, v___x_5593_, v___x_5591_);
v_fst_5596_ = lean_ctor_get(v___x_5595_, 0);
v_snd_5597_ = lean_ctor_get(v___x_5595_, 1);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5595_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5599_ = v___x_5595_;
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_snd_5597_);
lean_inc(v_fst_5596_);
lean_dec(v___x_5595_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5602_; 
if (v_isShared_5600_ == 0)
{
v___x_5602_ = v___x_5599_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_fst_5596_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v_snd_5597_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
v_a_5567_ = v___x_5602_;
goto v___jp_5566_;
}
}
}
}
}
else
{
lean_object* v___x_5607_; 
if (v_isShared_5576_ == 0)
{
v___x_5607_ = v___x_5575_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_fst_5572_);
lean_ctor_set(v_reuseFailAlloc_5608_, 1, v_snd_5573_);
v___x_5607_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
v_a_5567_ = v___x_5607_;
goto v___jp_5566_;
}
}
}
}
v___jp_5566_:
{
lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; 
v___x_5568_ = lean_unsigned_to_nat(1u);
v___x_5569_ = lean_nat_add(v_a_5564_, v___x_5568_);
v___x_5570_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_5558_, v___x_5559_, v_fixedParamPerms_5562_, v_next_5563_, v___x_5560_, v___x_5561_, v___x_5569_, v_a_5567_);
return v___x_5570_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg___boxed(lean_object* v_upperBound_5610_, lean_object* v___x_5611_, lean_object* v___x_5612_, lean_object* v___x_5613_, lean_object* v_fixedParamPerms_5614_, lean_object* v_next_5615_, lean_object* v_a_5616_, lean_object* v_b_5617_){
_start:
{
lean_object* v_res_5618_; 
v_res_5618_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_5610_, v___x_5611_, v___x_5612_, v___x_5613_, v_fixedParamPerms_5614_, v_next_5615_, v_a_5616_, v_b_5617_);
lean_dec(v_a_5616_);
lean_dec(v_next_5615_);
lean_dec_ref(v_fixedParamPerms_5614_);
lean_dec(v___x_5613_);
lean_dec(v___x_5612_);
lean_dec_ref(v___x_5611_);
lean_dec(v_upperBound_5610_);
return v_res_5618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(lean_object* v_upperBound_5619_, lean_object* v___x_5620_, lean_object* v___x_5621_, lean_object* v___x_5622_, lean_object* v_fixedParamPerms_5623_, lean_object* v_a_5624_, lean_object* v_b_5625_){
_start:
{
uint8_t v___x_5626_; 
v___x_5626_ = lean_nat_dec_lt(v_a_5624_, v_upperBound_5619_);
if (v___x_5626_ == 0)
{
lean_dec(v_a_5624_);
return v_b_5625_;
}
else
{
lean_object* v_fst_5627_; lean_object* v_snd_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5651_; 
v_fst_5627_ = lean_ctor_get(v_b_5625_, 0);
v_snd_5628_ = lean_ctor_get(v_b_5625_, 1);
v_isSharedCheck_5651_ = !lean_is_exclusive(v_b_5625_);
if (v_isSharedCheck_5651_ == 0)
{
v___x_5630_ = v_b_5625_;
v_isShared_5631_ = v_isSharedCheck_5651_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_snd_5628_);
lean_inc(v_fst_5627_);
lean_dec(v_b_5625_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5651_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5636_; 
v___x_5632_ = lean_array_fget_borrowed(v___x_5620_, v_a_5624_);
v___x_5633_ = lean_array_get_size(v___x_5632_);
v___x_5634_ = lean_unsigned_to_nat(0u);
if (v_isShared_5631_ == 0)
{
v___x_5636_ = v___x_5630_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v_snd_5628_);
v___x_5636_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
lean_object* v___x_5637_; lean_object* v_fst_5638_; lean_object* v_snd_5639_; lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5649_; 
v___x_5637_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v___x_5633_, v___x_5632_, v___x_5621_, v___x_5622_, v_fixedParamPerms_5623_, v_a_5624_, v___x_5634_, v___x_5636_);
v_fst_5638_ = lean_ctor_get(v___x_5637_, 0);
v_snd_5639_ = lean_ctor_get(v___x_5637_, 1);
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5637_);
if (v_isSharedCheck_5649_ == 0)
{
v___x_5641_ = v___x_5637_;
v_isShared_5642_ = v_isSharedCheck_5649_;
goto v_resetjp_5640_;
}
else
{
lean_inc(v_snd_5639_);
lean_inc(v_fst_5638_);
lean_dec(v___x_5637_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5649_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v___x_5644_; 
if (v_isShared_5642_ == 0)
{
v___x_5644_ = v___x_5641_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v_fst_5638_);
lean_ctor_set(v_reuseFailAlloc_5648_, 1, v_snd_5639_);
v___x_5644_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
lean_object* v___x_5645_; lean_object* v___x_5646_; 
v___x_5645_ = lean_unsigned_to_nat(1u);
v___x_5646_ = lean_nat_add(v_a_5624_, v___x_5645_);
lean_dec(v_a_5624_);
v_a_5624_ = v___x_5646_;
v_b_5625_ = v___x_5644_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg___boxed(lean_object* v_upperBound_5652_, lean_object* v___x_5653_, lean_object* v___x_5654_, lean_object* v___x_5655_, lean_object* v_fixedParamPerms_5656_, lean_object* v_a_5657_, lean_object* v_b_5658_){
_start:
{
lean_object* v_res_5659_; 
v_res_5659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_5652_, v___x_5653_, v___x_5654_, v___x_5655_, v_fixedParamPerms_5656_, v_a_5657_, v_b_5658_);
lean_dec_ref(v_fixedParamPerms_5656_);
lean_dec(v___x_5655_);
lean_dec(v___x_5654_);
lean_dec_ref(v___x_5653_);
lean_dec(v_upperBound_5652_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(lean_object* v___x_5660_, lean_object* v___x_5661_, lean_object* v___x_5662_, lean_object* v_fixedParamPerms_5663_, lean_object* v_a_5664_){
_start:
{
lean_object* v_snd_5665_; uint8_t v___x_5666_; 
v_snd_5665_ = lean_ctor_get(v_a_5664_, 1);
v___x_5666_ = lean_unbox(v_snd_5665_);
if (v___x_5666_ == 0)
{
lean_object* v_fst_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5674_; 
lean_inc(v_snd_5665_);
v_fst_5667_ = lean_ctor_get(v_a_5664_, 0);
v_isSharedCheck_5674_ = !lean_is_exclusive(v_a_5664_);
if (v_isSharedCheck_5674_ == 0)
{
lean_object* v_unused_5675_; 
v_unused_5675_ = lean_ctor_get(v_a_5664_, 1);
lean_dec(v_unused_5675_);
v___x_5669_ = v_a_5664_;
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_fst_5667_);
lean_dec(v_a_5664_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v___x_5672_; 
if (v_isShared_5670_ == 0)
{
v___x_5672_ = v___x_5669_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_fst_5667_);
lean_ctor_set(v_reuseFailAlloc_5673_, 1, v_snd_5665_);
v___x_5672_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
return v___x_5672_;
}
}
}
else
{
lean_object* v_fst_5676_; lean_object* v___x_5678_; uint8_t v_isShared_5679_; uint8_t v_isSharedCheck_5697_; 
v_fst_5676_ = lean_ctor_get(v_a_5664_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v_a_5664_);
if (v_isSharedCheck_5697_ == 0)
{
lean_object* v_unused_5698_; 
v_unused_5698_ = lean_ctor_get(v_a_5664_, 1);
lean_dec(v_unused_5698_);
v___x_5678_ = v_a_5664_;
v_isShared_5679_ = v_isSharedCheck_5697_;
goto v_resetjp_5677_;
}
else
{
lean_inc(v_fst_5676_);
lean_dec(v_a_5664_);
v___x_5678_ = lean_box(0);
v_isShared_5679_ = v_isSharedCheck_5697_;
goto v_resetjp_5677_;
}
v_resetjp_5677_:
{
uint8_t v_changed_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5684_; 
v_changed_5680_ = 0;
v___x_5681_ = lean_unsigned_to_nat(0u);
v___x_5682_ = lean_box(v_changed_5680_);
if (v_isShared_5679_ == 0)
{
lean_ctor_set(v___x_5678_, 1, v___x_5682_);
v___x_5684_ = v___x_5678_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_fst_5676_);
lean_ctor_set(v_reuseFailAlloc_5696_, 1, v___x_5682_);
v___x_5684_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
lean_object* v___x_5685_; lean_object* v_fst_5686_; lean_object* v_snd_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5695_; 
v___x_5685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v___x_5660_, v___x_5661_, v___x_5662_, v___x_5660_, v_fixedParamPerms_5663_, v___x_5681_, v___x_5684_);
v_fst_5686_ = lean_ctor_get(v___x_5685_, 0);
v_snd_5687_ = lean_ctor_get(v___x_5685_, 1);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___x_5685_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5689_ = v___x_5685_;
v_isShared_5690_ = v_isSharedCheck_5695_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_snd_5687_);
lean_inc(v_fst_5686_);
lean_dec(v___x_5685_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5695_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v___x_5692_; 
if (v_isShared_5690_ == 0)
{
v___x_5692_ = v___x_5689_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_fst_5686_);
lean_ctor_set(v_reuseFailAlloc_5694_, 1, v_snd_5687_);
v___x_5692_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
v_a_5664_ = v___x_5692_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg___boxed(lean_object* v___x_5699_, lean_object* v___x_5700_, lean_object* v___x_5701_, lean_object* v_fixedParamPerms_5702_, lean_object* v_a_5703_){
_start:
{
lean_object* v_res_5704_; 
v_res_5704_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_5699_, v___x_5700_, v___x_5701_, v_fixedParamPerms_5702_, v_a_5703_);
lean_dec_ref(v_fixedParamPerms_5702_);
lean_dec(v___x_5701_);
lean_dec_ref(v___x_5700_);
lean_dec(v___x_5699_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(lean_object* v_upperBound_5705_, lean_object* v_a_5706_, lean_object* v_b_5707_){
_start:
{
lean_object* v_a_5709_; uint8_t v___x_5713_; 
v___x_5713_ = lean_nat_dec_lt(v_a_5706_, v_upperBound_5705_);
if (v___x_5713_ == 0)
{
lean_dec(v_a_5706_);
return v_b_5707_;
}
else
{
lean_object* v_snd_5714_; lean_object* v_snd_5715_; lean_object* v_snd_5716_; lean_object* v_snd_5717_; lean_object* v_fst_5718_; lean_object* v___x_5720_; uint8_t v_isShared_5721_; uint8_t v_isSharedCheck_5830_; 
v_snd_5714_ = lean_ctor_get(v_b_5707_, 1);
lean_inc(v_snd_5714_);
v_snd_5715_ = lean_ctor_get(v_snd_5714_, 1);
lean_inc(v_snd_5715_);
v_snd_5716_ = lean_ctor_get(v_snd_5715_, 1);
lean_inc(v_snd_5716_);
v_snd_5717_ = lean_ctor_get(v_snd_5716_, 1);
lean_inc(v_snd_5717_);
v_fst_5718_ = lean_ctor_get(v_b_5707_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v_b_5707_);
if (v_isSharedCheck_5830_ == 0)
{
lean_object* v_unused_5831_; 
v_unused_5831_ = lean_ctor_get(v_b_5707_, 1);
lean_dec(v_unused_5831_);
v___x_5720_ = v_b_5707_;
v_isShared_5721_ = v_isSharedCheck_5830_;
goto v_resetjp_5719_;
}
else
{
lean_inc(v_fst_5718_);
lean_dec(v_b_5707_);
v___x_5720_ = lean_box(0);
v_isShared_5721_ = v_isSharedCheck_5830_;
goto v_resetjp_5719_;
}
v_resetjp_5719_:
{
lean_object* v_fst_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5828_; 
v_fst_5722_ = lean_ctor_get(v_snd_5714_, 0);
v_isSharedCheck_5828_ = !lean_is_exclusive(v_snd_5714_);
if (v_isSharedCheck_5828_ == 0)
{
lean_object* v_unused_5829_; 
v_unused_5829_ = lean_ctor_get(v_snd_5714_, 1);
lean_dec(v_unused_5829_);
v___x_5724_ = v_snd_5714_;
v_isShared_5725_ = v_isSharedCheck_5828_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_fst_5722_);
lean_dec(v_snd_5714_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5828_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v_fst_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5826_; 
v_fst_5726_ = lean_ctor_get(v_snd_5715_, 0);
v_isSharedCheck_5826_ = !lean_is_exclusive(v_snd_5715_);
if (v_isSharedCheck_5826_ == 0)
{
lean_object* v_unused_5827_; 
v_unused_5827_ = lean_ctor_get(v_snd_5715_, 1);
lean_dec(v_unused_5827_);
v___x_5728_ = v_snd_5715_;
v_isShared_5729_ = v_isSharedCheck_5826_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_fst_5726_);
lean_dec(v_snd_5715_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5826_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v_fst_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5824_; 
v_fst_5730_ = lean_ctor_get(v_snd_5716_, 0);
v_isSharedCheck_5824_ = !lean_is_exclusive(v_snd_5716_);
if (v_isSharedCheck_5824_ == 0)
{
lean_object* v_unused_5825_; 
v_unused_5825_ = lean_ctor_get(v_snd_5716_, 1);
lean_dec(v_unused_5825_);
v___x_5732_ = v_snd_5716_;
v_isShared_5733_ = v_isSharedCheck_5824_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_fst_5730_);
lean_dec(v_snd_5716_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5824_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v_array_5734_; lean_object* v_start_5735_; lean_object* v_stop_5736_; uint8_t v___x_5737_; 
v_array_5734_ = lean_ctor_get(v_snd_5717_, 0);
v_start_5735_ = lean_ctor_get(v_snd_5717_, 1);
v_stop_5736_ = lean_ctor_get(v_snd_5717_, 2);
v___x_5737_ = lean_nat_dec_lt(v_start_5735_, v_stop_5736_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5739_; 
lean_dec(v_a_5706_);
if (v_isShared_5733_ == 0)
{
v___x_5739_ = v___x_5732_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_fst_5730_);
lean_ctor_set(v_reuseFailAlloc_5749_, 1, v_snd_5717_);
v___x_5739_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
lean_object* v___x_5741_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5739_);
v___x_5741_ = v___x_5728_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5748_; 
v_reuseFailAlloc_5748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5748_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5748_, 1, v___x_5739_);
v___x_5741_ = v_reuseFailAlloc_5748_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
lean_object* v___x_5743_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5741_);
v___x_5743_ = v___x_5724_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v_fst_5722_);
lean_ctor_set(v_reuseFailAlloc_5747_, 1, v___x_5741_);
v___x_5743_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
lean_object* v___x_5745_; 
if (v_isShared_5721_ == 0)
{
lean_ctor_set(v___x_5720_, 1, v___x_5743_);
v___x_5745_ = v___x_5720_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_fst_5718_);
lean_ctor_set(v_reuseFailAlloc_5746_, 1, v___x_5743_);
v___x_5745_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
return v___x_5745_;
}
}
}
}
}
else
{
lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5820_; 
lean_inc(v_stop_5736_);
lean_inc(v_start_5735_);
lean_inc_ref(v_array_5734_);
v_isSharedCheck_5820_ = !lean_is_exclusive(v_snd_5717_);
if (v_isSharedCheck_5820_ == 0)
{
lean_object* v_unused_5821_; lean_object* v_unused_5822_; lean_object* v_unused_5823_; 
v_unused_5821_ = lean_ctor_get(v_snd_5717_, 2);
lean_dec(v_unused_5821_);
v_unused_5822_ = lean_ctor_get(v_snd_5717_, 1);
lean_dec(v_unused_5822_);
v_unused_5823_ = lean_ctor_get(v_snd_5717_, 0);
lean_dec(v_unused_5823_);
v___x_5751_ = v_snd_5717_;
v_isShared_5752_ = v_isSharedCheck_5820_;
goto v_resetjp_5750_;
}
else
{
lean_dec(v_snd_5717_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5820_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v_array_5753_; lean_object* v_start_5754_; lean_object* v_stop_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5760_; 
v_array_5753_ = lean_ctor_get(v_fst_5730_, 0);
v_start_5754_ = lean_ctor_get(v_fst_5730_, 1);
v_stop_5755_ = lean_ctor_get(v_fst_5730_, 2);
v___x_5756_ = lean_array_fget(v_array_5734_, v_start_5735_);
v___x_5757_ = lean_unsigned_to_nat(1u);
v___x_5758_ = lean_nat_add(v_start_5735_, v___x_5757_);
lean_dec(v_start_5735_);
if (v_isShared_5752_ == 0)
{
lean_ctor_set(v___x_5751_, 1, v___x_5758_);
v___x_5760_ = v___x_5751_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_array_5734_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v___x_5758_);
lean_ctor_set(v_reuseFailAlloc_5819_, 2, v_stop_5736_);
v___x_5760_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
uint8_t v___x_5761_; 
v___x_5761_ = lean_nat_dec_lt(v_start_5754_, v_stop_5755_);
if (v___x_5761_ == 0)
{
lean_object* v___x_5763_; 
lean_dec(v___x_5756_);
lean_dec(v_a_5706_);
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5760_);
v___x_5763_ = v___x_5732_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_fst_5730_);
lean_ctor_set(v_reuseFailAlloc_5773_, 1, v___x_5760_);
v___x_5763_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
lean_object* v___x_5765_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5763_);
v___x_5765_ = v___x_5728_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5772_, 1, v___x_5763_);
v___x_5765_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
lean_object* v___x_5767_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5765_);
v___x_5767_ = v___x_5724_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_fst_5722_);
lean_ctor_set(v_reuseFailAlloc_5771_, 1, v___x_5765_);
v___x_5767_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
lean_object* v___x_5769_; 
if (v_isShared_5721_ == 0)
{
lean_ctor_set(v___x_5720_, 1, v___x_5767_);
v___x_5769_ = v___x_5720_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_fst_5718_);
lean_ctor_set(v_reuseFailAlloc_5770_, 1, v___x_5767_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
return v___x_5769_;
}
}
}
}
}
else
{
lean_object* v___x_5775_; uint8_t v_isShared_5776_; uint8_t v_isSharedCheck_5815_; 
lean_inc(v_stop_5755_);
lean_inc(v_start_5754_);
lean_inc_ref(v_array_5753_);
v_isSharedCheck_5815_ = !lean_is_exclusive(v_fst_5730_);
if (v_isSharedCheck_5815_ == 0)
{
lean_object* v_unused_5816_; lean_object* v_unused_5817_; lean_object* v_unused_5818_; 
v_unused_5816_ = lean_ctor_get(v_fst_5730_, 2);
lean_dec(v_unused_5816_);
v_unused_5817_ = lean_ctor_get(v_fst_5730_, 1);
lean_dec(v_unused_5817_);
v_unused_5818_ = lean_ctor_get(v_fst_5730_, 0);
lean_dec(v_unused_5818_);
v___x_5775_ = v_fst_5730_;
v_isShared_5776_ = v_isSharedCheck_5815_;
goto v_resetjp_5774_;
}
else
{
lean_dec(v_fst_5730_);
v___x_5775_ = lean_box(0);
v_isShared_5776_ = v_isSharedCheck_5815_;
goto v_resetjp_5774_;
}
v_resetjp_5774_:
{
lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5780_; 
v___x_5777_ = lean_array_fget(v_array_5753_, v_start_5754_);
v___x_5778_ = lean_nat_add(v_start_5754_, v___x_5757_);
lean_dec(v_start_5754_);
if (v_isShared_5776_ == 0)
{
lean_ctor_set(v___x_5775_, 1, v___x_5778_);
v___x_5780_ = v___x_5775_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5814_; 
v_reuseFailAlloc_5814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_array_5753_);
lean_ctor_set(v_reuseFailAlloc_5814_, 1, v___x_5778_);
lean_ctor_set(v_reuseFailAlloc_5814_, 2, v_stop_5755_);
v___x_5780_ = v_reuseFailAlloc_5814_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
uint8_t v___x_5781_; 
v___x_5781_ = lean_unbox(v___x_5777_);
lean_dec(v___x_5777_);
if (v___x_5781_ == 0)
{
lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5787_; 
v___x_5782_ = lean_array_get_size(v_fst_5726_);
v___x_5783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5783_, 0, v___x_5782_);
v___x_5784_ = lean_array_push(v_fst_5718_, v___x_5783_);
v___x_5785_ = lean_array_push(v_fst_5726_, v___x_5756_);
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5760_);
lean_ctor_set(v___x_5732_, 0, v___x_5780_);
v___x_5787_ = v___x_5732_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5780_);
lean_ctor_set(v_reuseFailAlloc_5797_, 1, v___x_5760_);
v___x_5787_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
lean_object* v___x_5789_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5787_);
lean_ctor_set(v___x_5728_, 0, v___x_5785_);
v___x_5789_ = v___x_5728_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5796_; 
v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5785_);
lean_ctor_set(v_reuseFailAlloc_5796_, 1, v___x_5787_);
v___x_5789_ = v_reuseFailAlloc_5796_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
lean_object* v___x_5791_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5789_);
v___x_5791_ = v___x_5724_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_fst_5722_);
lean_ctor_set(v_reuseFailAlloc_5795_, 1, v___x_5789_);
v___x_5791_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
lean_object* v___x_5793_; 
if (v_isShared_5721_ == 0)
{
lean_ctor_set(v___x_5720_, 1, v___x_5791_);
lean_ctor_set(v___x_5720_, 0, v___x_5784_);
v___x_5793_ = v___x_5720_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5784_);
lean_ctor_set(v_reuseFailAlloc_5794_, 1, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
v_a_5709_ = v___x_5793_;
goto v___jp_5708_;
}
}
}
}
}
else
{
lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5803_; 
v___x_5798_ = lean_box(0);
v___x_5799_ = lean_array_push(v_fst_5718_, v___x_5798_);
v___x_5800_ = l_Lean_Expr_fvarId_x21(v___x_5756_);
lean_dec(v___x_5756_);
v___x_5801_ = lean_array_push(v_fst_5722_, v___x_5800_);
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5760_);
lean_ctor_set(v___x_5732_, 0, v___x_5780_);
v___x_5803_ = v___x_5732_;
goto v_reusejp_5802_;
}
else
{
lean_object* v_reuseFailAlloc_5813_; 
v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5780_);
lean_ctor_set(v_reuseFailAlloc_5813_, 1, v___x_5760_);
v___x_5803_ = v_reuseFailAlloc_5813_;
goto v_reusejp_5802_;
}
v_reusejp_5802_:
{
lean_object* v___x_5805_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5803_);
v___x_5805_ = v___x_5728_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5812_, 1, v___x_5803_);
v___x_5805_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
lean_object* v___x_5807_; 
if (v_isShared_5725_ == 0)
{
lean_ctor_set(v___x_5724_, 1, v___x_5805_);
lean_ctor_set(v___x_5724_, 0, v___x_5801_);
v___x_5807_ = v___x_5724_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v___x_5801_);
lean_ctor_set(v_reuseFailAlloc_5811_, 1, v___x_5805_);
v___x_5807_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
lean_object* v___x_5809_; 
if (v_isShared_5721_ == 0)
{
lean_ctor_set(v___x_5720_, 1, v___x_5807_);
lean_ctor_set(v___x_5720_, 0, v___x_5799_);
v___x_5809_ = v___x_5720_;
goto v_reusejp_5808_;
}
else
{
lean_object* v_reuseFailAlloc_5810_; 
v_reuseFailAlloc_5810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5810_, 0, v___x_5799_);
lean_ctor_set(v_reuseFailAlloc_5810_, 1, v___x_5807_);
v___x_5809_ = v_reuseFailAlloc_5810_;
goto v_reusejp_5808_;
}
v_reusejp_5808_:
{
v_a_5709_ = v___x_5809_;
goto v___jp_5708_;
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
v___jp_5708_:
{
lean_object* v___x_5710_; lean_object* v___x_5711_; 
v___x_5710_ = lean_unsigned_to_nat(1u);
v___x_5711_ = lean_nat_add(v_a_5706_, v___x_5710_);
lean_dec(v_a_5706_);
v_a_5706_ = v___x_5711_;
v_b_5707_ = v_a_5709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg___boxed(lean_object* v_upperBound_5832_, lean_object* v_a_5833_, lean_object* v_b_5834_){
_start:
{
lean_object* v_res_5835_; 
v_res_5835_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_5832_, v_a_5833_, v_b_5834_);
lean_dec(v_upperBound_5832_);
return v_res_5835_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(lean_object* v_as_5836_, size_t v_i_5837_, size_t v_stop_5838_){
_start:
{
uint8_t v___x_5839_; 
v___x_5839_ = lean_usize_dec_eq(v_i_5837_, v_stop_5838_);
if (v___x_5839_ == 0)
{
lean_object* v___x_5840_; uint8_t v___x_5841_; 
v___x_5840_ = lean_array_uget_borrowed(v_as_5836_, v_i_5837_);
v___x_5841_ = l_Lean_Expr_isFVar(v___x_5840_);
if (v___x_5841_ == 0)
{
uint8_t v___x_5842_; 
v___x_5842_ = 1;
return v___x_5842_;
}
else
{
size_t v___x_5843_; size_t v___x_5844_; 
v___x_5843_ = ((size_t)1ULL);
v___x_5844_ = lean_usize_add(v_i_5837_, v___x_5843_);
v_i_5837_ = v___x_5844_;
goto _start;
}
}
else
{
uint8_t v___x_5846_; 
v___x_5846_ = 0;
return v___x_5846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11___boxed(lean_object* v_as_5847_, lean_object* v_i_5848_, lean_object* v_stop_5849_){
_start:
{
size_t v_i_boxed_5850_; size_t v_stop_boxed_5851_; uint8_t v_res_5852_; lean_object* v_r_5853_; 
v_i_boxed_5850_ = lean_unbox_usize(v_i_5848_);
lean_dec(v_i_5848_);
v_stop_boxed_5851_ = lean_unbox_usize(v_stop_5849_);
lean_dec(v_stop_5849_);
v_res_5852_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_as_5847_, v_i_boxed_5850_, v_stop_boxed_5851_);
lean_dec_ref(v_as_5847_);
v_r_5853_ = lean_box(v_res_5852_);
return v_r_5853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(lean_object* v___x_5854_, size_t v_sz_5855_, size_t v_i_5856_, lean_object* v_bs_5857_){
_start:
{
uint8_t v___x_5858_; 
v___x_5858_ = lean_usize_dec_lt(v_i_5856_, v_sz_5855_);
if (v___x_5858_ == 0)
{
return v_bs_5857_;
}
else
{
lean_object* v_v_5859_; lean_object* v___x_5860_; lean_object* v_bs_x27_5861_; lean_object* v___y_5863_; 
v_v_5859_ = lean_array_uget(v_bs_5857_, v_i_5856_);
v___x_5860_ = lean_unsigned_to_nat(0u);
v_bs_x27_5861_ = lean_array_uset(v_bs_5857_, v_i_5856_, v___x_5860_);
if (lean_obj_tag(v_v_5859_) == 0)
{
v___y_5863_ = v_v_5859_;
goto v___jp_5862_;
}
else
{
lean_object* v_val_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v_val_5868_ = lean_ctor_get(v_v_5859_, 0);
lean_inc(v_val_5868_);
lean_dec_ref_known(v_v_5859_, 1);
v___x_5869_ = lean_box(0);
v___x_5870_ = lean_array_get_borrowed(v___x_5869_, v___x_5854_, v_val_5868_);
lean_dec(v_val_5868_);
lean_inc(v___x_5870_);
v___y_5863_ = v___x_5870_;
goto v___jp_5862_;
}
v___jp_5862_:
{
size_t v___x_5864_; size_t v___x_5865_; lean_object* v___x_5866_; 
v___x_5864_ = ((size_t)1ULL);
v___x_5865_ = lean_usize_add(v_i_5856_, v___x_5864_);
v___x_5866_ = lean_array_uset(v_bs_x27_5861_, v_i_5856_, v___y_5863_);
v_i_5856_ = v___x_5865_;
v_bs_5857_ = v___x_5866_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1___boxed(lean_object* v___x_5871_, lean_object* v_sz_5872_, lean_object* v_i_5873_, lean_object* v_bs_5874_){
_start:
{
size_t v_sz_boxed_5875_; size_t v_i_boxed_5876_; lean_object* v_res_5877_; 
v_sz_boxed_5875_ = lean_unbox_usize(v_sz_5872_);
lean_dec(v_sz_5872_);
v_i_boxed_5876_ = lean_unbox_usize(v_i_5873_);
lean_dec(v_i_5873_);
v_res_5877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5871_, v_sz_boxed_5875_, v_i_boxed_5876_, v_bs_5874_);
lean_dec_ref(v___x_5871_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(lean_object* v___x_5878_, size_t v_sz_5879_, size_t v_i_5880_, lean_object* v_bs_5881_){
_start:
{
uint8_t v___x_5882_; 
v___x_5882_ = lean_usize_dec_lt(v_i_5880_, v_sz_5879_);
if (v___x_5882_ == 0)
{
return v_bs_5881_;
}
else
{
lean_object* v_v_5883_; lean_object* v___x_5884_; lean_object* v_bs_x27_5885_; size_t v_sz_5886_; size_t v___x_5887_; lean_object* v___x_5888_; size_t v___x_5889_; size_t v___x_5890_; lean_object* v___x_5891_; 
v_v_5883_ = lean_array_uget(v_bs_5881_, v_i_5880_);
v___x_5884_ = lean_unsigned_to_nat(0u);
v_bs_x27_5885_ = lean_array_uset(v_bs_5881_, v_i_5880_, v___x_5884_);
v_sz_5886_ = lean_array_size(v_v_5883_);
v___x_5887_ = ((size_t)0ULL);
v___x_5888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__1(v___x_5878_, v_sz_5886_, v___x_5887_, v_v_5883_);
v___x_5889_ = ((size_t)1ULL);
v___x_5890_ = lean_usize_add(v_i_5880_, v___x_5889_);
v___x_5891_ = lean_array_uset(v_bs_x27_5885_, v_i_5880_, v___x_5888_);
v_i_5880_ = v___x_5890_;
v_bs_5881_ = v___x_5891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2___boxed(lean_object* v___x_5893_, lean_object* v_sz_5894_, lean_object* v_i_5895_, lean_object* v_bs_5896_){
_start:
{
size_t v_sz_boxed_5897_; size_t v_i_boxed_5898_; lean_object* v_res_5899_; 
v_sz_boxed_5897_ = lean_unbox_usize(v_sz_5894_);
lean_dec(v_sz_5894_);
v_i_boxed_5898_ = lean_unbox_usize(v_i_5895_);
lean_dec(v_i_5895_);
v_res_5899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v___x_5893_, v_sz_boxed_5897_, v_i_boxed_5898_, v_bs_5896_);
lean_dec_ref(v___x_5893_);
return v_res_5899_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2(void){
_start:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; 
v___x_5902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__1));
v___x_5903_ = lean_unsigned_to_nat(6u);
v___x_5904_ = lean_unsigned_to_nat(463u);
v___x_5905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_5906_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_5907_ = l_mkPanicMessageWithDecl(v___x_5906_, v___x_5905_, v___x_5904_, v___x_5903_, v___x_5902_);
return v___x_5907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(lean_object* v___x_5908_, lean_object* v___x_5909_, lean_object* v___x_5910_, lean_object* v_as_5911_, size_t v_sz_5912_, size_t v_i_5913_, lean_object* v_b_5914_){
_start:
{
lean_object* v_a_5916_; uint8_t v___x_5920_; 
v___x_5920_ = lean_usize_dec_lt(v_i_5913_, v_sz_5912_);
if (v___x_5920_ == 0)
{
return v_b_5914_;
}
else
{
lean_object* v_a_5921_; lean_object* v___x_5922_; uint8_t v___x_5923_; 
v_a_5921_ = lean_array_uget_borrowed(v_as_5911_, v_i_5913_);
v___x_5922_ = lean_array_get_size(v___x_5908_);
v___x_5923_ = lean_nat_dec_lt(v_a_5921_, v___x_5922_);
if (v___x_5923_ == 0)
{
lean_object* v___x_5924_; lean_object* v___x_5925_; 
lean_dec_ref(v_b_5914_);
v___x_5924_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__2);
v___x_5925_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(v___x_5924_);
if (lean_obj_tag(v___x_5925_) == 0)
{
lean_object* v_a_5926_; 
v_a_5926_ = lean_ctor_get(v___x_5925_, 0);
lean_inc(v_a_5926_);
lean_dec_ref_known(v___x_5925_, 1);
return v_a_5926_;
}
else
{
lean_object* v_a_5927_; 
v_a_5927_ = lean_ctor_get(v___x_5925_, 0);
lean_inc(v_a_5927_);
lean_dec_ref_known(v___x_5925_, 1);
v_a_5916_ = v_a_5927_;
goto v___jp_5915_;
}
}
else
{
lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5928_ = lean_box(0);
v___x_5929_ = lean_array_get_borrowed(v___x_5928_, v___x_5908_, v_a_5921_);
if (lean_obj_tag(v___x_5929_) == 1)
{
lean_object* v_val_5930_; uint8_t v_changed_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; 
v_val_5930_ = lean_ctor_get(v___x_5929_, 0);
v_changed_5931_ = lean_nat_dec_eq(v___x_5909_, v___x_5910_);
v___x_5932_ = lean_box(v_changed_5931_);
v___x_5933_ = lean_array_set(v_b_5914_, v_val_5930_, v___x_5932_);
v_a_5916_ = v___x_5933_;
goto v___jp_5915_;
}
else
{
v_a_5916_ = v_b_5914_;
goto v___jp_5915_;
}
}
}
v___jp_5915_:
{
size_t v___x_5917_; size_t v___x_5918_; 
v___x_5917_ = ((size_t)1ULL);
v___x_5918_ = lean_usize_add(v_i_5913_, v___x_5917_);
v_i_5913_ = v___x_5918_;
v_b_5914_ = v_a_5916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___boxed(lean_object* v___x_5934_, lean_object* v___x_5935_, lean_object* v___x_5936_, lean_object* v_as_5937_, lean_object* v_sz_5938_, lean_object* v_i_5939_, lean_object* v_b_5940_){
_start:
{
size_t v_sz_boxed_5941_; size_t v_i_boxed_5942_; lean_object* v_res_5943_; 
v_sz_boxed_5941_ = lean_unbox_usize(v_sz_5938_);
lean_dec(v_sz_5938_);
v_i_boxed_5942_ = lean_unbox_usize(v_i_5939_);
lean_dec(v_i_5939_);
v_res_5943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5934_, v___x_5935_, v___x_5936_, v_as_5937_, v_sz_boxed_5941_, v_i_boxed_5942_, v_b_5940_);
lean_dec_ref(v_as_5937_);
lean_dec(v___x_5936_);
lean_dec(v___x_5935_);
lean_dec_ref(v___x_5934_);
return v_res_5943_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(lean_object* v_upperBound_5944_, lean_object* v___x_5945_, lean_object* v___x_5946_, lean_object* v_a_5947_, lean_object* v_b_5948_){
_start:
{
uint8_t v___x_5949_; 
v___x_5949_ = lean_nat_dec_lt(v_a_5947_, v_upperBound_5944_);
if (v___x_5949_ == 0)
{
lean_dec(v_a_5947_);
return v_b_5948_;
}
else
{
lean_object* v_snd_5950_; lean_object* v_snd_5951_; lean_object* v_fst_5952_; lean_object* v___x_5954_; uint8_t v_isShared_5955_; uint8_t v_isSharedCheck_6018_; 
v_snd_5950_ = lean_ctor_get(v_b_5948_, 1);
lean_inc(v_snd_5950_);
v_snd_5951_ = lean_ctor_get(v_snd_5950_, 1);
lean_inc(v_snd_5951_);
v_fst_5952_ = lean_ctor_get(v_b_5948_, 0);
v_isSharedCheck_6018_ = !lean_is_exclusive(v_b_5948_);
if (v_isSharedCheck_6018_ == 0)
{
lean_object* v_unused_6019_; 
v_unused_6019_ = lean_ctor_get(v_b_5948_, 1);
lean_dec(v_unused_6019_);
v___x_5954_ = v_b_5948_;
v_isShared_5955_ = v_isSharedCheck_6018_;
goto v_resetjp_5953_;
}
else
{
lean_inc(v_fst_5952_);
lean_dec(v_b_5948_);
v___x_5954_ = lean_box(0);
v_isShared_5955_ = v_isSharedCheck_6018_;
goto v_resetjp_5953_;
}
v_resetjp_5953_:
{
lean_object* v_fst_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_6016_; 
v_fst_5956_ = lean_ctor_get(v_snd_5950_, 0);
v_isSharedCheck_6016_ = !lean_is_exclusive(v_snd_5950_);
if (v_isSharedCheck_6016_ == 0)
{
lean_object* v_unused_6017_; 
v_unused_6017_ = lean_ctor_get(v_snd_5950_, 1);
lean_dec(v_unused_6017_);
v___x_5958_ = v_snd_5950_;
v_isShared_5959_ = v_isSharedCheck_6016_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_fst_5956_);
lean_dec(v_snd_5950_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_6016_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v_array_5960_; lean_object* v_start_5961_; lean_object* v_stop_5962_; uint8_t v___x_5963_; 
v_array_5960_ = lean_ctor_get(v_snd_5951_, 0);
v_start_5961_ = lean_ctor_get(v_snd_5951_, 1);
v_stop_5962_ = lean_ctor_get(v_snd_5951_, 2);
v___x_5963_ = lean_nat_dec_lt(v_start_5961_, v_stop_5962_);
if (v___x_5963_ == 0)
{
lean_object* v___x_5965_; 
lean_dec(v_a_5947_);
if (v_isShared_5959_ == 0)
{
v___x_5965_ = v___x_5958_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_fst_5956_);
lean_ctor_set(v_reuseFailAlloc_5969_, 1, v_snd_5951_);
v___x_5965_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
lean_object* v___x_5967_; 
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5965_);
v___x_5967_ = v___x_5954_;
goto v_reusejp_5966_;
}
else
{
lean_object* v_reuseFailAlloc_5968_; 
v_reuseFailAlloc_5968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5968_, 0, v_fst_5952_);
lean_ctor_set(v_reuseFailAlloc_5968_, 1, v___x_5965_);
v___x_5967_ = v_reuseFailAlloc_5968_;
goto v_reusejp_5966_;
}
v_reusejp_5966_:
{
return v___x_5967_;
}
}
}
else
{
lean_object* v___x_5971_; uint8_t v_isShared_5972_; uint8_t v_isSharedCheck_6012_; 
lean_inc(v_stop_5962_);
lean_inc(v_start_5961_);
lean_inc_ref(v_array_5960_);
v_isSharedCheck_6012_ = !lean_is_exclusive(v_snd_5951_);
if (v_isSharedCheck_6012_ == 0)
{
lean_object* v_unused_6013_; lean_object* v_unused_6014_; lean_object* v_unused_6015_; 
v_unused_6013_ = lean_ctor_get(v_snd_5951_, 2);
lean_dec(v_unused_6013_);
v_unused_6014_ = lean_ctor_get(v_snd_5951_, 1);
lean_dec(v_unused_6014_);
v_unused_6015_ = lean_ctor_get(v_snd_5951_, 0);
lean_dec(v_unused_6015_);
v___x_5971_ = v_snd_5951_;
v_isShared_5972_ = v_isSharedCheck_6012_;
goto v_resetjp_5970_;
}
else
{
lean_dec(v_snd_5951_);
v___x_5971_ = lean_box(0);
v_isShared_5972_ = v_isSharedCheck_6012_;
goto v_resetjp_5970_;
}
v_resetjp_5970_:
{
lean_object* v_array_5973_; lean_object* v_start_5974_; lean_object* v_stop_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5980_; 
v_array_5973_ = lean_ctor_get(v_fst_5956_, 0);
v_start_5974_ = lean_ctor_get(v_fst_5956_, 1);
v_stop_5975_ = lean_ctor_get(v_fst_5956_, 2);
v___x_5976_ = lean_array_fget(v_array_5960_, v_start_5961_);
v___x_5977_ = lean_unsigned_to_nat(1u);
v___x_5978_ = lean_nat_add(v_start_5961_, v___x_5977_);
lean_dec(v_start_5961_);
if (v_isShared_5972_ == 0)
{
lean_ctor_set(v___x_5971_, 1, v___x_5978_);
v___x_5980_ = v___x_5971_;
goto v_reusejp_5979_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_array_5960_);
lean_ctor_set(v_reuseFailAlloc_6011_, 1, v___x_5978_);
lean_ctor_set(v_reuseFailAlloc_6011_, 2, v_stop_5962_);
v___x_5980_ = v_reuseFailAlloc_6011_;
goto v_reusejp_5979_;
}
v_reusejp_5979_:
{
uint8_t v___x_5981_; 
v___x_5981_ = lean_nat_dec_lt(v_start_5974_, v_stop_5975_);
if (v___x_5981_ == 0)
{
lean_object* v___x_5983_; 
lean_dec(v___x_5976_);
lean_dec(v_a_5947_);
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 1, v___x_5980_);
v___x_5983_ = v___x_5958_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_fst_5956_);
lean_ctor_set(v_reuseFailAlloc_5987_, 1, v___x_5980_);
v___x_5983_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
lean_object* v___x_5985_; 
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5983_);
v___x_5985_ = v___x_5954_;
goto v_reusejp_5984_;
}
else
{
lean_object* v_reuseFailAlloc_5986_; 
v_reuseFailAlloc_5986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5986_, 0, v_fst_5952_);
lean_ctor_set(v_reuseFailAlloc_5986_, 1, v___x_5983_);
v___x_5985_ = v_reuseFailAlloc_5986_;
goto v_reusejp_5984_;
}
v_reusejp_5984_:
{
return v___x_5985_;
}
}
}
else
{
lean_object* v___x_5989_; uint8_t v_isShared_5990_; uint8_t v_isSharedCheck_6007_; 
lean_inc(v_stop_5975_);
lean_inc(v_start_5974_);
lean_inc_ref(v_array_5973_);
v_isSharedCheck_6007_ = !lean_is_exclusive(v_fst_5956_);
if (v_isSharedCheck_6007_ == 0)
{
lean_object* v_unused_6008_; lean_object* v_unused_6009_; lean_object* v_unused_6010_; 
v_unused_6008_ = lean_ctor_get(v_fst_5956_, 2);
lean_dec(v_unused_6008_);
v_unused_6009_ = lean_ctor_get(v_fst_5956_, 1);
lean_dec(v_unused_6009_);
v_unused_6010_ = lean_ctor_get(v_fst_5956_, 0);
lean_dec(v_unused_6010_);
v___x_5989_ = v_fst_5956_;
v_isShared_5990_ = v_isSharedCheck_6007_;
goto v_resetjp_5988_;
}
else
{
lean_dec(v_fst_5956_);
v___x_5989_ = lean_box(0);
v_isShared_5990_ = v_isSharedCheck_6007_;
goto v_resetjp_5988_;
}
v_resetjp_5988_:
{
lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5994_; 
v___x_5991_ = lean_array_fget(v_array_5973_, v_start_5974_);
v___x_5992_ = lean_nat_add(v_start_5974_, v___x_5977_);
lean_dec(v_start_5974_);
if (v_isShared_5990_ == 0)
{
lean_ctor_set(v___x_5989_, 1, v___x_5992_);
v___x_5994_ = v___x_5989_;
goto v_reusejp_5993_;
}
else
{
lean_object* v_reuseFailAlloc_6006_; 
v_reuseFailAlloc_6006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6006_, 0, v_array_5973_);
lean_ctor_set(v_reuseFailAlloc_6006_, 1, v___x_5992_);
lean_ctor_set(v_reuseFailAlloc_6006_, 2, v_stop_5975_);
v___x_5994_ = v_reuseFailAlloc_6006_;
goto v_reusejp_5993_;
}
v_reusejp_5993_:
{
size_t v_sz_5995_; size_t v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5999_; 
v_sz_5995_ = lean_array_size(v___x_5991_);
v___x_5996_ = ((size_t)0ULL);
v___x_5997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4(v___x_5976_, v___x_5945_, v___x_5946_, v___x_5991_, v_sz_5995_, v___x_5996_, v_fst_5952_);
lean_dec(v___x_5991_);
lean_dec(v___x_5976_);
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 1, v___x_5980_);
lean_ctor_set(v___x_5958_, 0, v___x_5994_);
v___x_5999_ = v___x_5958_;
goto v_reusejp_5998_;
}
else
{
lean_object* v_reuseFailAlloc_6005_; 
v_reuseFailAlloc_6005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6005_, 0, v___x_5994_);
lean_ctor_set(v_reuseFailAlloc_6005_, 1, v___x_5980_);
v___x_5999_ = v_reuseFailAlloc_6005_;
goto v_reusejp_5998_;
}
v_reusejp_5998_:
{
lean_object* v___x_6001_; 
if (v_isShared_5955_ == 0)
{
lean_ctor_set(v___x_5954_, 1, v___x_5999_);
lean_ctor_set(v___x_5954_, 0, v___x_5997_);
v___x_6001_ = v___x_5954_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v___x_5997_);
lean_ctor_set(v_reuseFailAlloc_6004_, 1, v___x_5999_);
v___x_6001_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
lean_object* v___x_6002_; 
v___x_6002_ = lean_nat_add(v_a_5947_, v___x_5977_);
lean_dec(v_a_5947_);
v_a_5947_ = v___x_6002_;
v_b_5948_ = v___x_6001_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg___boxed(lean_object* v_upperBound_6020_, lean_object* v___x_6021_, lean_object* v___x_6022_, lean_object* v_a_6023_, lean_object* v_b_6024_){
_start:
{
lean_object* v_res_6025_; 
v_res_6025_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6020_, v___x_6021_, v___x_6022_, v_a_6023_, v_b_6024_);
lean_dec(v___x_6022_);
lean_dec(v___x_6021_);
lean_dec(v_upperBound_6020_);
return v_res_6025_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__1(void){
_start:
{
lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; 
v___x_6027_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__0));
v___x_6028_ = lean_unsigned_to_nat(2u);
v___x_6029_ = lean_unsigned_to_nat(457u);
v___x_6030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6031_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6032_ = l_mkPanicMessageWithDecl(v___x_6031_, v___x_6030_, v___x_6029_, v___x_6028_, v___x_6027_);
return v___x_6032_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__3(void){
_start:
{
lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___x_6034_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__2));
v___x_6035_ = lean_unsigned_to_nat(2u);
v___x_6036_ = lean_unsigned_to_nat(458u);
v___x_6037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6038_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6039_ = l_mkPanicMessageWithDecl(v___x_6038_, v___x_6037_, v___x_6036_, v___x_6035_, v___x_6034_);
return v___x_6039_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerms_erase___closed__5(void){
_start:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v___x_6041_ = ((lean_object*)(l_Lean_Elab_FixedParamPerms_erase___closed__4));
v___x_6042_ = lean_unsigned_to_nat(2u);
v___x_6043_ = lean_unsigned_to_nat(456u);
v___x_6044_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__4___closed__0));
v___x_6045_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_6046_ = l_mkPanicMessageWithDecl(v___x_6045_, v___x_6044_, v___x_6043_, v___x_6042_, v___x_6041_);
return v___x_6046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object* v_fixedParamPerms_6047_, lean_object* v_xs_6048_, lean_object* v_toErase_6049_){
_start:
{
lean_object* v___x_6050_; lean_object* v___x_6051_; uint8_t v___x_6135_; 
v___x_6050_ = lean_unsigned_to_nat(0u);
v___x_6051_ = lean_array_get_size(v_xs_6048_);
v___x_6135_ = lean_nat_dec_lt(v___x_6050_, v___x_6051_);
if (v___x_6135_ == 0)
{
goto v___jp_6052_;
}
else
{
if (v___x_6135_ == 0)
{
goto v___jp_6052_;
}
else
{
size_t v___x_6136_; size_t v___x_6137_; uint8_t v___x_6138_; 
v___x_6136_ = ((size_t)0ULL);
v___x_6137_ = lean_usize_of_nat(v___x_6051_);
v___x_6138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_FixedParamPerms_erase_spec__11(v_xs_6048_, v___x_6136_, v___x_6137_);
if (v___x_6138_ == 0)
{
goto v___jp_6052_;
}
else
{
lean_object* v___x_6139_; lean_object* v___x_6140_; 
lean_dec_ref(v_toErase_6049_);
lean_dec_ref(v_xs_6048_);
lean_dec_ref(v_fixedParamPerms_6047_);
v___x_6139_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__5, &l_Lean_Elab_FixedParamPerms_erase___closed__5_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__5);
v___x_6140_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6139_);
return v___x_6140_;
}
}
}
v___jp_6052_:
{
lean_object* v_numFixed_6053_; lean_object* v_perms_6054_; lean_object* v_revDeps_6055_; uint8_t v___x_6056_; 
v_numFixed_6053_ = lean_ctor_get(v_fixedParamPerms_6047_, 0);
v_perms_6054_ = lean_ctor_get(v_fixedParamPerms_6047_, 1);
lean_inc_ref(v_perms_6054_);
v_revDeps_6055_ = lean_ctor_get(v_fixedParamPerms_6047_, 2);
lean_inc_ref(v_revDeps_6055_);
v___x_6056_ = lean_nat_dec_eq(v_numFixed_6053_, v___x_6051_);
if (v___x_6056_ == 0)
{
lean_object* v___x_6057_; lean_object* v___x_6058_; 
lean_dec_ref(v_revDeps_6055_);
lean_dec_ref(v_perms_6054_);
lean_dec_ref(v_toErase_6049_);
lean_dec_ref(v_xs_6048_);
lean_dec_ref(v_fixedParamPerms_6047_);
v___x_6057_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__1, &l_Lean_Elab_FixedParamPerms_erase___closed__1_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__1);
v___x_6058_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6057_);
return v___x_6058_;
}
else
{
lean_object* v___x_6059_; lean_object* v___x_6060_; uint8_t v_changed_6061_; 
v___x_6059_ = lean_array_get_size(v_toErase_6049_);
v___x_6060_ = lean_array_get_size(v_perms_6054_);
v_changed_6061_ = lean_nat_dec_eq(v___x_6059_, v___x_6060_);
if (v_changed_6061_ == 0)
{
lean_object* v___x_6062_; lean_object* v___x_6063_; 
lean_dec_ref(v_revDeps_6055_);
lean_dec_ref(v_perms_6054_);
lean_dec_ref(v_toErase_6049_);
lean_dec_ref(v_xs_6048_);
lean_dec_ref(v_fixedParamPerms_6047_);
v___x_6062_ = lean_obj_once(&l_Lean_Elab_FixedParamPerms_erase___closed__3, &l_Lean_Elab_FixedParamPerms_erase___closed__3_once, _init_l_Lean_Elab_FixedParamPerms_erase___closed__3);
v___x_6063_ = l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(v___x_6062_);
return v___x_6063_;
}
else
{
uint8_t v_changed_6064_; lean_object* v___x_6065_; lean_object* v_mask_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v_fst_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6133_; 
v_changed_6064_ = 0;
v___x_6065_ = lean_box(v_changed_6064_);
lean_inc(v_numFixed_6053_);
v_mask_6066_ = lean_mk_array(v_numFixed_6053_, v___x_6065_);
v___x_6067_ = l_Array_toSubarray___redArg(v_toErase_6049_, v___x_6050_, v___x_6059_);
lean_inc_ref(v_perms_6054_);
v___x_6068_ = l_Array_toSubarray___redArg(v_perms_6054_, v___x_6050_, v___x_6060_);
v___x_6069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6067_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6070_, 0, v_mask_6066_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v___x_6059_, v___x_6059_, v___x_6060_, v___x_6050_, v___x_6070_);
v_fst_6072_ = lean_ctor_get(v___x_6071_, 0);
v_isSharedCheck_6133_ = !lean_is_exclusive(v___x_6071_);
if (v_isSharedCheck_6133_ == 0)
{
lean_object* v_unused_6134_; 
v_unused_6134_ = lean_ctor_get(v___x_6071_, 1);
lean_dec(v_unused_6134_);
v___x_6074_ = v___x_6071_;
v_isShared_6075_ = v_isSharedCheck_6133_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_fst_6072_);
lean_dec(v___x_6071_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6133_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v___x_6076_; lean_object* v___x_6078_; 
v___x_6076_ = lean_box(v_changed_6061_);
if (v_isShared_6075_ == 0)
{
lean_ctor_set(v___x_6074_, 1, v___x_6076_);
v___x_6078_ = v___x_6074_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_fst_6072_);
lean_ctor_set(v_reuseFailAlloc_6132_, 1, v___x_6076_);
v___x_6078_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
lean_object* v___x_6079_; lean_object* v___x_6081_; uint8_t v_isShared_6082_; uint8_t v_isSharedCheck_6128_; 
v___x_6079_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6060_, v_perms_6054_, v___x_6059_, v_fixedParamPerms_6047_, v___x_6078_);
v_isSharedCheck_6128_ = !lean_is_exclusive(v_fixedParamPerms_6047_);
if (v_isSharedCheck_6128_ == 0)
{
lean_object* v_unused_6129_; lean_object* v_unused_6130_; lean_object* v_unused_6131_; 
v_unused_6129_ = lean_ctor_get(v_fixedParamPerms_6047_, 2);
lean_dec(v_unused_6129_);
v_unused_6130_ = lean_ctor_get(v_fixedParamPerms_6047_, 1);
lean_dec(v_unused_6130_);
v_unused_6131_ = lean_ctor_get(v_fixedParamPerms_6047_, 0);
lean_dec(v_unused_6131_);
v___x_6081_ = v_fixedParamPerms_6047_;
v_isShared_6082_ = v_isSharedCheck_6128_;
goto v_resetjp_6080_;
}
else
{
lean_dec(v_fixedParamPerms_6047_);
v___x_6081_ = lean_box(0);
v_isShared_6082_ = v_isSharedCheck_6128_;
goto v_resetjp_6080_;
}
v_resetjp_6080_:
{
lean_object* v_fst_6083_; lean_object* v___x_6085_; uint8_t v_isShared_6086_; uint8_t v_isSharedCheck_6126_; 
v_fst_6083_ = lean_ctor_get(v___x_6079_, 0);
v_isSharedCheck_6126_ = !lean_is_exclusive(v___x_6079_);
if (v_isSharedCheck_6126_ == 0)
{
lean_object* v_unused_6127_; 
v_unused_6127_ = lean_ctor_get(v___x_6079_, 1);
lean_dec(v_unused_6127_);
v___x_6085_ = v___x_6079_;
v_isShared_6086_ = v_isSharedCheck_6126_;
goto v_resetjp_6084_;
}
else
{
lean_inc(v_fst_6083_);
lean_dec(v___x_6079_);
v___x_6085_ = lean_box(0);
v_isShared_6086_ = v_isSharedCheck_6126_;
goto v_resetjp_6084_;
}
v_resetjp_6084_:
{
lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6092_; 
v___x_6087_ = lean_array_get_size(v_fst_6083_);
v___x_6088_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_6089_ = l_Array_toSubarray___redArg(v_fst_6083_, v___x_6050_, v___x_6087_);
v___x_6090_ = l_Array_toSubarray___redArg(v_xs_6048_, v___x_6050_, v___x_6051_);
if (v_isShared_6086_ == 0)
{
lean_ctor_set(v___x_6085_, 1, v___x_6090_);
lean_ctor_set(v___x_6085_, 0, v___x_6089_);
v___x_6092_ = v___x_6085_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v___x_6089_);
lean_ctor_set(v_reuseFailAlloc_6125_, 1, v___x_6090_);
v___x_6092_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v_snd_6097_; lean_object* v_snd_6098_; lean_object* v_fst_6099_; lean_object* v_fst_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6123_; 
v___x_6093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6088_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6088_);
lean_ctor_set(v___x_6094_, 1, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6088_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v___x_6096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v___x_6087_, v___x_6050_, v___x_6095_);
v_snd_6097_ = lean_ctor_get(v___x_6096_, 1);
lean_inc(v_snd_6097_);
v_snd_6098_ = lean_ctor_get(v_snd_6097_, 1);
lean_inc(v_snd_6098_);
v_fst_6099_ = lean_ctor_get(v___x_6096_, 0);
lean_inc(v_fst_6099_);
lean_dec_ref(v___x_6096_);
v_fst_6100_ = lean_ctor_get(v_snd_6097_, 0);
v_isSharedCheck_6123_ = !lean_is_exclusive(v_snd_6097_);
if (v_isSharedCheck_6123_ == 0)
{
lean_object* v_unused_6124_; 
v_unused_6124_ = lean_ctor_get(v_snd_6097_, 1);
lean_dec(v_unused_6124_);
v___x_6102_ = v_snd_6097_;
v_isShared_6103_ = v_isSharedCheck_6123_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_fst_6100_);
lean_dec(v_snd_6097_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6123_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
lean_object* v_fst_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6121_; 
v_fst_6104_ = lean_ctor_get(v_snd_6098_, 0);
v_isSharedCheck_6121_ = !lean_is_exclusive(v_snd_6098_);
if (v_isSharedCheck_6121_ == 0)
{
lean_object* v_unused_6122_; 
v_unused_6122_ = lean_ctor_get(v_snd_6098_, 1);
lean_dec(v_unused_6122_);
v___x_6106_ = v_snd_6098_;
v_isShared_6107_ = v_isSharedCheck_6121_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_fst_6104_);
lean_dec(v_snd_6098_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6121_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6108_; size_t v_sz_6109_; size_t v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6113_; 
v___x_6108_ = lean_array_get_size(v_fst_6104_);
v_sz_6109_ = lean_array_size(v_perms_6054_);
v___x_6110_ = ((size_t)0ULL);
v___x_6111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_FixedParamPerms_erase_spec__2(v_fst_6099_, v_sz_6109_, v___x_6110_, v_perms_6054_);
lean_dec(v_fst_6099_);
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 1, v___x_6111_);
lean_ctor_set(v___x_6081_, 0, v___x_6108_);
v___x_6113_ = v___x_6081_;
goto v_reusejp_6112_;
}
else
{
lean_object* v_reuseFailAlloc_6120_; 
v_reuseFailAlloc_6120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6120_, 0, v___x_6108_);
lean_ctor_set(v_reuseFailAlloc_6120_, 1, v___x_6111_);
lean_ctor_set(v_reuseFailAlloc_6120_, 2, v_revDeps_6055_);
v___x_6113_ = v_reuseFailAlloc_6120_;
goto v_reusejp_6112_;
}
v_reusejp_6112_:
{
lean_object* v___x_6115_; 
if (v_isShared_6107_ == 0)
{
lean_ctor_set(v___x_6106_, 1, v_fst_6100_);
v___x_6115_ = v___x_6106_;
goto v_reusejp_6114_;
}
else
{
lean_object* v_reuseFailAlloc_6119_; 
v_reuseFailAlloc_6119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_fst_6104_);
lean_ctor_set(v_reuseFailAlloc_6119_, 1, v_fst_6100_);
v___x_6115_ = v_reuseFailAlloc_6119_;
goto v_reusejp_6114_;
}
v_reusejp_6114_:
{
lean_object* v___x_6117_; 
if (v_isShared_6103_ == 0)
{
lean_ctor_set(v___x_6102_, 1, v___x_6115_);
lean_ctor_set(v___x_6102_, 0, v___x_6113_);
v___x_6117_ = v___x_6102_;
goto v_reusejp_6116_;
}
else
{
lean_object* v_reuseFailAlloc_6118_; 
v_reuseFailAlloc_6118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6118_, 0, v___x_6113_);
lean_ctor_set(v_reuseFailAlloc_6118_, 1, v___x_6115_);
v___x_6117_ = v_reuseFailAlloc_6118_;
goto v_reusejp_6116_;
}
v_reusejp_6116_:
{
return v___x_6117_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(lean_object* v_upperBound_6141_, lean_object* v___x_6142_, lean_object* v___x_6143_, lean_object* v___x_6144_, lean_object* v_fixedParamPerms_6145_, lean_object* v_next_6146_, lean_object* v_inst_6147_, lean_object* v_R_6148_, lean_object* v_a_6149_, lean_object* v_b_6150_, lean_object* v_c_6151_){
_start:
{
lean_object* v___x_6152_; 
v___x_6152_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___redArg(v_upperBound_6141_, v___x_6142_, v___x_6143_, v___x_6144_, v_fixedParamPerms_6145_, v_next_6146_, v_a_6149_, v_b_6150_);
return v___x_6152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6___boxed(lean_object* v_upperBound_6153_, lean_object* v___x_6154_, lean_object* v___x_6155_, lean_object* v___x_6156_, lean_object* v_fixedParamPerms_6157_, lean_object* v_next_6158_, lean_object* v_inst_6159_, lean_object* v_R_6160_, lean_object* v_a_6161_, lean_object* v_b_6162_, lean_object* v_c_6163_){
_start:
{
lean_object* v_res_6164_; 
v_res_6164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6(v_upperBound_6153_, v___x_6154_, v___x_6155_, v___x_6156_, v_fixedParamPerms_6157_, v_next_6158_, v_inst_6159_, v_R_6160_, v_a_6161_, v_b_6162_, v_c_6163_);
lean_dec(v_a_6161_);
lean_dec(v_next_6158_);
lean_dec_ref(v_fixedParamPerms_6157_);
lean_dec(v___x_6156_);
lean_dec(v___x_6155_);
lean_dec_ref(v___x_6154_);
lean_dec(v_upperBound_6153_);
return v_res_6164_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(lean_object* v_upperBound_6165_, lean_object* v___x_6166_, lean_object* v___x_6167_, lean_object* v___x_6168_, lean_object* v_fixedParamPerms_6169_, lean_object* v_inst_6170_, lean_object* v_R_6171_, lean_object* v_a_6172_, lean_object* v_b_6173_, lean_object* v_c_6174_){
_start:
{
lean_object* v___x_6175_; 
v___x_6175_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___redArg(v_upperBound_6165_, v___x_6166_, v___x_6167_, v___x_6168_, v_fixedParamPerms_6169_, v_a_6172_, v_b_6173_);
return v___x_6175_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7___boxed(lean_object* v_upperBound_6176_, lean_object* v___x_6177_, lean_object* v___x_6178_, lean_object* v___x_6179_, lean_object* v_fixedParamPerms_6180_, lean_object* v_inst_6181_, lean_object* v_R_6182_, lean_object* v_a_6183_, lean_object* v_b_6184_, lean_object* v_c_6185_){
_start:
{
lean_object* v_res_6186_; 
v_res_6186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__7(v_upperBound_6176_, v___x_6177_, v___x_6178_, v___x_6179_, v_fixedParamPerms_6180_, v_inst_6181_, v_R_6182_, v_a_6183_, v_b_6184_, v_c_6185_);
lean_dec_ref(v_fixedParamPerms_6180_);
lean_dec(v___x_6179_);
lean_dec(v___x_6178_);
lean_dec_ref(v___x_6177_);
lean_dec(v_upperBound_6176_);
return v_res_6186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(lean_object* v___x_6187_, lean_object* v___x_6188_, lean_object* v___x_6189_, lean_object* v_fixedParamPerms_6190_, lean_object* v_inst_6191_, lean_object* v_a_6192_){
_start:
{
lean_object* v___x_6193_; 
v___x_6193_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___redArg(v___x_6187_, v___x_6188_, v___x_6189_, v_fixedParamPerms_6190_, v_a_6192_);
return v___x_6193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8___boxed(lean_object* v___x_6194_, lean_object* v___x_6195_, lean_object* v___x_6196_, lean_object* v_fixedParamPerms_6197_, lean_object* v_inst_6198_, lean_object* v_a_6199_){
_start:
{
lean_object* v_res_6200_; 
v_res_6200_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_FixedParamPerms_erase_spec__8(v___x_6194_, v___x_6195_, v___x_6196_, v_fixedParamPerms_6197_, v_inst_6198_, v_a_6199_);
lean_dec_ref(v_fixedParamPerms_6197_);
lean_dec(v___x_6196_);
lean_dec_ref(v___x_6195_);
lean_dec(v___x_6194_);
return v_res_6200_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(lean_object* v_upperBound_6201_, lean_object* v_inst_6202_, lean_object* v_R_6203_, lean_object* v_a_6204_, lean_object* v_b_6205_, lean_object* v_c_6206_){
_start:
{
lean_object* v___x_6207_; 
v___x_6207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___redArg(v_upperBound_6201_, v_a_6204_, v_b_6205_);
return v___x_6207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9___boxed(lean_object* v_upperBound_6208_, lean_object* v_inst_6209_, lean_object* v_R_6210_, lean_object* v_a_6211_, lean_object* v_b_6212_, lean_object* v_c_6213_){
_start:
{
lean_object* v_res_6214_; 
v_res_6214_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__9(v_upperBound_6208_, v_inst_6209_, v_R_6210_, v_a_6211_, v_b_6212_, v_c_6213_);
lean_dec(v_upperBound_6208_);
return v_res_6214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(lean_object* v_upperBound_6215_, lean_object* v___x_6216_, lean_object* v___x_6217_, lean_object* v_inst_6218_, lean_object* v_R_6219_, lean_object* v_a_6220_, lean_object* v_b_6221_, lean_object* v_c_6222_){
_start:
{
lean_object* v___x_6223_; 
v___x_6223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___redArg(v_upperBound_6215_, v___x_6216_, v___x_6217_, v_a_6220_, v_b_6221_);
return v___x_6223_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10___boxed(lean_object* v_upperBound_6224_, lean_object* v___x_6225_, lean_object* v___x_6226_, lean_object* v_inst_6227_, lean_object* v_R_6228_, lean_object* v_a_6229_, lean_object* v_b_6230_, lean_object* v_c_6231_){
_start:
{
lean_object* v_res_6232_; 
v_res_6232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__10(v_upperBound_6224_, v___x_6225_, v___x_6226_, v_inst_6227_, v_R_6228_, v_a_6229_, v_b_6230_, v_c_6231_);
lean_dec(v___x_6226_);
lean_dec(v___x_6225_);
lean_dec(v_upperBound_6224_);
return v_res_6232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(lean_object* v_upperBound_6233_, lean_object* v___x_6234_, lean_object* v_fixedParamPerms_6235_, lean_object* v_next_6236_, lean_object* v___x_6237_, lean_object* v___x_6238_, lean_object* v_inst_6239_, lean_object* v_R_6240_, lean_object* v_a_6241_, lean_object* v_b_6242_, lean_object* v_c_6243_){
_start:
{
lean_object* v___x_6244_; 
v___x_6244_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___redArg(v_upperBound_6233_, v___x_6234_, v_fixedParamPerms_6235_, v_next_6236_, v___x_6237_, v___x_6238_, v_a_6241_, v_b_6242_);
return v___x_6244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6___boxed(lean_object* v_upperBound_6245_, lean_object* v___x_6246_, lean_object* v_fixedParamPerms_6247_, lean_object* v_next_6248_, lean_object* v___x_6249_, lean_object* v___x_6250_, lean_object* v_inst_6251_, lean_object* v_R_6252_, lean_object* v_a_6253_, lean_object* v_b_6254_, lean_object* v_c_6255_){
_start:
{
lean_object* v_res_6256_; 
v_res_6256_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Elab_FixedParamPerms_erase_spec__6_spec__6(v_upperBound_6245_, v___x_6246_, v_fixedParamPerms_6247_, v_next_6248_, v___x_6249_, v___x_6250_, v_inst_6251_, v_R_6252_, v_a_6253_, v_b_6254_, v_c_6255_);
lean_dec(v___x_6250_);
lean_dec(v___x_6249_);
lean_dec(v_next_6248_);
lean_dec_ref(v_fixedParamPerms_6247_);
lean_dec_ref(v___x_6246_);
lean_dec(v_upperBound_6245_);
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6314_; uint8_t v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; 
v___x_6314_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_6315_ = 0;
v___x_6316_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_));
v___x_6317_ = l_Lean_registerTraceClass(v___x_6314_, v___x_6315_, v___x_6316_);
return v___x_6317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2____boxed(lean_object* v_a_6318_){
_start:
{
lean_object* v_res_6319_; 
v_res_6319_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__initFn_00___x40_Lean_Elab_PreDefinition_FixedParams_791000795____hygCtx___hyg_2_();
return v_res_6319_;
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
