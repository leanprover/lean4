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
lean_object* v___f_1008_; lean_object* v___x_27245__overap_1009_; lean_object* v___x_1010_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_27245__overap_1009_ = lean_panic_fn_borrowed(v___f_1008_, v_msg_1002_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1010_ = lean_apply_5(v___x_27245__overap_1009_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, lean_box(0));
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
lean_object* v_ref_1110_; lean_object* v___x_1111_; lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1157_; 
v_ref_1110_ = lean_ctor_get(v___y_1107_, 2);
v___x_1111_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2_spec__2(v_msg_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1157_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1157_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v_traceState_1117_; lean_object* v_env_1118_; lean_object* v_nextMacroScope_1119_; lean_object* v_ngen_1120_; lean_object* v_auxDeclNGen_1121_; lean_object* v_cache_1122_; lean_object* v_recordedDeps_1123_; lean_object* v_messages_1124_; lean_object* v_infoState_1125_; lean_object* v_snapshotTasks_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1156_; 
v___x_1116_ = lean_st_ref_take(v___y_1108_);
v_traceState_1117_ = lean_ctor_get(v___x_1116_, 4);
v_env_1118_ = lean_ctor_get(v___x_1116_, 0);
v_nextMacroScope_1119_ = lean_ctor_get(v___x_1116_, 1);
v_ngen_1120_ = lean_ctor_get(v___x_1116_, 2);
v_auxDeclNGen_1121_ = lean_ctor_get(v___x_1116_, 3);
v_cache_1122_ = lean_ctor_get(v___x_1116_, 5);
v_recordedDeps_1123_ = lean_ctor_get(v___x_1116_, 6);
v_messages_1124_ = lean_ctor_get(v___x_1116_, 7);
v_infoState_1125_ = lean_ctor_get(v___x_1116_, 8);
v_snapshotTasks_1126_ = lean_ctor_get(v___x_1116_, 9);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1128_ = v___x_1116_;
v_isShared_1129_ = v_isSharedCheck_1156_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snapshotTasks_1126_);
lean_inc(v_infoState_1125_);
lean_inc(v_messages_1124_);
lean_inc(v_recordedDeps_1123_);
lean_inc(v_cache_1122_);
lean_inc(v_traceState_1117_);
lean_inc(v_auxDeclNGen_1121_);
lean_inc(v_ngen_1120_);
lean_inc(v_nextMacroScope_1119_);
lean_inc(v_env_1118_);
lean_dec(v___x_1116_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1156_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint64_t v_tid_1130_; lean_object* v_traces_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_tid_1130_ = lean_ctor_get_uint64(v_traceState_1117_, sizeof(void*)*1);
v_traces_1131_ = lean_ctor_get(v_traceState_1117_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_traceState_1117_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1133_ = v_traceState_1117_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_traces_1131_);
lean_dec(v_traceState_1117_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; double v___x_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__0);
v___x_1138_ = 0;
v___x_1139_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__1));
v___x_1140_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1140_, 0, v_cls_1103_);
lean_ctor_set(v___x_1140_, 1, v___x_1136_);
lean_ctor_set(v___x_1140_, 2, v___x_1139_);
lean_ctor_set_float(v___x_1140_, sizeof(void*)*3, v___x_1137_);
lean_ctor_set_float(v___x_1140_, sizeof(void*)*3 + 8, v___x_1137_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*3 + 16, v___x_1138_);
v___x_1141_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2___closed__2));
v___x_1142_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v_a_1112_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
lean_inc(v_ref_1110_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_ref_1110_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_PersistentArray_push___redArg(v_traces_1131_, v___x_1143_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1144_);
v___x_1146_ = v___x_1133_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1144_);
lean_ctor_set_uint64(v_reuseFailAlloc_1154_, sizeof(void*)*1, v_tid_1130_);
v___x_1146_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v___x_1146_);
v___x_1148_ = v___x_1128_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_env_1118_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_nextMacroScope_1119_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_ngen_1120_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_auxDeclNGen_1121_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1153_, 5, v_cache_1122_);
lean_ctor_set(v_reuseFailAlloc_1153_, 6, v_recordedDeps_1123_);
lean_ctor_set(v_reuseFailAlloc_1153_, 7, v_messages_1124_);
lean_ctor_set(v_reuseFailAlloc_1153_, 8, v_infoState_1125_);
lean_ctor_set(v_reuseFailAlloc_1153_, 9, v_snapshotTasks_1126_);
v___x_1148_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_st_ref_put(v___y_1108_, v___x_1148_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1135_);
v___x_1151_ = v___x_1114_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1135_);
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
v___x_1314_ = lean_box(0);
v___x_1315_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v___x_1313_, v_e_1310_, v_a_1311_);
v___x_1316_ = lean_st_ref_put(v_a_1309_, v___x_1315_);
return v___x_1314_;
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
lean_object* v___y_1471_; lean_object* v_toCold_1480_; lean_object* v_currRecDepth_1481_; lean_object* v_ref_1482_; uint16_t v_optionFlags_1483_; uint8_t v_suppressElabErrors_1484_; uint8_t v_isRecordingDeps_1485_; lean_object* v_maxRecDepth_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v_toCold_1480_ = lean_ctor_get(v___y_1467_, 0);
v_currRecDepth_1481_ = lean_ctor_get(v___y_1467_, 1);
v_ref_1482_ = lean_ctor_get(v___y_1467_, 2);
v_optionFlags_1483_ = lean_ctor_get_uint16(v___y_1467_, sizeof(void*)*3);
v_suppressElabErrors_1484_ = lean_ctor_get_uint8(v___y_1467_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1485_ = lean_ctor_get_uint8(v___y_1467_, sizeof(void*)*3 + 3);
v_maxRecDepth_1491_ = lean_ctor_get(v_toCold_1480_, 3);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_nat_dec_eq(v_maxRecDepth_1491_, v___x_1492_);
if (v___x_1493_ == 0)
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_nat_dec_eq(v_currRecDepth_1481_, v_maxRecDepth_1491_);
if (v___x_1494_ == 0)
{
goto v___jp_1486_;
}
else
{
lean_object* v___x_1495_; 
lean_dec_ref(v_x_1463_);
lean_inc(v_ref_1482_);
v___x_1495_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_1482_);
v___y_1471_ = v___x_1495_;
goto v___jp_1470_;
}
}
else
{
goto v___jp_1486_;
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
v___jp_1486_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_add(v_currRecDepth_1481_, v___x_1487_);
lean_inc(v_ref_1482_);
lean_inc_ref(v_toCold_1480_);
v___x_1489_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1489_, 0, v_toCold_1480_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_ctor_set(v___x_1489_, 2, v_ref_1482_);
lean_ctor_set_uint16(v___x_1489_, sizeof(void*)*3, v_optionFlags_1483_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*3 + 2, v_suppressElabErrors_1484_);
lean_ctor_set_uint8(v___x_1489_, sizeof(void*)*3 + 3, v_isRecordingDeps_1485_);
lean_inc(v___y_1468_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
v___x_1490_ = lean_apply_6(v_x_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___x_1489_, v___y_1468_, lean_box(0));
v___y_1471_ = v___x_1490_;
goto v___jp_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg___boxed(lean_object* v_x_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(lean_object* v_a_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_box(0);
return v___x_1506_;
}
else
{
lean_object* v_key_1507_; lean_object* v_value_1508_; lean_object* v_tail_1509_; uint8_t v___x_1510_; 
v_key_1507_ = lean_ctor_get(v_x_1505_, 0);
v_value_1508_ = lean_ctor_get(v_x_1505_, 1);
v_tail_1509_ = lean_ctor_get(v_x_1505_, 2);
v___x_1510_ = l_Lean_ExprStructEq_beq(v_key_1507_, v_a_1504_);
if (v___x_1510_ == 0)
{
v_x_1505_ = v_tail_1509_;
goto _start;
}
else
{
lean_object* v___x_1512_; 
lean_inc(v_value_1508_);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_value_1508_);
return v___x_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg___boxed(lean_object* v_a_1513_, lean_object* v_x_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1513_, v_x_1514_);
lean_dec(v_x_1514_);
lean_dec_ref(v_a_1513_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(lean_object* v_m_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_buckets_1518_; lean_object* v___x_1519_; uint64_t v___x_1520_; uint64_t v___x_1521_; uint64_t v___x_1522_; uint64_t v_fold_1523_; uint64_t v___x_1524_; uint64_t v___x_1525_; uint64_t v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; size_t v___x_1530_; size_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_buckets_1518_ = lean_ctor_get(v_m_1516_, 1);
v___x_1519_ = lean_array_get_size(v_buckets_1518_);
v___x_1520_ = l_Lean_ExprStructEq_hash(v_a_1517_);
v___x_1521_ = 32ULL;
v___x_1522_ = lean_uint64_shift_right(v___x_1520_, v___x_1521_);
v_fold_1523_ = lean_uint64_xor(v___x_1520_, v___x_1522_);
v___x_1524_ = 16ULL;
v___x_1525_ = lean_uint64_shift_right(v_fold_1523_, v___x_1524_);
v___x_1526_ = lean_uint64_xor(v_fold_1523_, v___x_1525_);
v___x_1527_ = lean_uint64_to_usize(v___x_1526_);
v___x_1528_ = lean_usize_of_nat(v___x_1519_);
v___x_1529_ = ((size_t)1ULL);
v___x_1530_ = lean_usize_sub(v___x_1528_, v___x_1529_);
v___x_1531_ = lean_usize_land(v___x_1527_, v___x_1530_);
v___x_1532_ = lean_array_uget_borrowed(v_buckets_1518_, v___x_1531_);
v___x_1533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_1517_, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg___boxed(lean_object* v_m_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_1534_, v_a_1535_);
lean_dec_ref(v_a_1535_);
lean_dec_ref(v_m_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_1537_, lean_object* v_pre_1538_, lean_object* v_post_1539_, lean_object* v_usedLetOnly_1540_, lean_object* v_skipConstInApp_1541_, lean_object* v_skipInstances_1542_, lean_object* v_body_1543_, lean_object* v_x_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
uint8_t v_usedLetOnly_boxed_1551_; uint8_t v_skipConstInApp_boxed_1552_; uint8_t v_skipInstances_boxed_1553_; lean_object* v_res_1554_; 
v_usedLetOnly_boxed_1551_ = lean_unbox(v_usedLetOnly_1540_);
v_skipConstInApp_boxed_1552_ = lean_unbox(v_skipConstInApp_1541_);
v_skipInstances_boxed_1553_ = lean_unbox(v_skipInstances_1542_);
v_res_1554_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(v_fvars_1537_, v_pre_1538_, v_post_1539_, v_usedLetOnly_boxed_1551_, v_skipConstInApp_boxed_1552_, v_skipInstances_boxed_1553_, v_body_1543_, v_x_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(lean_object* v_fvars_1558_, lean_object* v_pre_1559_, lean_object* v_post_1560_, uint8_t v_usedLetOnly_1561_, uint8_t v_skipConstInApp_1562_, uint8_t v_skipInstances_1563_, lean_object* v_body_1564_, lean_object* v_x_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_array_push(v_fvars_1558_, v_x_1565_);
v___x_1573_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1559_, v_post_1560_, v_usedLetOnly_1561_, v_skipConstInApp_1562_, v_skipInstances_1563_, v___x_1572_, v_body_1564_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed(lean_object* v_fvars_1574_, lean_object* v_pre_1575_, lean_object* v_post_1576_, lean_object* v_usedLetOnly_1577_, lean_object* v_skipConstInApp_1578_, lean_object* v_skipInstances_1579_, lean_object* v_body_1580_, lean_object* v_x_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v_usedLetOnly_boxed_1588_; uint8_t v_skipConstInApp_boxed_1589_; uint8_t v_skipInstances_boxed_1590_; lean_object* v_res_1591_; 
v_usedLetOnly_boxed_1588_ = lean_unbox(v_usedLetOnly_1577_);
v_skipConstInApp_boxed_1589_ = lean_unbox(v_skipConstInApp_1578_);
v_skipInstances_boxed_1590_ = lean_unbox(v_skipInstances_1579_);
v_res_1591_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0(v_fvars_1574_, v_pre_1575_, v_post_1576_, v_usedLetOnly_boxed_1588_, v_skipConstInApp_boxed_1589_, v_skipInstances_boxed_1590_, v_body_1580_, v_x_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(lean_object* v_pre_1592_, lean_object* v_post_1593_, uint8_t v_usedLetOnly_1594_, uint8_t v_skipConstInApp_1595_, uint8_t v_skipInstances_1596_, lean_object* v_e_1597_, lean_object* v_a_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
lean_inc_ref(v_post_1593_);
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
lean_inc_ref(v_e_1597_);
v___x_1604_ = lean_apply_6(v_post_1593_, v_e_1597_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, lean_box(0));
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1623_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1623_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1623_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
switch(lean_obj_tag(v_a_1605_))
{
case 0:
{
lean_object* v_e_1609_; lean_object* v___x_1611_; 
lean_dec_ref(v_e_1597_);
lean_dec_ref(v_post_1593_);
lean_dec_ref(v_pre_1592_);
v_e_1609_ = lean_ctor_get(v_a_1605_, 0);
lean_inc_ref(v_e_1609_);
lean_dec_ref_known(v_a_1605_, 1);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v_e_1609_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_e_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
case 1:
{
lean_object* v_e_1613_; lean_object* v___x_1614_; 
lean_del_object(v___x_1607_);
lean_dec_ref(v_e_1597_);
v_e_1613_ = lean_ctor_get(v_a_1605_, 0);
lean_inc_ref(v_e_1613_);
lean_dec_ref_known(v_a_1605_, 1);
v___x_1614_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1592_, v_post_1593_, v_usedLetOnly_1594_, v_skipConstInApp_1595_, v_skipInstances_1596_, v_e_1613_, v_a_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
return v___x_1614_;
}
default: 
{
lean_object* v_e_x3f_1615_; 
lean_dec_ref(v_post_1593_);
lean_dec_ref(v_pre_1592_);
v_e_x3f_1615_ = lean_ctor_get(v_a_1605_, 0);
lean_inc(v_e_x3f_1615_);
lean_dec_ref_known(v_a_1605_, 1);
if (lean_obj_tag(v_e_x3f_1615_) == 0)
{
lean_object* v___x_1617_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v_e_1597_);
v___x_1617_ = v___x_1607_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_e_1597_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
else
{
lean_object* v_val_1619_; lean_object* v___x_1621_; 
lean_dec_ref(v_e_1597_);
v_val_1619_ = lean_ctor_get(v_e_x3f_1615_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v_e_x3f_1615_, 1);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v_val_1619_);
v___x_1621_ = v___x_1607_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_val_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_e_1597_);
lean_dec_ref(v_post_1593_);
lean_dec_ref(v_pre_1592_);
v_a_1624_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1604_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1604_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(lean_object* v_pre_1632_, lean_object* v_post_1633_, uint8_t v_usedLetOnly_1634_, uint8_t v_skipConstInApp_1635_, uint8_t v_skipInstances_1636_, lean_object* v_fvars_1637_, lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
if (lean_obj_tag(v_e_1638_) == 6)
{
lean_object* v_binderName_1645_; lean_object* v_binderType_1646_; lean_object* v_body_1647_; uint8_t v_binderInfo_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___f_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_binderName_1645_ = lean_ctor_get(v_e_1638_, 0);
lean_inc(v_binderName_1645_);
v_binderType_1646_ = lean_ctor_get(v_e_1638_, 1);
lean_inc_ref(v_binderType_1646_);
v_body_1647_ = lean_ctor_get(v_e_1638_, 2);
lean_inc_ref(v_body_1647_);
v_binderInfo_1648_ = lean_ctor_get_uint8(v_e_1638_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1638_, 3);
v___x_1649_ = lean_box(v_usedLetOnly_1634_);
v___x_1650_ = lean_box(v_skipConstInApp_1635_);
v___x_1651_ = lean_box(v_skipInstances_1636_);
lean_inc_ref(v_post_1633_);
lean_inc_ref(v_pre_1632_);
lean_inc_ref(v_fvars_1637_);
v___f_1652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1652_, 0, v_fvars_1637_);
lean_closure_set(v___f_1652_, 1, v_pre_1632_);
lean_closure_set(v___f_1652_, 2, v_post_1633_);
lean_closure_set(v___f_1652_, 3, v___x_1649_);
lean_closure_set(v___f_1652_, 4, v___x_1650_);
lean_closure_set(v___f_1652_, 5, v___x_1651_);
lean_closure_set(v___f_1652_, 6, v_body_1647_);
v___x_1653_ = lean_expr_instantiate_rev(v_binderType_1646_, v_fvars_1637_);
lean_dec_ref(v_fvars_1637_);
lean_dec_ref(v_binderType_1646_);
v___x_1654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1632_, v_post_1633_, v_usedLetOnly_1634_, v_skipConstInApp_1635_, v_skipInstances_1636_, v___x_1653_, v_a_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = 0;
v___x_1657_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_1645_, v_binderInfo_1648_, v_a_1655_, v___f_1652_, v___x_1656_, v_a_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1657_;
}
else
{
lean_dec_ref(v___f_1652_);
lean_dec(v_binderName_1645_);
return v___x_1654_;
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_expr_instantiate_rev(v_e_1638_, v_fvars_1637_);
lean_dec_ref(v_e_1638_);
lean_inc_ref(v_post_1633_);
lean_inc_ref(v_pre_1632_);
v___x_1659_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1632_, v_post_1633_, v_usedLetOnly_1634_, v_skipConstInApp_1635_, v_skipInstances_1636_, v___x_1658_, v_a_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; uint8_t v___x_1661_; uint8_t v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = 0;
v___x_1662_ = 1;
v___x_1663_ = 1;
v___x_1664_ = l_Lean_Meta_mkLambdaFVars(v_fvars_1637_, v_a_1660_, v___x_1661_, v_usedLetOnly_1634_, v___x_1661_, v___x_1662_, v___x_1663_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec_ref(v_fvars_1637_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v___x_1666_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1632_, v_post_1633_, v_usedLetOnly_1634_, v_skipConstInApp_1635_, v_skipInstances_1636_, v_a_1665_, v_a_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
return v___x_1666_;
}
else
{
lean_dec_ref(v_post_1633_);
lean_dec_ref(v_pre_1632_);
return v___x_1664_;
}
}
else
{
lean_dec_ref(v_fvars_1637_);
lean_dec_ref(v_post_1633_);
lean_dec_ref(v_pre_1632_);
return v___x_1659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(lean_object* v_fvars_1667_, lean_object* v_pre_1668_, lean_object* v_post_1669_, uint8_t v_usedLetOnly_1670_, uint8_t v_skipConstInApp_1671_, uint8_t v_skipInstances_1672_, lean_object* v_body_1673_, lean_object* v_x_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_array_push(v_fvars_1667_, v_x_1674_);
v___x_1682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1668_, v_post_1669_, v_usedLetOnly_1670_, v_skipConstInApp_1671_, v_skipInstances_1672_, v___x_1681_, v_body_1673_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed(lean_object* v_fvars_1683_, lean_object* v_pre_1684_, lean_object* v_post_1685_, lean_object* v_usedLetOnly_1686_, lean_object* v_skipConstInApp_1687_, lean_object* v_skipInstances_1688_, lean_object* v_body_1689_, lean_object* v_x_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v_usedLetOnly_boxed_1697_; uint8_t v_skipConstInApp_boxed_1698_; uint8_t v_skipInstances_boxed_1699_; lean_object* v_res_1700_; 
v_usedLetOnly_boxed_1697_ = lean_unbox(v_usedLetOnly_1686_);
v_skipConstInApp_boxed_1698_ = lean_unbox(v_skipConstInApp_1687_);
v_skipInstances_boxed_1699_ = lean_unbox(v_skipInstances_1688_);
v_res_1700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0(v_fvars_1683_, v_pre_1684_, v_post_1685_, v_usedLetOnly_boxed_1697_, v_skipConstInApp_boxed_1698_, v_skipInstances_boxed_1699_, v_body_1689_, v_x_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(lean_object* v_pre_1701_, lean_object* v_post_1702_, uint8_t v_usedLetOnly_1703_, uint8_t v_skipConstInApp_1704_, uint8_t v_skipInstances_1705_, lean_object* v_fvars_1706_, lean_object* v_e_1707_, lean_object* v_a_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
if (lean_obj_tag(v_e_1707_) == 8)
{
lean_object* v_declName_1714_; lean_object* v_type_1715_; lean_object* v_value_1716_; lean_object* v_body_1717_; uint8_t v_nondep_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_declName_1714_ = lean_ctor_get(v_e_1707_, 0);
lean_inc(v_declName_1714_);
v_type_1715_ = lean_ctor_get(v_e_1707_, 1);
lean_inc_ref(v_type_1715_);
v_value_1716_ = lean_ctor_get(v_e_1707_, 2);
lean_inc_ref(v_value_1716_);
v_body_1717_ = lean_ctor_get(v_e_1707_, 3);
lean_inc_ref(v_body_1717_);
v_nondep_1718_ = lean_ctor_get_uint8(v_e_1707_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_1707_, 4);
v___x_1719_ = lean_box(v_usedLetOnly_1703_);
v___x_1720_ = lean_box(v_skipConstInApp_1704_);
v___x_1721_ = lean_box(v_skipInstances_1705_);
lean_inc_ref_n(v_post_1702_, 2);
lean_inc_ref_n(v_pre_1701_, 2);
lean_inc_ref(v_fvars_1706_);
v___f_1722_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1722_, 0, v_fvars_1706_);
lean_closure_set(v___f_1722_, 1, v_pre_1701_);
lean_closure_set(v___f_1722_, 2, v_post_1702_);
lean_closure_set(v___f_1722_, 3, v___x_1719_);
lean_closure_set(v___f_1722_, 4, v___x_1720_);
lean_closure_set(v___f_1722_, 5, v___x_1721_);
lean_closure_set(v___f_1722_, 6, v_body_1717_);
v___x_1723_ = lean_expr_instantiate_rev(v_type_1715_, v_fvars_1706_);
lean_dec_ref(v_type_1715_);
v___x_1724_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1701_, v_post_1702_, v_usedLetOnly_1703_, v_skipConstInApp_1704_, v_skipInstances_1705_, v___x_1723_, v_a_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = lean_expr_instantiate_rev(v_value_1716_, v_fvars_1706_);
lean_dec_ref(v_fvars_1706_);
lean_dec_ref(v_value_1716_);
v___x_1727_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1701_, v_post_1702_, v_usedLetOnly_1703_, v_skipConstInApp_1704_, v_skipInstances_1705_, v___x_1726_, v_a_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = 0;
v___x_1730_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_declName_1714_, v_a_1725_, v_a_1728_, v___f_1722_, v_nondep_1718_, v___x_1729_, v_a_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1730_;
}
else
{
lean_dec(v_a_1725_);
lean_dec_ref(v___f_1722_);
lean_dec(v_declName_1714_);
return v___x_1727_;
}
}
else
{
lean_dec_ref(v___f_1722_);
lean_dec_ref(v_value_1716_);
lean_dec(v_declName_1714_);
lean_dec_ref(v_fvars_1706_);
lean_dec_ref(v_post_1702_);
lean_dec_ref(v_pre_1701_);
return v___x_1724_;
}
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_expr_instantiate_rev(v_e_1707_, v_fvars_1706_);
lean_dec_ref(v_e_1707_);
lean_inc_ref(v_post_1702_);
lean_inc_ref(v_pre_1701_);
v___x_1732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1701_, v_post_1702_, v_usedLetOnly_1703_, v_skipConstInApp_1704_, v_skipInstances_1705_, v___x_1731_, v_a_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; uint8_t v___x_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = 0;
v___x_1735_ = 1;
v___x_1736_ = l_Lean_Meta_mkLetFVars(v_fvars_1706_, v_a_1733_, v_usedLetOnly_1703_, v___x_1734_, v___x_1735_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec_ref(v_fvars_1706_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1738_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1701_, v_post_1702_, v_usedLetOnly_1703_, v_skipConstInApp_1704_, v_skipInstances_1705_, v_a_1737_, v_a_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1738_;
}
else
{
lean_dec_ref(v_post_1702_);
lean_dec_ref(v_pre_1701_);
return v___x_1736_;
}
}
else
{
lean_dec_ref(v_fvars_1706_);
lean_dec_ref(v_post_1702_);
lean_dec_ref(v_pre_1701_);
return v___x_1732_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1739_; lean_object* v_dummy_1740_; 
v___x_1739_ = lean_box(0);
v_dummy_1740_ = l_Lean_Expr_sort___override(v___x_1739_);
return v_dummy_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(lean_object* v_pre_1741_, lean_object* v_post_1742_, uint8_t v_usedLetOnly_1743_, uint8_t v_skipConstInApp_1744_, uint8_t v_skipInstances_1745_, size_t v_sz_1746_, size_t v_i_1747_, lean_object* v_bs_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_usize_dec_lt(v_i_1747_, v_sz_1746_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_dec_ref(v_post_1742_);
lean_dec_ref(v_pre_1741_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v_bs_1748_);
return v___x_1756_;
}
else
{
lean_object* v_v_1757_; lean_object* v___x_1758_; lean_object* v_bs_x27_1759_; lean_object* v___x_1760_; 
v_v_1757_ = lean_array_uget(v_bs_1748_, v_i_1747_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v_bs_x27_1759_ = lean_array_uset(v_bs_1748_, v_i_1747_, v___x_1758_);
lean_inc_ref(v_post_1742_);
lean_inc_ref(v_pre_1741_);
v___x_1760_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1741_, v_post_1742_, v_usedLetOnly_1743_, v_skipConstInApp_1744_, v_skipInstances_1745_, v_v_1757_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; size_t v___x_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = lean_usize_add(v_i_1747_, v___x_1762_);
v___x_1764_ = lean_array_uset(v_bs_x27_1759_, v_i_1747_, v_a_1761_);
v_i_1747_ = v___x_1763_;
v_bs_1748_ = v___x_1764_;
goto _start;
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v_bs_x27_1759_);
lean_dec_ref(v_post_1742_);
lean_dec_ref(v_pre_1741_);
v_a_1766_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1760_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1760_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(lean_object* v_pre_1774_, lean_object* v_post_1775_, uint8_t v_usedLetOnly_1776_, uint8_t v_skipConstInApp_1777_, uint8_t v_skipInstances_1778_, lean_object* v___x_1779_, lean_object* v___y_1780_, lean_object* v_b_1781_, lean_object* v_a_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1774_, v_post_1775_, v_usedLetOnly_1776_, v_skipConstInApp_1777_, v_skipInstances_1778_, v___x_1779_, v___y_1780_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1798_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1798_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1798_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1793_ = lean_array_fset(v_b_1781_, v_a_1782_, v_a_1789_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v___x_1794_);
v___x_1796_ = v___x_1791_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v_b_1781_);
v_a_1799_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1788_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1788_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed(lean_object* v_pre_1807_, lean_object* v_post_1808_, lean_object* v_usedLetOnly_1809_, lean_object* v_skipConstInApp_1810_, lean_object* v_skipInstances_1811_, lean_object* v___x_1812_, lean_object* v___y_1813_, lean_object* v_b_1814_, lean_object* v_a_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
uint8_t v_usedLetOnly_boxed_1821_; uint8_t v_skipConstInApp_boxed_1822_; uint8_t v_skipInstances_boxed_1823_; lean_object* v_res_1824_; 
v_usedLetOnly_boxed_1821_ = lean_unbox(v_usedLetOnly_1809_);
v_skipConstInApp_boxed_1822_ = lean_unbox(v_skipConstInApp_1810_);
v_skipInstances_boxed_1823_ = lean_unbox(v_skipInstances_1811_);
v_res_1824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0(v_pre_1807_, v_post_1808_, v_usedLetOnly_boxed_1821_, v_skipConstInApp_boxed_1822_, v_skipInstances_boxed_1823_, v___x_1812_, v___y_1813_, v_b_1814_, v_a_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v_a_1815_);
lean_dec(v___y_1813_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(lean_object* v_upperBound_1825_, lean_object* v___x_1826_, lean_object* v_pre_1827_, lean_object* v_post_1828_, uint8_t v_usedLetOnly_1829_, uint8_t v_skipConstInApp_1830_, uint8_t v_skipInstances_1831_, lean_object* v_a_1832_, lean_object* v_b_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___y_1841_; uint8_t v___x_1864_; 
v___x_1864_ = lean_nat_dec_lt(v_a_1832_, v_upperBound_1825_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_post_1828_);
lean_dec_ref(v_pre_1827_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v_b_1833_);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1866_ = lean_array_fget_borrowed(v_b_1833_, v_a_1832_);
v___x_1867_ = lean_array_get_size(v___x_1826_);
v___x_1868_ = lean_nat_dec_lt(v_a_1832_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___f_1872_; 
lean_inc(v___x_1866_);
v___x_1869_ = lean_box(v_usedLetOnly_1829_);
v___x_1870_ = lean_box(v_skipConstInApp_1830_);
v___x_1871_ = lean_box(v_skipInstances_1831_);
lean_inc(v_a_1832_);
lean_inc(v___y_1834_);
lean_inc_ref(v_post_1828_);
lean_inc_ref(v_pre_1827_);
v___f_1872_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1872_, 0, v_pre_1827_);
lean_closure_set(v___f_1872_, 1, v_post_1828_);
lean_closure_set(v___f_1872_, 2, v___x_1869_);
lean_closure_set(v___f_1872_, 3, v___x_1870_);
lean_closure_set(v___f_1872_, 4, v___x_1871_);
lean_closure_set(v___f_1872_, 5, v___x_1866_);
lean_closure_set(v___f_1872_, 6, v___y_1834_);
lean_closure_set(v___f_1872_, 7, v_b_1833_);
lean_closure_set(v___f_1872_, 8, v_a_1832_);
v___y_1841_ = v___f_1872_;
goto v___jp_1840_;
}
else
{
lean_object* v___x_1873_; uint8_t v_isInstance_1874_; 
v___x_1873_ = lean_array_fget_borrowed(v___x_1826_, v_a_1832_);
v_isInstance_1874_ = lean_ctor_get_uint8(v___x_1873_, sizeof(void*)*1 + 4);
if (v_isInstance_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___f_1878_; 
lean_inc(v___x_1866_);
v___x_1875_ = lean_box(v_usedLetOnly_1829_);
v___x_1876_ = lean_box(v_skipConstInApp_1830_);
v___x_1877_ = lean_box(v_skipInstances_1831_);
lean_inc(v_a_1832_);
lean_inc(v___y_1834_);
lean_inc_ref(v_post_1828_);
lean_inc_ref(v_pre_1827_);
v___f_1878_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_1878_, 0, v_pre_1827_);
lean_closure_set(v___f_1878_, 1, v_post_1828_);
lean_closure_set(v___f_1878_, 2, v___x_1875_);
lean_closure_set(v___f_1878_, 3, v___x_1876_);
lean_closure_set(v___f_1878_, 4, v___x_1877_);
lean_closure_set(v___f_1878_, 5, v___x_1866_);
lean_closure_set(v___f_1878_, 6, v___y_1834_);
lean_closure_set(v___f_1878_, 7, v_b_1833_);
lean_closure_set(v___f_1878_, 8, v_a_1832_);
v___y_1841_ = v___f_1878_;
goto v___jp_1840_;
}
else
{
lean_object* v___x_1879_; lean_object* v___f_1880_; 
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_b_1833_);
v___f_1880_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1880_, 0, v___x_1879_);
v___y_1841_ = v___f_1880_;
goto v___jp_1840_;
}
}
}
v___jp_1840_:
{
lean_object* v___x_1842_; 
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
v___x_1842_ = lean_apply_5(v___y_1841_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, lean_box(0));
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1855_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1855_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1855_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
if (lean_obj_tag(v_a_1843_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_post_1828_);
lean_dec_ref(v_pre_1827_);
v_a_1847_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v_a_1843_, 1);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v_a_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_del_object(v___x_1845_);
v_a_1851_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v_a_1843_, 1);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_add(v_a_1832_, v___x_1852_);
lean_dec(v_a_1832_);
v_a_1832_ = v___x_1853_;
v_b_1833_ = v_a_1851_;
goto _start;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_a_1832_);
lean_dec_ref(v_post_1828_);
lean_dec_ref(v_pre_1827_);
v_a_1856_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1842_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1842_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(uint8_t v_skipInstances_1881_, lean_object* v_pre_1882_, lean_object* v_post_1883_, uint8_t v_usedLetOnly_1884_, uint8_t v_skipConstInApp_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_f_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; 
if (lean_obj_tag(v_x_1886_) == 5)
{
lean_object* v_fn_1944_; lean_object* v_arg_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_fn_1944_ = lean_ctor_get(v_x_1886_, 0);
lean_inc_ref(v_fn_1944_);
v_arg_1945_ = lean_ctor_get(v_x_1886_, 1);
lean_inc_ref(v_arg_1945_);
lean_dec_ref_known(v_x_1886_, 2);
v___x_1946_ = lean_array_set(v_x_1887_, v_x_1888_, v_arg_1945_);
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_sub(v_x_1888_, v___x_1947_);
lean_dec(v_x_1888_);
v_x_1886_ = v_fn_1944_;
v_x_1887_ = v___x_1946_;
v_x_1888_ = v___x_1948_;
goto _start;
}
else
{
lean_dec(v_x_1888_);
if (v_skipConstInApp_1885_ == 0)
{
goto v___jp_1941_;
}
else
{
uint8_t v___x_1950_; 
v___x_1950_ = l_Lean_Expr_isConst(v_x_1886_);
if (v___x_1950_ == 0)
{
goto v___jp_1941_;
}
else
{
v_f_1896_ = v_x_1886_;
v___y_1897_ = v___y_1889_;
v___y_1898_ = v___y_1890_;
v___y_1899_ = v___y_1891_;
v___y_1900_ = v___y_1892_;
v___y_1901_ = v___y_1893_;
goto v___jp_1895_;
}
}
}
v___jp_1895_:
{
if (v_skipInstances_1881_ == 0)
{
size_t v_sz_1902_; size_t v___x_1903_; lean_object* v___x_1904_; 
v_sz_1902_ = lean_array_size(v_x_1887_);
v___x_1903_ = ((size_t)0ULL);
lean_inc_ref(v_post_1883_);
lean_inc_ref(v_pre_1882_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_1882_, v_post_1883_, v_usedLetOnly_1884_, v_skipConstInApp_1885_, v_skipInstances_1881_, v_sz_1902_, v___x_1903_, v_x_1887_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = l_Lean_mkAppN(v_f_1896_, v_a_1905_);
lean_dec(v_a_1905_);
v___x_1907_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1882_, v_post_1883_, v_usedLetOnly_1884_, v_skipConstInApp_1885_, v_skipInstances_1881_, v___x_1906_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
return v___x_1907_;
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v_f_1896_);
lean_dec_ref(v_post_1883_);
lean_dec_ref(v_pre_1882_);
v_a_1908_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1904_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1904_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_array_get_size(v_x_1887_);
lean_inc_ref(v_f_1896_);
v___x_1917_ = l_Lean_Meta_getFunInfoNArgs(v_f_1896_, v___x_1916_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v_paramInfo_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v_paramInfo_1919_ = lean_ctor_get(v_a_1918_, 0);
lean_inc_ref(v_paramInfo_1919_);
lean_dec(v_a_1918_);
v___x_1920_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_1883_);
lean_inc_ref(v_pre_1882_);
v___x_1921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v___x_1916_, v_paramInfo_1919_, v_pre_1882_, v_post_1883_, v_usedLetOnly_1884_, v_skipConstInApp_1885_, v_skipInstances_1881_, v___x_1920_, v_x_1887_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec_ref(v_paramInfo_1919_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = l_Lean_mkAppN(v_f_1896_, v_a_1922_);
lean_dec(v_a_1922_);
v___x_1924_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1882_, v_post_1883_, v_usedLetOnly_1884_, v_skipConstInApp_1885_, v_skipInstances_1881_, v___x_1923_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
return v___x_1924_;
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec_ref(v_f_1896_);
lean_dec_ref(v_post_1883_);
lean_dec_ref(v_pre_1882_);
v_a_1925_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1921_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1921_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v_f_1896_);
lean_dec_ref(v_x_1887_);
lean_dec_ref(v_post_1883_);
lean_dec_ref(v_pre_1882_);
v_a_1933_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1917_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1917_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
v___jp_1941_:
{
lean_object* v___x_1942_; 
lean_inc_ref(v_post_1883_);
lean_inc_ref(v_pre_1882_);
v___x_1942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1882_, v_post_1883_, v_usedLetOnly_1884_, v_skipConstInApp_1885_, v_skipInstances_1881_, v_x_1886_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v_f_1896_ = v_a_1943_;
v___y_1897_ = v___y_1889_;
v___y_1898_ = v___y_1890_;
v___y_1899_ = v___y_1891_;
v___y_1900_ = v___y_1892_;
v___y_1901_ = v___y_1893_;
goto v___jp_1895_;
}
else
{
lean_dec_ref(v_x_1887_);
lean_dec_ref(v_post_1883_);
lean_dec_ref(v_pre_1882_);
return v___x_1942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(lean_object* v___x_1951_, lean_object* v_pre_1952_, lean_object* v_e_1953_, lean_object* v_post_1954_, uint8_t v_usedLetOnly_1955_, uint8_t v_skipConstInApp_1956_, uint8_t v_skipInstances_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Core_checkSystem(v___x_1951_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref_known(v___x_1964_, 1);
lean_inc_ref(v_pre_1952_);
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc_ref(v_e_1953_);
v___x_1965_ = lean_apply_6(v_pre_1952_, v_e_1953_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, lean_box(0));
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2014_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_2014_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2014_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___y_1971_; 
switch(lean_obj_tag(v_a_1966_))
{
case 0:
{
lean_object* v_e_2006_; lean_object* v___x_2008_; 
lean_dec_ref(v_post_1954_);
lean_dec_ref(v_e_1953_);
lean_dec_ref(v_pre_1952_);
v_e_2006_ = lean_ctor_get(v_a_1966_, 0);
lean_inc_ref(v_e_2006_);
lean_dec_ref_known(v_a_1966_, 1);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v_e_2006_);
v___x_2008_ = v___x_1968_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_e_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
case 1:
{
lean_object* v_e_2010_; lean_object* v___x_2011_; 
lean_del_object(v___x_1968_);
lean_dec_ref(v_e_1953_);
v_e_2010_ = lean_ctor_get(v_a_1966_, 0);
lean_inc_ref(v_e_2010_);
lean_dec_ref_known(v_a_1966_, 1);
v___x_2011_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v_e_2010_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_2011_;
}
default: 
{
lean_object* v_e_x3f_2012_; 
lean_del_object(v___x_1968_);
v_e_x3f_2012_ = lean_ctor_get(v_a_1966_, 0);
lean_inc(v_e_x3f_2012_);
lean_dec_ref_known(v_a_1966_, 1);
if (lean_obj_tag(v_e_x3f_2012_) == 0)
{
v___y_1971_ = v_e_1953_;
goto v___jp_1970_;
}
else
{
lean_object* v_val_2013_; 
lean_dec_ref(v_e_1953_);
v_val_2013_ = lean_ctor_get(v_e_x3f_2012_, 0);
lean_inc(v_val_2013_);
lean_dec_ref_known(v_e_x3f_2012_, 1);
v___y_1971_ = v_val_2013_;
goto v___jp_1970_;
}
}
}
v___jp_1970_:
{
switch(lean_obj_tag(v___y_1971_))
{
case 7:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v___x_1972_, v___y_1971_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1973_;
}
case 6:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1975_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v___x_1974_, v___y_1971_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1975_;
}
case 8:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__0));
v___x_1977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v___x_1976_, v___y_1971_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1977_;
}
case 5:
{
lean_object* v_dummy_1978_; lean_object* v_nargs_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_dummy_1978_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_1979_ = l_Lean_Expr_getAppNumArgs(v___y_1971_);
lean_inc(v_nargs_1979_);
v___x_1980_ = lean_mk_array(v_nargs_1979_, v_dummy_1978_);
v___x_1981_ = lean_unsigned_to_nat(1u);
v___x_1982_ = lean_nat_sub(v_nargs_1979_, v___x_1981_);
lean_dec(v_nargs_1979_);
v___x_1983_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_1957_, v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v___y_1971_, v___x_1980_, v___x_1982_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1983_;
}
case 10:
{
lean_object* v_data_1984_; lean_object* v_expr_1985_; lean_object* v___x_1986_; 
v_data_1984_ = lean_ctor_get(v___y_1971_, 0);
v_expr_1985_ = lean_ctor_get(v___y_1971_, 1);
lean_inc_ref(v_expr_1985_);
lean_inc_ref(v_post_1954_);
lean_inc_ref(v_pre_1952_);
v___x_1986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v_expr_1985_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; size_t v___x_1988_; size_t v___x_1989_; uint8_t v___x_1990_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = lean_ptr_addr(v_expr_1985_);
v___x_1989_ = lean_ptr_addr(v_a_1987_);
v___x_1990_ = lean_usize_dec_eq(v___x_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_inc(v_data_1984_);
lean_dec_ref_known(v___y_1971_, 2);
v___x_1991_ = l_Lean_Expr_mdata___override(v_data_1984_, v_a_1987_);
v___x_1992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v___x_1991_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; 
lean_dec(v_a_1987_);
v___x_1993_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v___y_1971_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1993_;
}
}
else
{
lean_dec_ref_known(v___y_1971_, 2);
lean_dec_ref(v_post_1954_);
lean_dec_ref(v_pre_1952_);
return v___x_1986_;
}
}
case 11:
{
lean_object* v_typeName_1994_; lean_object* v_idx_1995_; lean_object* v_struct_1996_; lean_object* v___x_1997_; 
v_typeName_1994_ = lean_ctor_get(v___y_1971_, 0);
v_idx_1995_ = lean_ctor_get(v___y_1971_, 1);
v_struct_1996_ = lean_ctor_get(v___y_1971_, 2);
lean_inc_ref(v_struct_1996_);
lean_inc_ref(v_post_1954_);
lean_inc_ref(v_pre_1952_);
v___x_1997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v_struct_1996_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; size_t v___x_1999_; size_t v___x_2000_; uint8_t v___x_2001_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = lean_ptr_addr(v_struct_1996_);
v___x_2000_ = lean_ptr_addr(v_a_1998_);
v___x_2001_ = lean_usize_dec_eq(v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_inc(v_idx_1995_);
lean_inc(v_typeName_1994_);
lean_dec_ref_known(v___y_1971_, 3);
v___x_2002_ = l_Lean_Expr_proj___override(v_typeName_1994_, v_idx_1995_, v_a_1998_);
v___x_2003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v___x_2002_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; 
lean_dec(v_a_1998_);
v___x_2004_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v___y_1971_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_2004_;
}
}
else
{
lean_dec_ref_known(v___y_1971_, 3);
lean_dec_ref(v_post_1954_);
lean_dec_ref(v_pre_1952_);
return v___x_1997_;
}
}
default: 
{
lean_object* v___x_2005_; 
v___x_2005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_1952_, v_post_1954_, v_usedLetOnly_1955_, v_skipConstInApp_1956_, v_skipInstances_1957_, v___y_1971_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_2005_;
}
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v_post_1954_);
lean_dec_ref(v_e_1953_);
lean_dec_ref(v_pre_1952_);
v_a_2015_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1965_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1965_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_post_1954_);
lean_dec_ref(v_e_1953_);
lean_dec_ref(v_pre_1952_);
v_a_2023_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1964_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1964_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed(lean_object* v___x_2031_, lean_object* v_pre_2032_, lean_object* v_e_2033_, lean_object* v_post_2034_, lean_object* v_usedLetOnly_2035_, lean_object* v_skipConstInApp_2036_, lean_object* v_skipInstances_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v_usedLetOnly_boxed_2044_; uint8_t v_skipConstInApp_boxed_2045_; uint8_t v_skipInstances_boxed_2046_; lean_object* v_res_2047_; 
v_usedLetOnly_boxed_2044_ = lean_unbox(v_usedLetOnly_2035_);
v_skipConstInApp_boxed_2045_ = lean_unbox(v_skipConstInApp_2036_);
v_skipInstances_boxed_2046_ = lean_unbox(v_skipInstances_2037_);
v_res_2047_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1(v___x_2031_, v_pre_2032_, v_e_2033_, v_post_2034_, v_usedLetOnly_boxed_2044_, v_skipConstInApp_boxed_2045_, v_skipInstances_boxed_2046_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(lean_object* v_pre_2048_, lean_object* v_post_2049_, uint8_t v_usedLetOnly_2050_, uint8_t v_skipConstInApp_2051_, uint8_t v_skipInstances_2052_, lean_object* v_e_2053_, lean_object* v_a_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_inc(v_a_2054_);
v___x_2060_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2060_, 0, lean_box(0));
lean_closure_set(v___x_2060_, 1, lean_box(0));
lean_closure_set(v___x_2060_, 2, v_a_2054_);
v___x_2061_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___x_2060_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2096_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2096_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2096_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_a_2062_, v_e_2053_);
lean_dec(v_a_2062_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; 
lean_del_object(v___x_2064_);
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___closed__0));
v___x_2068_ = lean_box(v_usedLetOnly_2050_);
v___x_2069_ = lean_box(v_skipConstInApp_2051_);
v___x_2070_ = lean_box(v_skipInstances_2052_);
lean_inc_ref(v_e_2053_);
v___f_2071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2071_, 0, v___x_2067_);
lean_closure_set(v___f_2071_, 1, v_pre_2048_);
lean_closure_set(v___f_2071_, 2, v_e_2053_);
lean_closure_set(v___f_2071_, 3, v_post_2049_);
lean_closure_set(v___f_2071_, 4, v___x_2068_);
lean_closure_set(v___f_2071_, 5, v___x_2069_);
lean_closure_set(v___f_2071_, 6, v___x_2070_);
v___x_2072_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v___f_2071_, v_a_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc_n(v_a_2073_, 2);
lean_dec_ref_known(v___x_2072_, 1);
lean_inc(v_a_2054_);
v___f_2074_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2074_, 0, v_a_2054_);
lean_closure_set(v___f_2074_, 1, v_e_2053_);
lean_closure_set(v___f_2074_, 2, v_a_2073_);
v___x_2075_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__0(lean_box(0), v___f_2074_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v___x_2075_, 0);
lean_dec(v_unused_2083_);
v___x_2077_ = v___x_2075_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v___x_2075_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v_a_2073_);
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2073_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_a_2073_);
v_a_2084_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2075_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2075_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_dec_ref(v_e_2053_);
return v___x_2072_;
}
}
else
{
lean_object* v_val_2092_; lean_object* v___x_2094_; 
lean_dec_ref(v_e_2053_);
lean_dec_ref(v_post_2049_);
lean_dec_ref(v_pre_2048_);
v_val_2092_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_val_2092_);
lean_dec_ref_known(v___x_2066_, 1);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v_val_2092_);
v___x_2094_ = v___x_2064_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_val_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_e_2053_);
lean_dec_ref(v_post_2049_);
lean_dec_ref(v_pre_2048_);
v_a_2097_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2061_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2061_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(lean_object* v_pre_2105_, lean_object* v_post_2106_, uint8_t v_usedLetOnly_2107_, uint8_t v_skipConstInApp_2108_, uint8_t v_skipInstances_2109_, lean_object* v_fvars_2110_, lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
if (lean_obj_tag(v_e_2111_) == 7)
{
lean_object* v_binderName_2118_; lean_object* v_binderType_2119_; lean_object* v_body_2120_; uint8_t v_binderInfo_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___f_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_binderName_2118_ = lean_ctor_get(v_e_2111_, 0);
lean_inc(v_binderName_2118_);
v_binderType_2119_ = lean_ctor_get(v_e_2111_, 1);
lean_inc_ref(v_binderType_2119_);
v_body_2120_ = lean_ctor_get(v_e_2111_, 2);
lean_inc_ref(v_body_2120_);
v_binderInfo_2121_ = lean_ctor_get_uint8(v_e_2111_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2111_, 3);
v___x_2122_ = lean_box(v_usedLetOnly_2107_);
v___x_2123_ = lean_box(v_skipConstInApp_2108_);
v___x_2124_ = lean_box(v_skipInstances_2109_);
lean_inc_ref(v_post_2106_);
lean_inc_ref(v_pre_2105_);
lean_inc_ref(v_fvars_2110_);
v___f_2125_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2125_, 0, v_fvars_2110_);
lean_closure_set(v___f_2125_, 1, v_pre_2105_);
lean_closure_set(v___f_2125_, 2, v_post_2106_);
lean_closure_set(v___f_2125_, 3, v___x_2122_);
lean_closure_set(v___f_2125_, 4, v___x_2123_);
lean_closure_set(v___f_2125_, 5, v___x_2124_);
lean_closure_set(v___f_2125_, 6, v_body_2120_);
v___x_2126_ = lean_expr_instantiate_rev(v_binderType_2119_, v_fvars_2110_);
lean_dec_ref(v_fvars_2110_);
lean_dec_ref(v_binderType_2119_);
v___x_2127_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2105_, v_post_2106_, v_usedLetOnly_2107_, v_skipConstInApp_2108_, v_skipInstances_2109_, v___x_2126_, v_a_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v___x_2129_ = 0;
v___x_2130_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_binderName_2118_, v_binderInfo_2121_, v_a_2128_, v___f_2125_, v___x_2129_, v_a_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2130_;
}
else
{
lean_dec_ref(v___f_2125_);
lean_dec(v_binderName_2118_);
return v___x_2127_;
}
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_expr_instantiate_rev(v_e_2111_, v_fvars_2110_);
lean_dec_ref(v_e_2111_);
lean_inc_ref(v_post_2106_);
lean_inc_ref(v_pre_2105_);
v___x_2132_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2105_, v_post_2106_, v_usedLetOnly_2107_, v_skipConstInApp_2108_, v_skipInstances_2109_, v___x_2131_, v_a_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; uint8_t v___x_2134_; uint8_t v___x_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = 0;
v___x_2135_ = 1;
v___x_2136_ = 1;
v___x_2137_ = l_Lean_Meta_mkForallFVars(v_fvars_2110_, v_a_2133_, v___x_2134_, v_usedLetOnly_2107_, v___x_2135_, v___x_2136_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec_ref(v_fvars_2110_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2105_, v_post_2106_, v_usedLetOnly_2107_, v_skipConstInApp_2108_, v_skipInstances_2109_, v_a_2138_, v_a_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2139_;
}
else
{
lean_dec_ref(v_post_2106_);
lean_dec_ref(v_pre_2105_);
return v___x_2137_;
}
}
else
{
lean_dec_ref(v_fvars_2110_);
lean_dec_ref(v_post_2106_);
lean_dec_ref(v_pre_2105_);
return v___x_2132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___lam__0(lean_object* v_fvars_2140_, lean_object* v_pre_2141_, lean_object* v_post_2142_, uint8_t v_usedLetOnly_2143_, uint8_t v_skipConstInApp_2144_, uint8_t v_skipInstances_2145_, lean_object* v_body_2146_, lean_object* v_x_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_array_push(v_fvars_2140_, v_x_2147_);
v___x_2155_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2141_, v_post_2142_, v_usedLetOnly_2143_, v_skipConstInApp_2144_, v_skipInstances_2145_, v___x_2154_, v_body_2146_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11___boxed(lean_object* v_pre_2156_, lean_object* v_post_2157_, lean_object* v_usedLetOnly_2158_, lean_object* v_skipConstInApp_2159_, lean_object* v_skipInstances_2160_, lean_object* v_e_2161_, lean_object* v_a_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v_usedLetOnly_boxed_2168_; uint8_t v_skipConstInApp_boxed_2169_; uint8_t v_skipInstances_boxed_2170_; lean_object* v_res_2171_; 
v_usedLetOnly_boxed_2168_ = lean_unbox(v_usedLetOnly_2158_);
v_skipConstInApp_boxed_2169_ = lean_unbox(v_skipConstInApp_2159_);
v_skipInstances_boxed_2170_ = lean_unbox(v_skipInstances_2160_);
v_res_2171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__11(v_pre_2156_, v_post_2157_, v_usedLetOnly_boxed_2168_, v_skipConstInApp_boxed_2169_, v_skipInstances_boxed_2170_, v_e_2161_, v_a_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v_a_2162_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10___boxed(lean_object* v_pre_2172_, lean_object* v_post_2173_, lean_object* v_usedLetOnly_2174_, lean_object* v_skipConstInApp_2175_, lean_object* v_skipInstances_2176_, lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_bs_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
uint8_t v_usedLetOnly_boxed_2186_; uint8_t v_skipConstInApp_boxed_2187_; uint8_t v_skipInstances_boxed_2188_; size_t v_sz_boxed_2189_; size_t v_i_boxed_2190_; lean_object* v_res_2191_; 
v_usedLetOnly_boxed_2186_ = lean_unbox(v_usedLetOnly_2174_);
v_skipConstInApp_boxed_2187_ = lean_unbox(v_skipConstInApp_2175_);
v_skipInstances_boxed_2188_ = lean_unbox(v_skipInstances_2176_);
v_sz_boxed_2189_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2190_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__10(v_pre_2172_, v_post_2173_, v_usedLetOnly_boxed_2186_, v_skipConstInApp_boxed_2187_, v_skipInstances_boxed_2188_, v_sz_boxed_2189_, v_i_boxed_2190_, v_bs_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___boxed(lean_object* v_pre_2192_, lean_object* v_post_2193_, lean_object* v_usedLetOnly_2194_, lean_object* v_skipConstInApp_2195_, lean_object* v_skipInstances_2196_, lean_object* v_e_2197_, lean_object* v_a_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v_usedLetOnly_boxed_2204_; uint8_t v_skipConstInApp_boxed_2205_; uint8_t v_skipInstances_boxed_2206_; lean_object* v_res_2207_; 
v_usedLetOnly_boxed_2204_ = lean_unbox(v_usedLetOnly_2194_);
v_skipConstInApp_boxed_2205_ = lean_unbox(v_skipConstInApp_2195_);
v_skipInstances_boxed_2206_ = lean_unbox(v_skipInstances_2196_);
v_res_2207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2192_, v_post_2193_, v_usedLetOnly_boxed_2204_, v_skipConstInApp_boxed_2205_, v_skipInstances_boxed_2206_, v_e_2197_, v_a_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v_a_2198_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14___boxed(lean_object* v_pre_2208_, lean_object* v_post_2209_, lean_object* v_usedLetOnly_2210_, lean_object* v_skipConstInApp_2211_, lean_object* v_skipInstances_2212_, lean_object* v_fvars_2213_, lean_object* v_e_2214_, lean_object* v_a_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v_usedLetOnly_boxed_2221_; uint8_t v_skipConstInApp_boxed_2222_; uint8_t v_skipInstances_boxed_2223_; lean_object* v_res_2224_; 
v_usedLetOnly_boxed_2221_ = lean_unbox(v_usedLetOnly_2210_);
v_skipConstInApp_boxed_2222_ = lean_unbox(v_skipConstInApp_2211_);
v_skipInstances_boxed_2223_ = lean_unbox(v_skipInstances_2212_);
v_res_2224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14(v_pre_2208_, v_post_2209_, v_usedLetOnly_boxed_2221_, v_skipConstInApp_boxed_2222_, v_skipInstances_boxed_2223_, v_fvars_2213_, v_e_2214_, v_a_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v_a_2215_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15___boxed(lean_object* v_pre_2225_, lean_object* v_post_2226_, lean_object* v_usedLetOnly_2227_, lean_object* v_skipConstInApp_2228_, lean_object* v_skipInstances_2229_, lean_object* v_fvars_2230_, lean_object* v_e_2231_, lean_object* v_a_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
uint8_t v_usedLetOnly_boxed_2238_; uint8_t v_skipConstInApp_boxed_2239_; uint8_t v_skipInstances_boxed_2240_; lean_object* v_res_2241_; 
v_usedLetOnly_boxed_2238_ = lean_unbox(v_usedLetOnly_2227_);
v_skipConstInApp_boxed_2239_ = lean_unbox(v_skipConstInApp_2228_);
v_skipInstances_boxed_2240_ = lean_unbox(v_skipInstances_2229_);
v_res_2241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__15(v_pre_2225_, v_post_2226_, v_usedLetOnly_boxed_2238_, v_skipConstInApp_boxed_2239_, v_skipInstances_boxed_2240_, v_fvars_2230_, v_e_2231_, v_a_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v_a_2232_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16___boxed(lean_object* v_pre_2242_, lean_object* v_post_2243_, lean_object* v_usedLetOnly_2244_, lean_object* v_skipConstInApp_2245_, lean_object* v_skipInstances_2246_, lean_object* v_fvars_2247_, lean_object* v_e_2248_, lean_object* v_a_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v_usedLetOnly_boxed_2255_; uint8_t v_skipConstInApp_boxed_2256_; uint8_t v_skipInstances_boxed_2257_; lean_object* v_res_2258_; 
v_usedLetOnly_boxed_2255_ = lean_unbox(v_usedLetOnly_2244_);
v_skipConstInApp_boxed_2256_ = lean_unbox(v_skipConstInApp_2245_);
v_skipInstances_boxed_2257_ = lean_unbox(v_skipInstances_2246_);
v_res_2258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16(v_pre_2242_, v_post_2243_, v_usedLetOnly_boxed_2255_, v_skipConstInApp_boxed_2256_, v_skipInstances_boxed_2257_, v_fvars_2247_, v_e_2248_, v_a_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v_a_2249_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg___boxed(lean_object* v_upperBound_2259_, lean_object* v___x_2260_, lean_object* v_pre_2261_, lean_object* v_post_2262_, lean_object* v_usedLetOnly_2263_, lean_object* v_skipConstInApp_2264_, lean_object* v_skipInstances_2265_, lean_object* v_a_2266_, lean_object* v_b_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
uint8_t v_usedLetOnly_boxed_2274_; uint8_t v_skipConstInApp_boxed_2275_; uint8_t v_skipInstances_boxed_2276_; lean_object* v_res_2277_; 
v_usedLetOnly_boxed_2274_ = lean_unbox(v_usedLetOnly_2263_);
v_skipConstInApp_boxed_2275_ = lean_unbox(v_skipConstInApp_2264_);
v_skipInstances_boxed_2276_ = lean_unbox(v_skipInstances_2265_);
v_res_2277_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_2259_, v___x_2260_, v_pre_2261_, v_post_2262_, v_usedLetOnly_boxed_2274_, v_skipConstInApp_boxed_2275_, v_skipInstances_boxed_2276_, v_a_2266_, v_b_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___x_2260_);
lean_dec(v_upperBound_2259_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17___boxed(lean_object* v_skipInstances_2278_, lean_object* v_pre_2279_, lean_object* v_post_2280_, lean_object* v_usedLetOnly_2281_, lean_object* v_skipConstInApp_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v_skipInstances_boxed_2292_; uint8_t v_usedLetOnly_boxed_2293_; uint8_t v_skipConstInApp_boxed_2294_; lean_object* v_res_2295_; 
v_skipInstances_boxed_2292_ = lean_unbox(v_skipInstances_2278_);
v_usedLetOnly_boxed_2293_ = lean_unbox(v_usedLetOnly_2281_);
v_skipConstInApp_boxed_2294_ = lean_unbox(v_skipConstInApp_2282_);
v_res_2295_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__17(v_skipInstances_boxed_2292_, v_pre_2279_, v_post_2280_, v_usedLetOnly_boxed_2293_, v_skipConstInApp_boxed_2294_, v_x_2283_, v_x_2284_, v_x_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
return v_res_2295_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Elab_getParamRevDeps_spec__0___redArg___closed__2);
v___x_2297_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2297_, 0, lean_box(0));
lean_closure_set(v___x_2297_, 1, lean_box(0));
lean_closure_set(v___x_2297_, 2, v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(lean_object* v_input_2298_, lean_object* v_pre_2299_, lean_object* v_post_2300_, uint8_t v_usedLetOnly_2301_, uint8_t v_skipConstInApp_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
uint8_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_a_2311_; lean_object* v___x_2312_; 
v___x_2308_ = 0;
v___x_2309_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___closed__0);
v___x_2310_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2309_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9(v_pre_2299_, v_post_2300_, v_usedLetOnly_2301_, v_skipConstInApp_2302_, v___x_2308_, v_input_2298_, v_a_2311_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v___x_2314_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2314_, 0, lean_box(0));
lean_closure_set(v___x_2314_, 1, lean_box(0));
lean_closure_set(v___x_2314_, 2, v_a_2311_);
v___x_2315_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___lam__0(lean_box(0), v___x_2314_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2315_, 0);
lean_dec(v_unused_2323_);
v___x_2317_ = v___x_2315_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v___x_2315_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v_a_2313_);
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2313_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
else
{
lean_dec(v_a_2311_);
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8___boxed(lean_object* v_input_2324_, lean_object* v_pre_2325_, lean_object* v_post_2326_, lean_object* v_usedLetOnly_2327_, lean_object* v_skipConstInApp_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v_usedLetOnly_boxed_2334_; uint8_t v_skipConstInApp_boxed_2335_; lean_object* v_res_2336_; 
v_usedLetOnly_boxed_2334_ = lean_unbox(v_usedLetOnly_2327_);
v_skipConstInApp_boxed_2335_ = lean_unbox(v_skipConstInApp_2328_);
v_res_2336_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_input_2324_, v_pre_2325_, v_post_2326_, v_usedLetOnly_boxed_2334_, v_skipConstInApp_boxed_2335_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(lean_object* v___x_2337_, lean_object* v_as_2338_, lean_object* v_j_2339_){
_start:
{
lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = lean_array_get_size(v_as_2338_);
v___x_2341_ = lean_nat_dec_lt(v_j_2339_, v___x_2340_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
lean_dec(v_j_2339_);
v___x_2342_ = lean_box(0);
return v___x_2342_;
}
else
{
lean_object* v___x_2343_; lean_object* v_declName_2344_; uint8_t v___x_2345_; 
v___x_2343_ = lean_array_fget_borrowed(v_as_2338_, v_j_2339_);
v_declName_2344_ = lean_ctor_get(v___x_2343_, 3);
v___x_2345_ = lean_name_eq(v_declName_2344_, v___x_2337_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_unsigned_to_nat(1u);
v___x_2347_ = lean_nat_add(v_j_2339_, v___x_2346_);
lean_dec(v_j_2339_);
v_j_2339_ = v___x_2347_;
goto _start;
}
else
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v_j_2339_);
return v___x_2349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3___boxed(lean_object* v___x_2350_, lean_object* v_as_2351_, lean_object* v_j_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2350_, v_as_2351_, v_j_2352_);
lean_dec_ref(v_as_2351_);
lean_dec(v___x_2350_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(lean_object* v_val_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_st_ref_get(v_val_2354_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0___boxed(lean_object* v_val_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v_val_2362_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(lean_object* v_val_2369_, lean_object* v_val_2370_, lean_object* v_a_2371_, lean_object* v___x_2372_, lean_object* v_____r_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2379_ = lean_st_ref_take(v_val_2369_);
v___x_2380_ = l_Lean_Elab_FixedParams_Info_setVarying(v_val_2370_, v_a_2371_, v___x_2379_);
v___x_2381_ = lean_st_ref_put(v_val_2369_, v___x_2380_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2372_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1___boxed(lean_object* v_val_2384_, lean_object* v_val_2385_, lean_object* v_a_2386_, lean_object* v___x_2387_, lean_object* v_____r_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2384_, v_val_2385_, v_a_2386_, v___x_2387_, v_____r_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_val_2385_);
lean_dec(v_val_2384_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(lean_object* v_val_2395_, lean_object* v_val_2396_, lean_object* v_next_2397_, lean_object* v_next_2398_, lean_object* v___x_2399_, lean_object* v___x_2400_, lean_object* v_upperBound_2401_, lean_object* v_params_2402_, lean_object* v___x_2403_, lean_object* v_a_2404_, uint8_t v_b_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
uint8_t v_a_2412_; uint8_t v___x_2416_; 
v___x_2416_ = lean_nat_dec_lt(v_a_2404_, v_upperBound_2401_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec(v_a_2404_);
lean_dec_ref(v___x_2403_);
lean_dec(v_next_2397_);
v___x_2417_ = lean_box(v_b_2405_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
else
{
uint8_t v___x_2419_; lean_object* v___y_2421_; lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2419_ = lean_nat_dec_eq(v___x_2399_, v___x_2400_);
v___x_2435_ = lean_st_ref_get(v_val_2395_);
v___x_2436_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_next_2398_, v_a_2404_, v___x_2435_);
lean_dec(v___x_2435_);
if (v___x_2436_ == 0)
{
v_a_2412_ = v_b_2405_;
goto v___jp_2411_;
}
else
{
lean_object* v___x_2437_; uint8_t v_foApprox_2438_; uint8_t v_ctxApprox_2439_; uint8_t v_quasiPatternApprox_2440_; uint8_t v_constApprox_2441_; uint8_t v_isDefEqStuckEx_2442_; uint8_t v_unificationHints_2443_; uint8_t v_assignSyntheticOpaque_2444_; uint8_t v_offsetCnstrs_2445_; uint8_t v_transparency_2446_; uint8_t v_etaStruct_2447_; uint8_t v_univApprox_2448_; uint8_t v_iota_2449_; uint8_t v_beta_2450_; uint8_t v_proj_2451_; uint8_t v_zeta_2452_; uint8_t v_zetaDelta_2453_; uint8_t v_zetaUnused_2454_; uint8_t v_zetaHave_2455_; uint8_t v_canUnfoldPredicateConfig_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2486_; 
v___x_2437_ = l_Lean_Meta_Context_config(v___y_2406_);
v_foApprox_2438_ = lean_ctor_get_uint8(v___x_2437_, 0);
v_ctxApprox_2439_ = lean_ctor_get_uint8(v___x_2437_, 1);
v_quasiPatternApprox_2440_ = lean_ctor_get_uint8(v___x_2437_, 2);
v_constApprox_2441_ = lean_ctor_get_uint8(v___x_2437_, 3);
v_isDefEqStuckEx_2442_ = lean_ctor_get_uint8(v___x_2437_, 4);
v_unificationHints_2443_ = lean_ctor_get_uint8(v___x_2437_, 5);
v_assignSyntheticOpaque_2444_ = lean_ctor_get_uint8(v___x_2437_, 7);
v_offsetCnstrs_2445_ = lean_ctor_get_uint8(v___x_2437_, 8);
v_transparency_2446_ = lean_ctor_get_uint8(v___x_2437_, 9);
v_etaStruct_2447_ = lean_ctor_get_uint8(v___x_2437_, 10);
v_univApprox_2448_ = lean_ctor_get_uint8(v___x_2437_, 11);
v_iota_2449_ = lean_ctor_get_uint8(v___x_2437_, 12);
v_beta_2450_ = lean_ctor_get_uint8(v___x_2437_, 13);
v_proj_2451_ = lean_ctor_get_uint8(v___x_2437_, 14);
v_zeta_2452_ = lean_ctor_get_uint8(v___x_2437_, 15);
v_zetaDelta_2453_ = lean_ctor_get_uint8(v___x_2437_, 16);
v_zetaUnused_2454_ = lean_ctor_get_uint8(v___x_2437_, 17);
v_zetaHave_2455_ = lean_ctor_get_uint8(v___x_2437_, 18);
v_canUnfoldPredicateConfig_2456_ = lean_ctor_get_uint8(v___x_2437_, 19);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2458_ = v___x_2437_;
v_isShared_2459_ = v_isSharedCheck_2486_;
goto v_resetjp_2457_;
}
else
{
lean_dec(v___x_2437_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2486_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
uint8_t v_trackZetaDelta_2460_; lean_object* v_zetaDeltaSet_2461_; lean_object* v_lctx_2462_; lean_object* v_localInstances_2463_; lean_object* v_defEqCtx_x3f_2464_; lean_object* v_synthPendingDepth_2465_; lean_object* v_customCanUnfoldPredicate_x3f_2466_; uint8_t v_univApprox_2467_; uint8_t v_inTypeClassResolution_2468_; uint8_t v_cacheInferType_2469_; uint8_t v___x_2470_; lean_object* v___x_2472_; 
v_trackZetaDelta_2460_ = lean_ctor_get_uint8(v___y_2406_, sizeof(void*)*7);
v_zetaDeltaSet_2461_ = lean_ctor_get(v___y_2406_, 1);
v_lctx_2462_ = lean_ctor_get(v___y_2406_, 2);
v_localInstances_2463_ = lean_ctor_get(v___y_2406_, 3);
v_defEqCtx_x3f_2464_ = lean_ctor_get(v___y_2406_, 4);
v_synthPendingDepth_2465_ = lean_ctor_get(v___y_2406_, 5);
v_customCanUnfoldPredicate_x3f_2466_ = lean_ctor_get(v___y_2406_, 6);
v_univApprox_2467_ = lean_ctor_get_uint8(v___y_2406_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2468_ = lean_ctor_get_uint8(v___y_2406_, sizeof(void*)*7 + 2);
v_cacheInferType_2469_ = lean_ctor_get_uint8(v___y_2406_, sizeof(void*)*7 + 3);
v___x_2470_ = 0;
if (v_isShared_2459_ == 0)
{
v___x_2472_ = v___x_2458_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 0, v_foApprox_2438_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 1, v_ctxApprox_2439_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 2, v_quasiPatternApprox_2440_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 3, v_constApprox_2441_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 4, v_isDefEqStuckEx_2442_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 5, v_unificationHints_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 7, v_assignSyntheticOpaque_2444_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 8, v_offsetCnstrs_2445_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 9, v_transparency_2446_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 10, v_etaStruct_2447_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 11, v_univApprox_2448_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 12, v_iota_2449_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 13, v_beta_2450_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 14, v_proj_2451_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 15, v_zeta_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 16, v_zetaDelta_2453_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 17, v_zetaUnused_2454_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 18, v_zetaHave_2455_);
lean_ctor_set_uint8(v_reuseFailAlloc_2485_, 19, v_canUnfoldPredicateConfig_2456_);
v___x_2472_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
uint64_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v_transparency_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; uint8_t v___x_2480_; 
lean_ctor_set_uint8(v___x_2472_, 6, v___x_2470_);
v___x_2473_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2472_);
v___x_2474_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set_uint64(v___x_2474_, sizeof(void*)*1, v___x_2473_);
lean_inc(v_customCanUnfoldPredicate_x3f_2466_);
lean_inc(v_synthPendingDepth_2465_);
lean_inc(v_defEqCtx_x3f_2464_);
lean_inc_ref(v_localInstances_2463_);
lean_inc_ref(v_lctx_2462_);
lean_inc(v_zetaDeltaSet_2461_);
lean_inc_ref(v___x_2474_);
v___x_2475_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
lean_ctor_set(v___x_2475_, 1, v_zetaDeltaSet_2461_);
lean_ctor_set(v___x_2475_, 2, v_lctx_2462_);
lean_ctor_set(v___x_2475_, 3, v_localInstances_2463_);
lean_ctor_set(v___x_2475_, 4, v_defEqCtx_x3f_2464_);
lean_ctor_set(v___x_2475_, 5, v_synthPendingDepth_2465_);
lean_ctor_set(v___x_2475_, 6, v_customCanUnfoldPredicate_x3f_2466_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*7, v_trackZetaDelta_2460_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*7 + 1, v_univApprox_2467_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2468_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*7 + 3, v_cacheInferType_2469_);
v___x_2476_ = l_Lean_Meta_Context_config(v___x_2475_);
v_transparency_2477_ = lean_ctor_get_uint8(v___x_2476_, 9);
lean_dec_ref(v___x_2476_);
v___x_2478_ = lean_array_fget_borrowed(v_params_2402_, v_a_2404_);
v___x_2479_ = 2;
v___x_2480_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2477_, v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref_known(v___x_2475_, 7);
v___x_2481_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2479_, v___x_2474_);
lean_inc(v_customCanUnfoldPredicate_x3f_2466_);
lean_inc(v_synthPendingDepth_2465_);
lean_inc(v_defEqCtx_x3f_2464_);
lean_inc_ref(v_localInstances_2463_);
lean_inc_ref(v_lctx_2462_);
lean_inc(v_zetaDeltaSet_2461_);
v___x_2482_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v_zetaDeltaSet_2461_);
lean_ctor_set(v___x_2482_, 2, v_lctx_2462_);
lean_ctor_set(v___x_2482_, 3, v_localInstances_2463_);
lean_ctor_set(v___x_2482_, 4, v_defEqCtx_x3f_2464_);
lean_ctor_set(v___x_2482_, 5, v_synthPendingDepth_2465_);
lean_ctor_set(v___x_2482_, 6, v_customCanUnfoldPredicate_x3f_2466_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*7, v_trackZetaDelta_2460_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*7 + 1, v_univApprox_2467_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2468_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*7 + 3, v_cacheInferType_2469_);
lean_inc_ref(v___x_2403_);
lean_inc(v___x_2478_);
v___x_2483_ = l_Lean_Meta_isExprDefEq(v___x_2478_, v___x_2403_, v___x_2482_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec_ref_known(v___x_2482_, 7);
v___y_2421_ = v___x_2483_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2484_; 
lean_dec_ref_known(v___x_2474_, 1);
lean_inc_ref(v___x_2403_);
lean_inc(v___x_2478_);
v___x_2484_ = l_Lean_Meta_isExprDefEq(v___x_2478_, v___x_2403_, v___x_2475_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec_ref_known(v___x_2475_, 7);
v___y_2421_ = v___x_2484_;
goto v___jp_2420_;
}
}
}
}
v___jp_2420_:
{
if (lean_obj_tag(v___y_2421_) == 0)
{
lean_object* v_a_2422_; uint8_t v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___y_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___y_2421_, 1);
v___x_2423_ = lean_unbox(v_a_2422_);
lean_dec(v_a_2422_);
if (v___x_2423_ == 0)
{
v_a_2412_ = v_b_2405_;
goto v___jp_2411_;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = lean_st_ref_take(v_val_2395_);
lean_inc(v_a_2404_);
lean_inc(v_next_2397_);
v___x_2425_ = l_Lean_Elab_FixedParams_Info_setCallerParam(v_val_2396_, v_next_2397_, v_next_2398_, v_a_2404_, v___x_2424_);
v___x_2426_ = lean_st_ref_put(v_val_2395_, v___x_2425_);
v_a_2412_ = v___x_2419_;
goto v___jp_2411_;
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_a_2404_);
lean_dec_ref(v___x_2403_);
lean_dec(v_next_2397_);
v_a_2427_ = lean_ctor_get(v___y_2421_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___y_2421_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___y_2421_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___y_2421_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
v___jp_2411_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_add(v_a_2404_, v___x_2413_);
lean_dec(v_a_2404_);
v_a_2404_ = v___x_2414_;
v_b_2405_ = v_a_2412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg___boxed(lean_object* v_val_2487_, lean_object* v_val_2488_, lean_object* v_next_2489_, lean_object* v_next_2490_, lean_object* v___x_2491_, lean_object* v___x_2492_, lean_object* v_upperBound_2493_, lean_object* v_params_2494_, lean_object* v___x_2495_, lean_object* v_a_2496_, lean_object* v_b_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v_b_boxed_2503_; lean_object* v_res_2504_; 
v_b_boxed_2503_ = lean_unbox(v_b_2497_);
v_res_2504_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2487_, v_val_2488_, v_next_2489_, v_next_2490_, v___x_2491_, v___x_2492_, v_upperBound_2493_, v_params_2494_, v___x_2495_, v_a_2496_, v_b_boxed_2503_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v_params_2494_);
lean_dec(v_upperBound_2493_);
lean_dec(v___x_2492_);
lean_dec(v___x_2491_);
lean_dec(v_next_2490_);
lean_dec(v_val_2488_);
lean_dec(v_val_2487_);
return v_res_2504_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2516_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__5));
v___x_2517_ = l_Lean_Name_append(v___x_2516_, v___x_2515_);
return v___x_2517_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__7));
v___x_2520_ = l_Lean_stringToMessageData(v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__2));
v___x_2522_ = l_Lean_stringToMessageData(v___x_2521_);
return v___x_2522_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__10));
v___x_2525_ = l_Lean_stringToMessageData(v___x_2524_);
return v___x_2525_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__12));
v___x_2528_ = l_Lean_stringToMessageData(v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__14));
v___x_2531_ = l_Lean_stringToMessageData(v___x_2530_);
return v___x_2531_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__16));
v___x_2534_ = l_Lean_stringToMessageData(v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__18));
v___x_2537_ = l_Lean_stringToMessageData(v___x_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(lean_object* v_val_2538_, lean_object* v_val_2539_, lean_object* v_upperBound_2540_, lean_object* v_args_2541_, lean_object* v_e_2542_, lean_object* v_next_2543_, lean_object* v_params_2544_, lean_object* v___x_2545_, lean_object* v___x_2546_, lean_object* v_a_2547_, lean_object* v_b_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_a_2555_; lean_object* v___y_2560_; uint8_t v___x_2579_; 
v___x_2579_ = lean_nat_dec_lt(v_a_2547_, v_upperBound_2540_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; 
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_b_2548_);
return v___x_2580_;
}
else
{
lean_object* v___x_2581_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2581_ = lean_box(0);
v___x_2588_ = l_Lean_instInhabitedExpr;
v___x_2589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2538_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; uint8_t v___x_2591_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___x_2591_ = l_Lean_Elab_FixedParams_Info_mayBeFixed(v_val_2539_, v_a_2547_, v_a_2590_);
lean_dec(v_a_2590_);
if (v___x_2591_ == 0)
{
v_a_2555_ = v___x_2581_;
goto v___jp_2554_;
}
else
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = lean_array_get_size(v_args_2541_);
v___x_2593_ = lean_nat_dec_lt(v_a_2547_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v_toCold_2594_; lean_object* v_options_2595_; uint8_t v_hasTrace_2596_; 
v_toCold_2594_ = lean_ctor_get(v___y_2551_, 0);
v_options_2595_ = lean_ctor_get(v_toCold_2594_, 2);
v_hasTrace_2596_ = lean_ctor_get_uint8(v_options_2595_, sizeof(void*)*1);
if (v_hasTrace_2596_ == 0)
{
goto v___jp_2584_;
}
else
{
lean_object* v_inheritedTraceOptions_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v_inheritedTraceOptions_2597_ = lean_ctor_get(v_toCold_2594_, 11);
v___x_2598_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2599_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2597_, v_options_2595_, v___x_2599_);
if (v___x_2600_ == 0)
{
goto v___jp_2584_;
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2601_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2539_);
v___x_2602_ = l_Nat_reprFast(v_val_2539_);
v___x_2603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
v___x_2604_ = l_Lean_MessageData_ofFormat(v___x_2603_);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2601_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_inc(v_a_2547_);
v___x_2608_ = l_Nat_reprFast(v_a_2547_);
v___x_2609_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
v___x_2610_ = l_Lean_MessageData_ofFormat(v___x_2609_);
lean_inc_ref(v___x_2610_);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2607_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
lean_inc_ref(v_e_2542_);
v___x_2614_ = l_Lean_MessageData_ofExpr(v_e_2542_);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__13);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v___x_2610_);
v___x_2619_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2598_, v___x_2618_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2621_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
lean_inc(v_a_2547_);
v___x_2621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2538_, v_val_2539_, v_a_2547_, v___x_2581_, v_a_2620_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
v___y_2560_ = v___x_2621_;
goto v___jp_2559_;
}
else
{
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
return v___x_2619_;
}
}
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = lean_array_fget_borrowed(v_args_2541_, v_a_2547_);
v___x_2623_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__0(v_val_2538_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2625_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
v___x_2625_ = l_Lean_Elab_FixedParams_Info_getCallerParam_x3f(v_val_2539_, v_a_2547_, v_next_2543_, v_a_2624_);
lean_dec(v_a_2624_);
if (lean_obj_tag(v___x_2625_) == 1)
{
lean_object* v_val_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2727_; 
v_val_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2727_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_val_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2727_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; uint8_t v_foApprox_2631_; uint8_t v_ctxApprox_2632_; uint8_t v_quasiPatternApprox_2633_; uint8_t v_constApprox_2634_; uint8_t v_isDefEqStuckEx_2635_; uint8_t v_unificationHints_2636_; uint8_t v_assignSyntheticOpaque_2637_; uint8_t v_offsetCnstrs_2638_; uint8_t v_transparency_2639_; uint8_t v_etaStruct_2640_; uint8_t v_univApprox_2641_; uint8_t v_iota_2642_; uint8_t v_beta_2643_; uint8_t v_proj_2644_; uint8_t v_zeta_2645_; uint8_t v_zetaDelta_2646_; uint8_t v_zetaUnused_2647_; uint8_t v_zetaHave_2648_; uint8_t v_canUnfoldPredicateConfig_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2726_; 
v___x_2630_ = l_Lean_Meta_Context_config(v___y_2549_);
v_foApprox_2631_ = lean_ctor_get_uint8(v___x_2630_, 0);
v_ctxApprox_2632_ = lean_ctor_get_uint8(v___x_2630_, 1);
v_quasiPatternApprox_2633_ = lean_ctor_get_uint8(v___x_2630_, 2);
v_constApprox_2634_ = lean_ctor_get_uint8(v___x_2630_, 3);
v_isDefEqStuckEx_2635_ = lean_ctor_get_uint8(v___x_2630_, 4);
v_unificationHints_2636_ = lean_ctor_get_uint8(v___x_2630_, 5);
v_assignSyntheticOpaque_2637_ = lean_ctor_get_uint8(v___x_2630_, 7);
v_offsetCnstrs_2638_ = lean_ctor_get_uint8(v___x_2630_, 8);
v_transparency_2639_ = lean_ctor_get_uint8(v___x_2630_, 9);
v_etaStruct_2640_ = lean_ctor_get_uint8(v___x_2630_, 10);
v_univApprox_2641_ = lean_ctor_get_uint8(v___x_2630_, 11);
v_iota_2642_ = lean_ctor_get_uint8(v___x_2630_, 12);
v_beta_2643_ = lean_ctor_get_uint8(v___x_2630_, 13);
v_proj_2644_ = lean_ctor_get_uint8(v___x_2630_, 14);
v_zeta_2645_ = lean_ctor_get_uint8(v___x_2630_, 15);
v_zetaDelta_2646_ = lean_ctor_get_uint8(v___x_2630_, 16);
v_zetaUnused_2647_ = lean_ctor_get_uint8(v___x_2630_, 17);
v_zetaHave_2648_ = lean_ctor_get_uint8(v___x_2630_, 18);
v_canUnfoldPredicateConfig_2649_ = lean_ctor_get_uint8(v___x_2630_, 19);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2651_ = v___x_2630_;
v_isShared_2652_ = v_isSharedCheck_2726_;
goto v_resetjp_2650_;
}
else
{
lean_dec(v___x_2630_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2726_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
uint8_t v_trackZetaDelta_2653_; lean_object* v_zetaDeltaSet_2654_; lean_object* v_lctx_2655_; lean_object* v_localInstances_2656_; lean_object* v_defEqCtx_x3f_2657_; lean_object* v_synthPendingDepth_2658_; lean_object* v_customCanUnfoldPredicate_x3f_2659_; uint8_t v_univApprox_2660_; uint8_t v_inTypeClassResolution_2661_; uint8_t v_cacheInferType_2662_; uint8_t v___x_2663_; lean_object* v___x_2665_; 
v_trackZetaDelta_2653_ = lean_ctor_get_uint8(v___y_2549_, sizeof(void*)*7);
v_zetaDeltaSet_2654_ = lean_ctor_get(v___y_2549_, 1);
v_lctx_2655_ = lean_ctor_get(v___y_2549_, 2);
v_localInstances_2656_ = lean_ctor_get(v___y_2549_, 3);
v_defEqCtx_x3f_2657_ = lean_ctor_get(v___y_2549_, 4);
v_synthPendingDepth_2658_ = lean_ctor_get(v___y_2549_, 5);
v_customCanUnfoldPredicate_x3f_2659_ = lean_ctor_get(v___y_2549_, 6);
v_univApprox_2660_ = lean_ctor_get_uint8(v___y_2549_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2661_ = lean_ctor_get_uint8(v___y_2549_, sizeof(void*)*7 + 2);
v_cacheInferType_2662_ = lean_ctor_get_uint8(v___y_2549_, sizeof(void*)*7 + 3);
v___x_2663_ = 0;
if (v_isShared_2652_ == 0)
{
v___x_2665_ = v___x_2651_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 0, v_foApprox_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 1, v_ctxApprox_2632_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 2, v_quasiPatternApprox_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 3, v_constApprox_2634_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 4, v_isDefEqStuckEx_2635_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 5, v_unificationHints_2636_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 7, v_assignSyntheticOpaque_2637_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 8, v_offsetCnstrs_2638_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 9, v_transparency_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 10, v_etaStruct_2640_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 11, v_univApprox_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 12, v_iota_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 13, v_beta_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 14, v_proj_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 15, v_zeta_2645_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 16, v_zetaDelta_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 17, v_zetaUnused_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 18, v_zetaHave_2648_);
lean_ctor_set_uint8(v_reuseFailAlloc_2725_, 19, v_canUnfoldPredicateConfig_2649_);
v___x_2665_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
uint64_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v_transparency_2670_; lean_object* v___x_2671_; lean_object* v___y_2673_; uint8_t v___x_2719_; uint8_t v___x_2720_; 
lean_ctor_set_uint8(v___x_2665_, 6, v___x_2663_);
v___x_2666_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2667_, 0, v___x_2665_);
lean_ctor_set_uint64(v___x_2667_, sizeof(void*)*1, v___x_2666_);
lean_inc(v_customCanUnfoldPredicate_x3f_2659_);
lean_inc(v_synthPendingDepth_2658_);
lean_inc(v_defEqCtx_x3f_2657_);
lean_inc_ref(v_localInstances_2656_);
lean_inc_ref(v_lctx_2655_);
lean_inc(v_zetaDeltaSet_2654_);
lean_inc_ref(v___x_2667_);
v___x_2668_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
lean_ctor_set(v___x_2668_, 1, v_zetaDeltaSet_2654_);
lean_ctor_set(v___x_2668_, 2, v_lctx_2655_);
lean_ctor_set(v___x_2668_, 3, v_localInstances_2656_);
lean_ctor_set(v___x_2668_, 4, v_defEqCtx_x3f_2657_);
lean_ctor_set(v___x_2668_, 5, v_synthPendingDepth_2658_);
lean_ctor_set(v___x_2668_, 6, v_customCanUnfoldPredicate_x3f_2659_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*7, v_trackZetaDelta_2653_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*7 + 1, v_univApprox_2660_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2661_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*7 + 3, v_cacheInferType_2662_);
v___x_2669_ = l_Lean_Meta_Context_config(v___x_2668_);
v_transparency_2670_ = lean_ctor_get_uint8(v___x_2669_, 9);
lean_dec_ref(v___x_2669_);
v___x_2671_ = lean_array_get_borrowed(v___x_2588_, v_params_2544_, v_val_2626_);
lean_dec(v_val_2626_);
v___x_2719_ = 2;
v___x_2720_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2670_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec_ref_known(v___x_2668_, 7);
v___x_2721_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2719_, v___x_2667_);
lean_inc(v_customCanUnfoldPredicate_x3f_2659_);
lean_inc(v_synthPendingDepth_2658_);
lean_inc(v_defEqCtx_x3f_2657_);
lean_inc_ref(v_localInstances_2656_);
lean_inc_ref(v_lctx_2655_);
lean_inc(v_zetaDeltaSet_2654_);
v___x_2722_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_zetaDeltaSet_2654_);
lean_ctor_set(v___x_2722_, 2, v_lctx_2655_);
lean_ctor_set(v___x_2722_, 3, v_localInstances_2656_);
lean_ctor_set(v___x_2722_, 4, v_defEqCtx_x3f_2657_);
lean_ctor_set(v___x_2722_, 5, v_synthPendingDepth_2658_);
lean_ctor_set(v___x_2722_, 6, v_customCanUnfoldPredicate_x3f_2659_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7, v_trackZetaDelta_2653_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 1, v_univApprox_2660_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2661_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*7 + 3, v_cacheInferType_2662_);
lean_inc(v___x_2622_);
lean_inc(v___x_2671_);
v___x_2723_ = l_Lean_Meta_isExprDefEq(v___x_2671_, v___x_2622_, v___x_2722_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec_ref_known(v___x_2722_, 7);
v___y_2673_ = v___x_2723_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2724_; 
lean_dec_ref_known(v___x_2667_, 1);
lean_inc(v___x_2622_);
lean_inc(v___x_2671_);
v___x_2724_ = l_Lean_Meta_isExprDefEq(v___x_2671_, v___x_2622_, v___x_2668_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec_ref_known(v___x_2668_, 7);
v___y_2673_ = v___x_2724_;
goto v___jp_2672_;
}
v___jp_2672_:
{
if (lean_obj_tag(v___y_2673_) == 0)
{
lean_object* v_a_2674_; uint8_t v___x_2675_; 
v_a_2674_ = lean_ctor_get(v___y_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___y_2673_, 1);
v___x_2675_ = lean_unbox(v_a_2674_);
lean_dec(v_a_2674_);
if (v___x_2675_ == 0)
{
lean_object* v_toCold_2676_; lean_object* v_options_2677_; uint8_t v_hasTrace_2678_; 
v_toCold_2676_ = lean_ctor_get(v___y_2551_, 0);
v_options_2677_ = lean_ctor_get(v_toCold_2676_, 2);
v_hasTrace_2678_ = lean_ctor_get_uint8(v_options_2677_, sizeof(void*)*1);
if (v_hasTrace_2678_ == 0)
{
lean_del_object(v___x_2628_);
goto v___jp_2586_;
}
else
{
lean_object* v_inheritedTraceOptions_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v_inheritedTraceOptions_2679_ = lean_ctor_get(v_toCold_2676_, 11);
v___x_2680_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2681_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2679_, v_options_2677_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_del_object(v___x_2628_);
goto v___jp_2586_;
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
v___x_2683_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2539_);
v___x_2684_ = l_Nat_reprFast(v_val_2539_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 3);
lean_ctor_set(v___x_2628_, 0, v___x_2684_);
v___x_2686_ = v___x_2628_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2687_ = l_Lean_MessageData_ofFormat(v___x_2686_);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2683_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
lean_inc(v_a_2547_);
v___x_2691_ = l_Nat_reprFast(v_a_2547_);
v___x_2692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
v___x_2693_ = l_Lean_MessageData_ofFormat(v___x_2692_);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2690_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
lean_inc_ref(v_e_2542_);
v___x_2697_ = l_Lean_MessageData_ofExpr(v_e_2542_);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
lean_inc(v___x_2671_);
v___x_2701_ = l_Lean_MessageData_ofExpr(v___x_2671_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__17);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
lean_inc(v___x_2622_);
v___x_2705_ = l_Lean_MessageData_ofExpr(v___x_2622_);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2680_, v___x_2706_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2709_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
lean_inc(v_a_2547_);
v___x_2709_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2538_, v_val_2539_, v_a_2547_, v___x_2581_, v_a_2708_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
v___y_2560_ = v___x_2709_;
goto v___jp_2559_;
}
else
{
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
return v___x_2707_;
}
}
}
}
}
else
{
lean_del_object(v___x_2628_);
v_a_2555_ = v___x_2581_;
goto v___jp_2554_;
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_del_object(v___x_2628_);
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
v_a_2711_ = lean_ctor_get(v___y_2673_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___y_2673_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___y_2673_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___y_2673_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
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
lean_object* v___x_2728_; uint8_t v___x_2729_; lean_object* v___x_2730_; 
lean_dec(v___x_2625_);
v___x_2728_ = lean_unsigned_to_nat(0u);
v___x_2729_ = 0;
lean_inc(v___x_2622_);
lean_inc(v_a_2547_);
v___x_2730_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_2538_, v_val_2539_, v_a_2547_, v_next_2543_, v___x_2545_, v___x_2546_, v___x_2545_, v_params_2544_, v___x_2622_, v___x_2728_, v___x_2729_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; uint8_t v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v___x_2732_ = lean_unbox(v_a_2731_);
lean_dec(v_a_2731_);
if (v___x_2732_ == 0)
{
lean_object* v_toCold_2733_; lean_object* v_options_2734_; uint8_t v_hasTrace_2735_; 
v_toCold_2733_ = lean_ctor_get(v___y_2551_, 0);
v_options_2734_ = lean_ctor_get(v_toCold_2733_, 2);
v_hasTrace_2735_ = lean_ctor_get_uint8(v_options_2734_, sizeof(void*)*1);
if (v_hasTrace_2735_ == 0)
{
goto v___jp_2582_;
}
else
{
lean_object* v_inheritedTraceOptions_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_inheritedTraceOptions_2736_ = lean_ctor_get(v_toCold_2733_, 11);
v___x_2737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_2738_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_2739_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2736_, v_options_2734_, v___x_2738_);
if (v___x_2739_ == 0)
{
goto v___jp_2582_;
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2740_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__8);
lean_inc(v_val_2539_);
v___x_2741_ = l_Nat_reprFast(v_val_2539_);
v___x_2742_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
v___x_2743_ = l_Lean_MessageData_ofFormat(v___x_2742_);
v___x_2744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2740_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__9);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
lean_inc(v_a_2547_);
v___x_2747_ = l_Nat_reprFast(v_a_2547_);
v___x_2748_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
v___x_2749_ = l_Lean_MessageData_ofFormat(v___x_2748_);
v___x_2750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2746_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__11);
v___x_2752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2750_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
lean_inc_ref(v_e_2542_);
v___x_2753_ = l_Lean_MessageData_ofExpr(v_e_2542_);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__15);
v___x_2756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
lean_inc(v___x_2622_);
v___x_2757_ = l_Lean_MessageData_ofExpr(v___x_2622_);
v___x_2758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__19);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_2737_, v___x_2760_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
lean_inc(v_a_2547_);
v___x_2763_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2538_, v_val_2539_, v_a_2547_, v___x_2581_, v_a_2762_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
v___y_2560_ = v___x_2763_;
goto v___jp_2559_;
}
else
{
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
return v___x_2761_;
}
}
}
}
else
{
v_a_2555_ = v___x_2581_;
goto v___jp_2554_;
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
v_a_2764_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2730_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2730_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
v_a_2772_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2623_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2623_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
v_a_2780_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2589_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2589_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
v___jp_2582_:
{
lean_object* v___x_2583_; 
lean_inc(v_a_2547_);
v___x_2583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2538_, v_val_2539_, v_a_2547_, v___x_2581_, v___x_2581_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
v___y_2560_ = v___x_2583_;
goto v___jp_2559_;
}
v___jp_2584_:
{
lean_object* v___x_2585_; 
lean_inc(v_a_2547_);
v___x_2585_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2538_, v_val_2539_, v_a_2547_, v___x_2581_, v___x_2581_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
v___y_2560_ = v___x_2585_;
goto v___jp_2559_;
}
v___jp_2586_:
{
lean_object* v___x_2587_; 
lean_inc(v_a_2547_);
v___x_2587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___lam__1(v_val_2538_, v_val_2539_, v_a_2547_, v___x_2581_, v___x_2581_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
v___y_2560_ = v___x_2587_;
goto v___jp_2559_;
}
}
v___jp_2554_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_unsigned_to_nat(1u);
v___x_2557_ = lean_nat_add(v_a_2547_, v___x_2556_);
lean_dec(v_a_2547_);
v_a_2547_ = v___x_2557_;
v_b_2548_ = v_a_2555_;
goto _start;
}
v___jp_2559_:
{
if (lean_obj_tag(v___y_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2570_; 
v_a_2561_ = lean_ctor_get(v___y_2560_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___y_2560_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2563_ = v___y_2560_;
v_isShared_2564_ = v_isSharedCheck_2570_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___y_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2570_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
if (lean_obj_tag(v_a_2561_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; 
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
v_a_2565_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v_a_2561_, 1);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v_a_2565_);
v___x_2567_ = v___x_2563_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2565_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
else
{
lean_object* v_a_2569_; 
lean_del_object(v___x_2563_);
v_a_2569_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v_a_2561_, 1);
v_a_2555_ = v_a_2569_;
goto v___jp_2554_;
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_a_2547_);
lean_dec_ref(v_e_2542_);
lean_dec(v_val_2539_);
v_a_2571_ = lean_ctor_get(v___y_2560_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___y_2560_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___y_2560_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___y_2560_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___boxed(lean_object* v_val_2788_, lean_object* v_val_2789_, lean_object* v_upperBound_2790_, lean_object* v_args_2791_, lean_object* v_e_2792_, lean_object* v_next_2793_, lean_object* v_params_2794_, lean_object* v___x_2795_, lean_object* v___x_2796_, lean_object* v_a_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2788_, v_val_2789_, v_upperBound_2790_, v_args_2791_, v_e_2792_, v_next_2793_, v_params_2794_, v___x_2795_, v___x_2796_, v_a_2797_, v_b_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___x_2796_);
lean_dec(v___x_2795_);
lean_dec_ref(v_params_2794_);
lean_dec(v_next_2793_);
lean_dec_ref(v_args_2791_);
lean_dec(v_upperBound_2790_);
lean_dec(v_val_2788_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(lean_object* v_preDefs_2807_, lean_object* v___x_2808_, lean_object* v_val_2809_, lean_object* v_e_2810_, lean_object* v_next_2811_, lean_object* v_params_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
if (lean_obj_tag(v_x_2815_) == 5)
{
lean_object* v_fn_2823_; lean_object* v_arg_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_fn_2823_ = lean_ctor_get(v_x_2815_, 0);
lean_inc_ref(v_fn_2823_);
v_arg_2824_ = lean_ctor_get(v_x_2815_, 1);
lean_inc_ref(v_arg_2824_);
lean_dec_ref_known(v_x_2815_, 2);
v___x_2825_ = lean_array_set(v_x_2816_, v_x_2817_, v_arg_2824_);
v___x_2826_ = lean_unsigned_to_nat(1u);
v___x_2827_ = lean_nat_sub(v_x_2817_, v___x_2826_);
lean_dec(v_x_2817_);
v_x_2815_ = v_fn_2823_;
v_x_2816_ = v___x_2825_;
v_x_2817_ = v___x_2827_;
goto _start;
}
else
{
uint8_t v___x_2829_; 
lean_dec(v_x_2817_);
v___x_2829_ = l_Lean_Expr_isConst(v_x_2815_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_dec_ref(v_x_2816_);
lean_dec_ref(v_x_2815_);
lean_dec_ref(v_e_2810_);
v___x_2830_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
return v___x_2831_;
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2832_ = l_Lean_Expr_constName_x21(v_x_2815_);
lean_dec_ref(v_x_2815_);
v___x_2833_ = lean_unsigned_to_nat(0u);
v___x_2834_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_getFixedParamsInfo_spec__3(v___x_2832_, v_preDefs_2807_, v___x_2833_);
lean_dec(v___x_2832_);
if (lean_obj_tag(v___x_2834_) == 1)
{
lean_object* v_val_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_val_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_val_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_array_get_borrowed(v___x_2833_, v___x_2808_, v_val_2835_);
v___x_2838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_2809_, v_val_2835_, v___x_2837_, v_x_2816_, v_e_2810_, v_next_2811_, v_params_2812_, v___x_2813_, v___x_2814_, v___x_2833_, v___x_2836_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec_ref(v_x_2816_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2846_; 
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2838_, 0);
lean_dec(v_unused_2847_);
v___x_2840_ = v___x_2838_;
v_isShared_2841_ = v_isSharedCheck_2846_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v___x_2838_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2846_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2842_);
v___x_2844_ = v___x_2840_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
v_a_2848_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2838_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2838_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_dec(v___x_2834_);
lean_dec_ref(v_x_2816_);
lean_dec_ref(v_e_2810_);
v___x_2856_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___closed__0));
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
return v___x_2857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6___boxed(lean_object* v_preDefs_2858_, lean_object* v___x_2859_, lean_object* v_val_2860_, lean_object* v_e_2861_, lean_object* v_next_2862_, lean_object* v_params_2863_, lean_object* v___x_2864_, lean_object* v___x_2865_, lean_object* v_x_2866_, lean_object* v_x_2867_, lean_object* v_x_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2858_, v___x_2859_, v_val_2860_, v_e_2861_, v_next_2862_, v_params_2863_, v___x_2864_, v___x_2865_, v_x_2866_, v_x_2867_, v_x_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___x_2865_);
lean_dec(v___x_2864_);
lean_dec_ref(v_params_2863_);
lean_dec(v_next_2862_);
lean_dec(v_val_2860_);
lean_dec_ref(v___x_2859_);
lean_dec_ref(v_preDefs_2858_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(lean_object* v_preDefs_2875_, lean_object* v___x_2876_, lean_object* v_val_2877_, lean_object* v_a_2878_, lean_object* v_params_2879_, lean_object* v___x_2880_, lean_object* v___x_2881_, lean_object* v_e_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_dummy_2888_; lean_object* v_nargs_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_dummy_2888_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9___lam__1___closed__1);
v_nargs_2889_ = l_Lean_Expr_getAppNumArgs(v_e_2882_);
lean_inc(v_nargs_2889_);
v___x_2890_ = lean_mk_array(v_nargs_2889_, v_dummy_2888_);
v___x_2891_ = lean_unsigned_to_nat(1u);
v___x_2892_ = lean_nat_sub(v_nargs_2889_, v___x_2891_);
lean_dec(v_nargs_2889_);
lean_inc_ref(v_e_2882_);
v___x_2893_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_getFixedParamsInfo_spec__6(v_preDefs_2875_, v___x_2876_, v_val_2877_, v_e_2882_, v_a_2878_, v_params_2879_, v___x_2880_, v___x_2881_, v_e_2882_, v___x_2890_, v___x_2892_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed(lean_object* v_preDefs_2894_, lean_object* v___x_2895_, lean_object* v_val_2896_, lean_object* v_a_2897_, lean_object* v_params_2898_, lean_object* v___x_2899_, lean_object* v___x_2900_, lean_object* v_e_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1(v_preDefs_2894_, v___x_2895_, v_val_2896_, v_a_2897_, v_params_2898_, v___x_2899_, v___x_2900_, v_e_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___x_2900_);
lean_dec(v___x_2899_);
lean_dec_ref(v_params_2898_);
lean_dec(v_a_2897_);
lean_dec(v_val_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v_preDefs_2894_);
return v_res_2907_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2911_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__2));
v___x_2912_ = lean_unsigned_to_nat(6u);
v___x_2913_ = lean_unsigned_to_nat(201u);
v___x_2914_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__1));
v___x_2915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_2916_ = l_mkPanicMessageWithDecl(v___x_2915_, v___x_2914_, v___x_2913_, v___x_2912_, v___x_2911_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(lean_object* v___x_2917_, lean_object* v___x_2918_, lean_object* v_a_2919_, lean_object* v_preDefs_2920_, lean_object* v_val_2921_, lean_object* v___f_2922_, lean_object* v___x_2923_, lean_object* v_params_2924_, lean_object* v_body_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2931_ = lean_array_get_size(v_params_2924_);
v___x_2932_ = lean_array_get(v___x_2917_, v___x_2918_, v_a_2919_);
v___x_2933_ = lean_nat_dec_eq(v___x_2931_, v___x_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_dec(v___x_2932_);
lean_dec_ref(v_body_2925_);
lean_dec_ref(v_params_2924_);
lean_dec_ref(v___f_2922_);
lean_dec(v_val_2921_);
lean_dec_ref(v_preDefs_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2918_);
v___x_2934_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__3);
v___x_2935_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_2934_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2935_;
}
else
{
lean_object* v___f_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; 
v___f_2936_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__1___boxed), 13, 7);
lean_closure_set(v___f_2936_, 0, v_preDefs_2920_);
lean_closure_set(v___f_2936_, 1, v___x_2918_);
lean_closure_set(v___f_2936_, 2, v_val_2921_);
lean_closure_set(v___f_2936_, 3, v_a_2919_);
lean_closure_set(v___f_2936_, 4, v_params_2924_);
lean_closure_set(v___f_2936_, 5, v___x_2931_);
lean_closure_set(v___f_2936_, 6, v___x_2932_);
v___x_2937_ = 0;
v___x_2938_ = l_Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8(v_body_2925_, v___f_2936_, v___f_2922_, v___x_2937_, v___x_2933_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; 
v_unused_2946_ = lean_ctor_get(v___x_2938_, 0);
lean_dec(v_unused_2946_);
v___x_2940_ = v___x_2938_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_dec(v___x_2938_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2923_);
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2923_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
v_a_2947_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2938_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2938_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed(lean_object* v___x_2955_, lean_object* v___x_2956_, lean_object* v_a_2957_, lean_object* v_preDefs_2958_, lean_object* v_val_2959_, lean_object* v___f_2960_, lean_object* v___x_2961_, lean_object* v_params_2962_, lean_object* v_body_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2(v___x_2955_, v___x_2956_, v_a_2957_, v_preDefs_2958_, v_val_2959_, v___f_2960_, v___x_2961_, v_params_2962_, v_body_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___x_2955_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(lean_object* v_e_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_e_2970_);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0___boxed(lean_object* v_e_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__0(v_e_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(lean_object* v___x_2986_, lean_object* v_preDefs_2987_, lean_object* v_val_2988_, lean_object* v_upperBound_2989_, lean_object* v_a_2990_, lean_object* v_b_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
uint8_t v___x_2997_; 
v___x_2997_ = lean_nat_dec_lt(v_a_2990_, v_upperBound_2989_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; 
lean_dec(v_a_2990_);
lean_dec(v_val_2988_);
lean_dec_ref(v_preDefs_2987_);
lean_dec_ref(v___x_2986_);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_b_2991_);
return v___x_2998_;
}
else
{
lean_object* v___x_2999_; lean_object* v_value_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___f_3004_; uint8_t v___x_3005_; lean_object* v___x_3006_; 
v___x_2999_ = lean_array_fget_borrowed(v_preDefs_2987_, v_a_2990_);
v_value_3000_ = lean_ctor_get(v___x_2999_, 7);
v___f_3001_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___closed__0));
v___x_3002_ = lean_unsigned_to_nat(0u);
v___x_3003_ = lean_box(0);
lean_inc(v_val_2988_);
lean_inc_ref(v_preDefs_2987_);
lean_inc(v_a_2990_);
lean_inc_ref(v___x_2986_);
v___f_3004_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_3004_, 0, v___x_3002_);
lean_closure_set(v___f_3004_, 1, v___x_2986_);
lean_closure_set(v___f_3004_, 2, v_a_2990_);
lean_closure_set(v___f_3004_, 3, v_preDefs_2987_);
lean_closure_set(v___f_3004_, 4, v_val_2988_);
lean_closure_set(v___f_3004_, 5, v___f_3001_);
lean_closure_set(v___f_3004_, 6, v___x_3003_);
v___x_3005_ = 0;
lean_inc_ref(v_value_3000_);
v___x_3006_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_3000_, v___f_3004_, v___x_3005_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec_ref_known(v___x_3006_, 1);
v___x_3007_ = lean_unsigned_to_nat(1u);
v___x_3008_ = lean_nat_add(v_a_2990_, v___x_3007_);
lean_dec(v_a_2990_);
v_a_2990_ = v___x_3008_;
v_b_2991_ = v___x_3003_;
goto _start;
}
else
{
lean_dec(v_a_2990_);
lean_dec(v_val_2988_);
lean_dec_ref(v_preDefs_2987_);
lean_dec_ref(v___x_2986_);
return v___x_3006_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___boxed(lean_object* v___x_3010_, lean_object* v_preDefs_3011_, lean_object* v_val_3012_, lean_object* v_upperBound_3013_, lean_object* v_a_3014_, lean_object* v_b_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3010_, v_preDefs_3011_, v_val_3012_, v_upperBound_3013_, v_a_3014_, v_b_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v_upperBound_3013_);
return v_res_3021_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamsInfo___closed__1(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l_Lean_Elab_getFixedParamsInfo___closed__0));
v___x_3024_ = l_Lean_stringToMessageData(v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo(lean_object* v_preDefs_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
size_t v_sz_3031_; size_t v___x_3032_; lean_object* v___x_3033_; 
v_sz_3031_ = lean_array_size(v_preDefs_3025_);
v___x_3032_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3025_);
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__0(v_sz_3031_, v___x_3032_, v_preDefs_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; size_t v_sz_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc_n(v_a_3034_, 2);
lean_dec_ref_known(v___x_3033_, 1);
v_sz_3035_ = lean_array_size(v_a_3034_);
v___x_3036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_getFixedParamsInfo_spec__1(v_sz_3035_, v___x_3032_, v_a_3034_);
v___x_3037_ = l_Lean_Elab_FixedParams_Info_init(v_a_3034_);
v___x_3038_ = lean_st_mk_ref(v___x_3037_);
v___x_3039_ = lean_st_ref_take(v___x_3038_);
v___x_3040_ = l_Lean_Elab_FixedParams_Info_addSelfCalls(v___x_3039_);
v___x_3041_ = lean_st_ref_put(v___x_3038_, v___x_3040_);
v___x_3042_ = lean_array_get_size(v_preDefs_3025_);
v___x_3043_ = lean_unsigned_to_nat(0u);
v___x_3044_ = lean_box(0);
lean_inc(v___x_3038_);
v___x_3045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3036_, v_preDefs_3025_, v___x_3038_, v___x_3042_, v___x_3043_, v___x_3044_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3085_; 
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; 
v_unused_3086_ = lean_ctor_get(v___x_3045_, 0);
lean_dec(v_unused_3086_);
v___x_3047_ = v___x_3045_;
v_isShared_3048_ = v_isSharedCheck_3085_;
goto v_resetjp_3046_;
}
else
{
lean_dec(v___x_3045_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3085_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v_toCold_3050_; lean_object* v_options_3051_; uint8_t v_hasTrace_3052_; 
v___x_3049_ = lean_st_ref_get(v___x_3038_);
lean_dec(v___x_3038_);
v_toCold_3050_ = lean_ctor_get(v_a_3028_, 0);
v_options_3051_ = lean_ctor_get(v_toCold_3050_, 2);
v_hasTrace_3052_ = lean_ctor_get_uint8(v_options_3051_, sizeof(void*)*1);
if (v_hasTrace_3052_ == 0)
{
lean_object* v___x_3054_; 
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3049_);
v___x_3054_ = v___x_3047_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
v_inheritedTraceOptions_3056_ = lean_ctor_get(v_toCold_3050_, 11);
v___x_3057_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__3));
v___x_3058_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg___closed__6);
v___x_3059_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3056_, v_options_3051_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3061_; 
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3049_);
v___x_3061_ = v___x_3047_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3049_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_del_object(v___x_3047_);
v___x_3063_ = lean_obj_once(&l_Lean_Elab_getFixedParamsInfo___closed__1, &l_Lean_Elab_getFixedParamsInfo___closed__1_once, _init_l_Lean_Elab_getFixedParamsInfo___closed__1);
lean_inc(v___x_3049_);
v___x_3064_ = l_Lean_Elab_FixedParams_Info_format(v___x_3049_);
v___x_3065_ = l_Std_Format_indentD(v___x_3064_);
v___x_3066_ = l_Lean_MessageData_ofFormat(v___x_3065_);
v___x_3067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3063_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_Lean_addTrace___at___00Lean_Elab_getFixedParamsInfo_spec__2(v___x_3057_, v___x_3067_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v___x_3068_, 0);
lean_dec(v_unused_3076_);
v___x_3070_ = v___x_3068_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_dec(v___x_3068_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v___x_3049_);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3049_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v___x_3049_);
v_a_3077_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3068_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3068_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v___x_3038_);
v_a_3087_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3045_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3045_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v_preDefs_3025_);
v_a_3095_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3033_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3033_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamsInfo___boxed(lean_object* v_preDefs_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(lean_object* v_val_3110_, lean_object* v_val_3111_, lean_object* v_next_3112_, lean_object* v_next_3113_, lean_object* v___x_3114_, lean_object* v___x_3115_, lean_object* v_upperBound_3116_, lean_object* v_params_3117_, lean_object* v___x_3118_, lean_object* v_inst_3119_, lean_object* v_R_3120_, lean_object* v_a_3121_, uint8_t v_b_3122_, lean_object* v_c_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___redArg(v_val_3110_, v_val_3111_, v_next_3112_, v_next_3113_, v___x_3114_, v___x_3115_, v_upperBound_3116_, v_params_3117_, v___x_3118_, v_a_3121_, v_b_3122_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4___boxed(lean_object** _args){
lean_object* v_val_3130_ = _args[0];
lean_object* v_val_3131_ = _args[1];
lean_object* v_next_3132_ = _args[2];
lean_object* v_next_3133_ = _args[3];
lean_object* v___x_3134_ = _args[4];
lean_object* v___x_3135_ = _args[5];
lean_object* v_upperBound_3136_ = _args[6];
lean_object* v_params_3137_ = _args[7];
lean_object* v___x_3138_ = _args[8];
lean_object* v_inst_3139_ = _args[9];
lean_object* v_R_3140_ = _args[10];
lean_object* v_a_3141_ = _args[11];
lean_object* v_b_3142_ = _args[12];
lean_object* v_c_3143_ = _args[13];
lean_object* v___y_3144_ = _args[14];
lean_object* v___y_3145_ = _args[15];
lean_object* v___y_3146_ = _args[16];
lean_object* v___y_3147_ = _args[17];
lean_object* v___y_3148_ = _args[18];
_start:
{
uint8_t v_b_boxed_3149_; lean_object* v_res_3150_; 
v_b_boxed_3149_ = lean_unbox(v_b_3142_);
v_res_3150_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__4(v_val_3130_, v_val_3131_, v_next_3132_, v_next_3133_, v___x_3134_, v___x_3135_, v_upperBound_3136_, v_params_3137_, v___x_3138_, v_inst_3139_, v_R_3140_, v_a_3141_, v_b_boxed_3149_, v_c_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec_ref(v_params_3137_);
lean_dec(v_upperBound_3136_);
lean_dec(v___x_3135_);
lean_dec(v___x_3134_);
lean_dec(v_next_3133_);
lean_dec(v_val_3131_);
lean_dec(v_val_3130_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(lean_object* v_val_3151_, lean_object* v_val_3152_, lean_object* v_upperBound_3153_, lean_object* v_args_3154_, lean_object* v_e_3155_, lean_object* v_next_3156_, lean_object* v_params_3157_, lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v_inst_3160_, lean_object* v_R_3161_, lean_object* v_a_3162_, lean_object* v_b_3163_, lean_object* v_c_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___redArg(v_val_3151_, v_val_3152_, v_upperBound_3153_, v_args_3154_, v_e_3155_, v_next_3156_, v_params_3157_, v___x_3158_, v___x_3159_, v_a_3162_, v_b_3163_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5___boxed(lean_object** _args){
lean_object* v_val_3171_ = _args[0];
lean_object* v_val_3172_ = _args[1];
lean_object* v_upperBound_3173_ = _args[2];
lean_object* v_args_3174_ = _args[3];
lean_object* v_e_3175_ = _args[4];
lean_object* v_next_3176_ = _args[5];
lean_object* v_params_3177_ = _args[6];
lean_object* v___x_3178_ = _args[7];
lean_object* v___x_3179_ = _args[8];
lean_object* v_inst_3180_ = _args[9];
lean_object* v_R_3181_ = _args[10];
lean_object* v_a_3182_ = _args[11];
lean_object* v_b_3183_ = _args[12];
lean_object* v_c_3184_ = _args[13];
lean_object* v___y_3185_ = _args[14];
lean_object* v___y_3186_ = _args[15];
lean_object* v___y_3187_ = _args[16];
lean_object* v___y_3188_ = _args[17];
lean_object* v___y_3189_ = _args[18];
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__5(v_val_3171_, v_val_3172_, v_upperBound_3173_, v_args_3174_, v_e_3175_, v_next_3176_, v_params_3177_, v___x_3178_, v___x_3179_, v_inst_3180_, v_R_3181_, v_a_3182_, v_b_3183_, v_c_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___x_3179_);
lean_dec(v___x_3178_);
lean_dec_ref(v_params_3177_);
lean_dec(v_next_3176_);
lean_dec_ref(v_args_3174_);
lean_dec(v_upperBound_3173_);
lean_dec(v_val_3171_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(lean_object* v___x_3191_, lean_object* v_preDefs_3192_, lean_object* v_val_3193_, lean_object* v_upperBound_3194_, lean_object* v_inst_3195_, lean_object* v_R_3196_, lean_object* v_a_3197_, lean_object* v_b_3198_, lean_object* v_c_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg(v___x_3191_, v_preDefs_3192_, v_val_3193_, v_upperBound_3194_, v_a_3197_, v_b_3198_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___boxed(lean_object* v___x_3206_, lean_object* v_preDefs_3207_, lean_object* v_val_3208_, lean_object* v_upperBound_3209_, lean_object* v_inst_3210_, lean_object* v_R_3211_, lean_object* v_a_3212_, lean_object* v_b_3213_, lean_object* v_c_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9(v___x_3206_, v_preDefs_3207_, v_val_3208_, v_upperBound_3209_, v_inst_3210_, v_R_3211_, v_a_3212_, v_b_3213_, v_c_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v_upperBound_3209_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(lean_object* v_upperBound_3221_, lean_object* v___x_3222_, lean_object* v_pre_3223_, lean_object* v_post_3224_, uint8_t v_usedLetOnly_3225_, uint8_t v_skipConstInApp_3226_, uint8_t v_skipInstances_3227_, lean_object* v___x_3228_, lean_object* v_inst_3229_, lean_object* v_R_3230_, lean_object* v_a_3231_, lean_object* v_b_3232_, lean_object* v_c_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___redArg(v_upperBound_3221_, v___x_3222_, v_pre_3223_, v_post_3224_, v_usedLetOnly_3225_, v_skipConstInApp_3226_, v_skipInstances_3227_, v_a_3231_, v_b_3232_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12___boxed(lean_object** _args){
lean_object* v_upperBound_3241_ = _args[0];
lean_object* v___x_3242_ = _args[1];
lean_object* v_pre_3243_ = _args[2];
lean_object* v_post_3244_ = _args[3];
lean_object* v_usedLetOnly_3245_ = _args[4];
lean_object* v_skipConstInApp_3246_ = _args[5];
lean_object* v_skipInstances_3247_ = _args[6];
lean_object* v___x_3248_ = _args[7];
lean_object* v_inst_3249_ = _args[8];
lean_object* v_R_3250_ = _args[9];
lean_object* v_a_3251_ = _args[10];
lean_object* v_b_3252_ = _args[11];
lean_object* v_c_3253_ = _args[12];
lean_object* v___y_3254_ = _args[13];
lean_object* v___y_3255_ = _args[14];
lean_object* v___y_3256_ = _args[15];
lean_object* v___y_3257_ = _args[16];
lean_object* v___y_3258_ = _args[17];
lean_object* v___y_3259_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3260_; uint8_t v_skipConstInApp_boxed_3261_; uint8_t v_skipInstances_boxed_3262_; lean_object* v_res_3263_; 
v_usedLetOnly_boxed_3260_ = lean_unbox(v_usedLetOnly_3245_);
v_skipConstInApp_boxed_3261_ = lean_unbox(v_skipConstInApp_3246_);
v_skipInstances_boxed_3262_ = lean_unbox(v_skipInstances_3247_);
v_res_3263_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__12(v_upperBound_3241_, v___x_3242_, v_pre_3243_, v_post_3244_, v_usedLetOnly_boxed_3260_, v_skipConstInApp_boxed_3261_, v_skipInstances_boxed_3262_, v___x_3248_, v_inst_3249_, v_R_3250_, v_a_3251_, v_b_3252_, v_c_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec(v___x_3248_);
lean_dec_ref(v___x_3242_);
lean_dec(v_upperBound_3241_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(lean_object* v_00_u03b2_3264_, lean_object* v_m_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___redArg(v_m_3265_, v_a_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3268_, lean_object* v_m_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13(v_00_u03b2_3268_, v_m_3269_, v_a_3270_);
lean_dec_ref(v_a_3270_);
lean_dec_ref(v_m_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(lean_object* v_00_u03b1_3272_, lean_object* v_name_3273_, uint8_t v_bi_3274_, lean_object* v_type_3275_, lean_object* v_k_3276_, uint8_t v_kind_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___redArg(v_name_3273_, v_bi_3274_, v_type_3275_, v_k_3276_, v_kind_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17___boxed(lean_object* v_00_u03b1_3285_, lean_object* v_name_3286_, lean_object* v_bi_3287_, lean_object* v_type_3288_, lean_object* v_k_3289_, lean_object* v_kind_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v_bi_boxed_3297_; uint8_t v_kind_boxed_3298_; lean_object* v_res_3299_; 
v_bi_boxed_3297_ = lean_unbox(v_bi_3287_);
v_kind_boxed_3298_ = lean_unbox(v_kind_3290_);
v_res_3299_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__14_spec__17(v_00_u03b1_3285_, v_name_3286_, v_bi_boxed_3297_, v_type_3288_, v_k_3289_, v_kind_boxed_3298_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(lean_object* v_00_u03b1_3300_, lean_object* v_name_3301_, lean_object* v_type_3302_, lean_object* v_val_3303_, lean_object* v_k_3304_, uint8_t v_nondep_3305_, uint8_t v_kind_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___redArg(v_name_3301_, v_type_3302_, v_val_3303_, v_k_3304_, v_nondep_3305_, v_kind_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20___boxed(lean_object* v_00_u03b1_3314_, lean_object* v_name_3315_, lean_object* v_type_3316_, lean_object* v_val_3317_, lean_object* v_k_3318_, lean_object* v_nondep_3319_, lean_object* v_kind_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
uint8_t v_nondep_boxed_3327_; uint8_t v_kind_boxed_3328_; lean_object* v_res_3329_; 
v_nondep_boxed_3327_ = lean_unbox(v_nondep_3319_);
v_kind_boxed_3328_ = lean_unbox(v_kind_3320_);
v_res_3329_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__16_spec__20(v_00_u03b1_3314_, v_name_3315_, v_type_3316_, v_val_3317_, v_k_3318_, v_nondep_boxed_3327_, v_kind_boxed_3328_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(lean_object* v_00_u03b1_3330_, lean_object* v_ref_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___x_3337_; 
v___x_3337_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___redArg(v_ref_3331_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23___boxed(lean_object* v_00_u03b1_3338_, lean_object* v_ref_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18_spec__23(v_00_u03b1_3338_, v_ref_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(lean_object* v_00_u03b1_3346_, lean_object* v_x_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___redArg(v_x_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18___boxed(lean_object* v_00_u03b1_3355_, lean_object* v_x_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__18(v_00_u03b1_3355_, v_x_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19(lean_object* v_00_u03b2_3364_, lean_object* v_m_3365_, lean_object* v_a_3366_, lean_object* v_b_3367_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19___redArg(v_m_3365_, v_a_3366_, v_b_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(lean_object* v_00_u03b2_3369_, lean_object* v_a_3370_, lean_object* v_x_3371_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___redArg(v_a_3370_, v_x_3371_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15___boxed(lean_object* v_00_u03b2_3373_, lean_object* v_a_3374_, lean_object* v_x_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__13_spec__15(v_00_u03b2_3373_, v_a_3374_, v_x_3375_);
lean_dec(v_x_3375_);
lean_dec_ref(v_a_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(lean_object* v_00_u03b2_3377_, lean_object* v_a_3378_, lean_object* v_x_3379_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___redArg(v_a_3378_, v_x_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25___boxed(lean_object* v_00_u03b2_3381_, lean_object* v_a_3382_, lean_object* v_x_3383_){
_start:
{
uint8_t v_res_3384_; lean_object* v_r_3385_; 
v_res_3384_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__25(v_00_u03b2_3381_, v_a_3382_, v_x_3383_);
lean_dec(v_x_3383_);
lean_dec_ref(v_a_3382_);
v_r_3385_ = lean_box(v_res_3384_);
return v_r_3385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26(lean_object* v_00_u03b2_3386_, lean_object* v_data_3387_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26___redArg(v_data_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27(lean_object* v_00_u03b2_3389_, lean_object* v_a_3390_, lean_object* v_b_3391_, lean_object* v_x_3392_){
_start:
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__27___redArg(v_a_3390_, v_b_3391_, v_x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27(lean_object* v_00_u03b2_3394_, lean_object* v_i_3395_, lean_object* v_source_3396_, lean_object* v_target_3397_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27___redArg(v_i_3395_, v_source_3396_, v_target_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28(lean_object* v_00_u03b2_3399_, lean_object* v_x_3400_, lean_object* v_x_3401_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_getFixedParamsInfo_spec__8_spec__9_spec__19_spec__26_spec__27_spec__28___redArg(v_x_3400_, v_x_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(lean_object* v_x_3416_, lean_object* v_x_3417_){
_start:
{
if (lean_obj_tag(v_x_3416_) == 0)
{
lean_object* v___x_3418_; 
v___x_3418_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_3418_;
}
else
{
lean_object* v_val_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3430_; 
v_val_3419_ = lean_ctor_get(v_x_3416_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_x_3416_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3421_ = v_x_3416_;
v_isShared_3422_ = v_isSharedCheck_3430_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_val_3419_);
lean_dec(v_x_3416_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3430_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3423_ = ((lean_object*)(l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___closed__3));
v___x_3424_ = l_Nat_reprFast(v_val_3419_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set_tag(v___x_3421_, 3);
lean_ctor_set(v___x_3421_, 0, v___x_3424_);
v___x_3426_ = v___x_3421_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3423_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Repr_addAppParen(v___x_3427_, v_x_3417_);
return v___x_3428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_3431_, lean_object* v_x_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_x_3431_, v_x_3432_);
lean_dec(v_x_3432_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(lean_object* v_x_3434_, lean_object* v_x_3435_, lean_object* v_x_3436_){
_start:
{
if (lean_obj_tag(v_x_3436_) == 0)
{
lean_dec(v_x_3434_);
return v_x_3435_;
}
else
{
lean_object* v_head_3437_; lean_object* v_tail_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3449_; 
v_head_3437_ = lean_ctor_get(v_x_3436_, 0);
v_tail_3438_ = lean_ctor_get(v_x_3436_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_x_3436_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3440_ = v_x_3436_;
v_isShared_3441_ = v_isSharedCheck_3449_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_tail_3438_);
lean_inc(v_head_3437_);
lean_dec(v_x_3436_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3449_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
lean_inc(v_x_3434_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set_tag(v___x_3440_, 5);
lean_ctor_set(v___x_3440_, 1, v_x_3434_);
lean_ctor_set(v___x_3440_, 0, v_x_3435_);
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_x_3435_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_x_3434_);
v___x_3443_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3437_, v___x_3444_);
v___x_3446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3443_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v_x_3435_ = v___x_3446_;
v_x_3436_ = v_tail_3438_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_3450_, lean_object* v_x_3451_, lean_object* v_x_3452_){
_start:
{
if (lean_obj_tag(v_x_3452_) == 0)
{
lean_dec(v_x_3450_);
return v_x_3451_;
}
else
{
lean_object* v_head_3453_; lean_object* v_tail_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3465_; 
v_head_3453_ = lean_ctor_get(v_x_3452_, 0);
v_tail_3454_ = lean_ctor_get(v_x_3452_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_x_3452_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3456_ = v_x_3452_;
v_isShared_3457_ = v_isSharedCheck_3465_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_tail_3454_);
lean_inc(v_head_3453_);
lean_dec(v_x_3452_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3465_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
lean_inc(v_x_3450_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set_tag(v___x_3456_, 5);
lean_ctor_set(v___x_3456_, 1, v_x_3450_);
lean_ctor_set(v___x_3456_, 0, v_x_3451_);
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_x_3451_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_x_3450_);
v___x_3459_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3460_ = lean_unsigned_to_nat(0u);
v___x_3461_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v_head_3453_, v___x_3460_);
v___x_3462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3459_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4_spec__8(v_x_3450_, v___x_3462_, v_tail_3454_);
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_unsigned_to_nat(0u);
v___x_3468_ = l_Option_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__1(v___y_3466_, v___x_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(lean_object* v_x_3469_, lean_object* v_x_3470_){
_start:
{
if (lean_obj_tag(v_x_3469_) == 0)
{
lean_object* v___x_3471_; 
lean_dec(v_x_3470_);
v___x_3471_ = lean_box(0);
return v___x_3471_;
}
else
{
lean_object* v_tail_3472_; 
v_tail_3472_ = lean_ctor_get(v_x_3469_, 1);
if (lean_obj_tag(v_tail_3472_) == 0)
{
lean_object* v_head_3473_; lean_object* v___x_3474_; 
lean_dec(v_x_3470_);
v_head_3473_ = lean_ctor_get(v_x_3469_, 0);
lean_inc(v_head_3473_);
lean_dec_ref_known(v_x_3469_, 2);
v___x_3474_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3473_);
return v___x_3474_;
}
else
{
lean_object* v_head_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_inc(v_tail_3472_);
v_head_3475_ = lean_ctor_get(v_x_3469_, 0);
lean_inc(v_head_3475_);
lean_dec_ref_known(v_x_3469_, 2);
v___x_3476_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2___lam__0(v_head_3475_);
v___x_3477_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2_spec__4(v_x_3470_, v___x_3476_, v_tail_3472_);
return v___x_3477_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__0));
v___x_3486_ = lean_string_length(v___x_3485_);
return v___x_3486_;
}
}
static lean_object* _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__4);
v___x_3488_ = lean_nat_to_int(v___x_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(lean_object* v_xs_3494_){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v___x_3495_ = lean_array_get_size(v_xs_3494_);
v___x_3496_ = lean_unsigned_to_nat(0u);
v___x_3497_ = lean_nat_dec_eq(v___x_3495_, v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3498_ = lean_array_to_list(v_xs_3494_);
v___x_3499_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3500_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0_spec__2(v___x_3498_, v___x_3499_);
v___x_3501_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3502_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3503_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3500_);
v___x_3504_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3503_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3501_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = l_Std_Format_fill(v___x_3506_);
return v___x_3507_;
}
else
{
lean_object* v___x_3508_; 
lean_dec_ref(v_xs_3494_);
v___x_3508_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3508_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(lean_object* v_x_3509_, lean_object* v_x_3510_, lean_object* v_x_3511_){
_start:
{
if (lean_obj_tag(v_x_3511_) == 0)
{
lean_dec(v_x_3509_);
return v_x_3510_;
}
else
{
lean_object* v_head_3512_; lean_object* v_tail_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3523_; 
v_head_3512_ = lean_ctor_get(v_x_3511_, 0);
v_tail_3513_ = lean_ctor_get(v_x_3511_, 1);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_x_3511_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3515_ = v_x_3511_;
v_isShared_3516_ = v_isSharedCheck_3523_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_tail_3513_);
lean_inc(v_head_3512_);
lean_dec(v_x_3511_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3523_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
lean_inc(v_x_3509_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set_tag(v___x_3515_, 5);
lean_ctor_set(v___x_3515_, 1, v_x_3509_);
lean_ctor_set(v___x_3515_, 0, v_x_3510_);
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_x_3510_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_x_3509_);
v___x_3518_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3512_);
v___x_3520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v_x_3510_ = v___x_3520_;
v_x_3511_ = v_tail_3513_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(lean_object* v_x_3524_, lean_object* v_x_3525_){
_start:
{
if (lean_obj_tag(v_x_3524_) == 0)
{
lean_object* v___x_3526_; 
lean_dec(v_x_3525_);
v___x_3526_ = lean_box(0);
return v___x_3526_;
}
else
{
lean_object* v_tail_3527_; 
v_tail_3527_ = lean_ctor_get(v_x_3524_, 1);
if (lean_obj_tag(v_tail_3527_) == 0)
{
lean_object* v_head_3528_; lean_object* v___x_3529_; 
lean_dec(v_x_3525_);
v_head_3528_ = lean_ctor_get(v_x_3524_, 0);
lean_inc(v_head_3528_);
lean_dec_ref_known(v_x_3524_, 2);
v___x_3529_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3528_);
return v___x_3529_;
}
else
{
lean_object* v_head_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_inc(v_tail_3527_);
v_head_3530_ = lean_ctor_get(v_x_3524_, 0);
lean_inc(v_head_3530_);
lean_dec_ref_known(v_x_3524_, 2);
v___x_3531_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0(v_head_3530_);
v___x_3532_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1_spec__4(v_x_3525_, v___x_3531_, v_tail_3527_);
return v___x_3532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(lean_object* v_xs_3533_){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; 
v___x_3534_ = lean_array_get_size(v_xs_3533_);
v___x_3535_ = lean_unsigned_to_nat(0u);
v___x_3536_ = lean_nat_dec_eq(v___x_3534_, v___x_3535_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3537_ = lean_array_to_list(v_xs_3533_);
v___x_3538_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3539_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__1(v___x_3537_, v___x_3538_);
v___x_3540_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3541_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
lean_ctor_set(v___x_3542_, 1, v___x_3539_);
v___x_3543_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3540_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = l_Std_Format_fill(v___x_3545_);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; 
lean_dec_ref(v_xs_3533_);
v___x_3547_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(lean_object* v_x_3548_, lean_object* v_x_3549_, lean_object* v_x_3550_){
_start:
{
if (lean_obj_tag(v_x_3550_) == 0)
{
lean_dec(v_x_3548_);
return v_x_3549_;
}
else
{
lean_object* v_head_3551_; lean_object* v_tail_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3563_; 
v_head_3551_ = lean_ctor_get(v_x_3550_, 0);
v_tail_3552_ = lean_ctor_get(v_x_3550_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_x_3550_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3554_ = v_x_3550_;
v_isShared_3555_ = v_isSharedCheck_3563_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_tail_3552_);
lean_inc(v_head_3551_);
lean_dec(v_x_3550_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3563_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
lean_inc(v_x_3548_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set_tag(v___x_3554_, 5);
lean_ctor_set(v___x_3554_, 1, v_x_3548_);
lean_ctor_set(v___x_3554_, 0, v_x_3549_);
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_x_3549_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_x_3548_);
v___x_3557_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = l_Nat_reprFast(v_head_3551_);
v___x_3559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
v___x_3560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3557_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v_x_3549_ = v___x_3560_;
v_x_3550_ = v_tail_3552_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v_x_3564_, lean_object* v_x_3565_, lean_object* v_x_3566_){
_start:
{
if (lean_obj_tag(v_x_3566_) == 0)
{
lean_dec(v_x_3564_);
return v_x_3565_;
}
else
{
lean_object* v_head_3567_; lean_object* v_tail_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3579_; 
v_head_3567_ = lean_ctor_get(v_x_3566_, 0);
v_tail_3568_ = lean_ctor_get(v_x_3566_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_x_3566_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3570_ = v_x_3566_;
v_isShared_3571_ = v_isSharedCheck_3579_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_tail_3568_);
lean_inc(v_head_3567_);
lean_dec(v_x_3566_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3579_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
lean_inc(v_x_3564_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set_tag(v___x_3570_, 5);
lean_ctor_set(v___x_3570_, 1, v_x_3564_);
lean_ctor_set(v___x_3570_, 0, v_x_3565_);
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_x_3565_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_x_3564_);
v___x_3573_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3574_ = l_Nat_reprFast(v_head_3567_);
v___x_3575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
v___x_3576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3573_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12_spec__15(v_x_3564_, v___x_3576_, v_tail_3568_);
return v___x_3577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(lean_object* v___y_3580_){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = l_Nat_reprFast(v___y_3580_);
v___x_3582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(lean_object* v_x_3583_, lean_object* v_x_3584_){
_start:
{
if (lean_obj_tag(v_x_3583_) == 0)
{
lean_object* v___x_3585_; 
lean_dec(v_x_3584_);
v___x_3585_ = lean_box(0);
return v___x_3585_;
}
else
{
lean_object* v_tail_3586_; 
v_tail_3586_ = lean_ctor_get(v_x_3583_, 1);
if (lean_obj_tag(v_tail_3586_) == 0)
{
lean_object* v_head_3587_; lean_object* v___x_3588_; 
lean_dec(v_x_3584_);
v_head_3587_ = lean_ctor_get(v_x_3583_, 0);
lean_inc(v_head_3587_);
lean_dec_ref_known(v_x_3583_, 2);
v___x_3588_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3587_);
return v___x_3588_;
}
else
{
lean_object* v_head_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
lean_inc(v_tail_3586_);
v_head_3589_ = lean_ctor_get(v_x_3583_, 0);
lean_inc(v_head_3589_);
lean_dec_ref_known(v_x_3583_, 2);
v___x_3590_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9___lam__0(v_head_3589_);
v___x_3591_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9_spec__12(v_x_3584_, v___x_3590_, v_tail_3586_);
return v___x_3591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(lean_object* v_xs_3592_){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v___x_3593_ = lean_array_get_size(v_xs_3592_);
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = lean_nat_dec_eq(v___x_3593_, v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3596_ = lean_array_to_list(v_xs_3592_);
v___x_3597_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3598_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7_spec__9(v___x_3596_, v___x_3597_);
v___x_3599_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3600_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set(v___x_3601_, 1, v___x_3598_);
v___x_3602_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3599_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = l_Std_Format_fill(v___x_3604_);
return v___x_3605_;
}
else
{
lean_object* v___x_3606_; 
lean_dec_ref(v_xs_3592_);
v___x_3606_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3606_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(lean_object* v_x_3607_, lean_object* v_x_3608_, lean_object* v_x_3609_){
_start:
{
if (lean_obj_tag(v_x_3609_) == 0)
{
lean_dec(v_x_3607_);
return v_x_3608_;
}
else
{
lean_object* v_head_3610_; lean_object* v_tail_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3621_; 
v_head_3610_ = lean_ctor_get(v_x_3609_, 0);
v_tail_3611_ = lean_ctor_get(v_x_3609_, 1);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_x_3609_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3613_ = v_x_3609_;
v_isShared_3614_ = v_isSharedCheck_3621_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_tail_3611_);
lean_inc(v_head_3610_);
lean_dec(v_x_3609_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3621_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
lean_inc(v_x_3607_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set_tag(v___x_3613_, 5);
lean_ctor_set(v___x_3613_, 1, v_x_3607_);
lean_ctor_set(v___x_3613_, 0, v_x_3608_);
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_x_3608_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_x_3607_);
v___x_3616_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3610_);
v___x_3618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3616_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v_x_3608_ = v___x_3618_;
v_x_3609_ = v_tail_3611_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
if (lean_obj_tag(v_x_3622_) == 0)
{
lean_object* v___x_3624_; 
lean_dec(v_x_3623_);
v___x_3624_ = lean_box(0);
return v___x_3624_;
}
else
{
lean_object* v_tail_3625_; 
v_tail_3625_ = lean_ctor_get(v_x_3622_, 1);
if (lean_obj_tag(v_tail_3625_) == 0)
{
lean_object* v_head_3626_; lean_object* v___x_3627_; 
lean_dec(v_x_3623_);
v_head_3626_ = lean_ctor_get(v_x_3622_, 0);
lean_inc(v_head_3626_);
lean_dec_ref_known(v_x_3622_, 2);
v___x_3627_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3626_);
return v___x_3627_;
}
else
{
lean_object* v_head_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
lean_inc(v_tail_3625_);
v_head_3628_ = lean_ctor_get(v_x_3622_, 0);
lean_inc(v_head_3628_);
lean_dec_ref_known(v_x_3622_, 2);
v___x_3629_ = l_Array_repr___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__7(v_head_3628_);
v___x_3630_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8_spec__11(v_x_3623_, v___x_3629_, v_tail_3625_);
return v___x_3630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(lean_object* v_xs_3631_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3632_ = lean_array_get_size(v_xs_3631_);
v___x_3633_ = lean_unsigned_to_nat(0u);
v___x_3634_ = lean_nat_dec_eq(v___x_3632_, v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3635_ = lean_array_to_list(v_xs_3631_);
v___x_3636_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3637_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3_spec__8(v___x_3635_, v___x_3636_);
v___x_3638_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3639_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3640_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
lean_ctor_set(v___x_3640_, 1, v___x_3637_);
v___x_3641_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3638_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = l_Std_Format_fill(v___x_3643_);
return v___x_3644_;
}
else
{
lean_object* v___x_3645_; 
lean_dec_ref(v_xs_3631_);
v___x_3645_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3645_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(lean_object* v_x_3646_, lean_object* v_x_3647_, lean_object* v_x_3648_){
_start:
{
if (lean_obj_tag(v_x_3648_) == 0)
{
lean_dec(v_x_3646_);
return v_x_3647_;
}
else
{
lean_object* v_head_3649_; lean_object* v_tail_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3660_; 
v_head_3649_ = lean_ctor_get(v_x_3648_, 0);
v_tail_3650_ = lean_ctor_get(v_x_3648_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_x_3648_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3652_ = v_x_3648_;
v_isShared_3653_ = v_isSharedCheck_3660_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_tail_3650_);
lean_inc(v_head_3649_);
lean_dec(v_x_3648_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3660_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
lean_inc(v_x_3646_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set_tag(v___x_3652_, 5);
lean_ctor_set(v___x_3652_, 1, v_x_3646_);
lean_ctor_set(v___x_3652_, 0, v_x_3647_);
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_x_3647_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_x_3646_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3649_);
v___x_3657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v_x_3647_ = v___x_3657_;
v_x_3648_ = v_tail_3650_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(lean_object* v_x_3661_, lean_object* v_x_3662_){
_start:
{
if (lean_obj_tag(v_x_3661_) == 0)
{
lean_object* v___x_3663_; 
lean_dec(v_x_3662_);
v___x_3663_ = lean_box(0);
return v___x_3663_;
}
else
{
lean_object* v_tail_3664_; 
v_tail_3664_ = lean_ctor_get(v_x_3661_, 1);
if (lean_obj_tag(v_tail_3664_) == 0)
{
lean_object* v_head_3665_; lean_object* v___x_3666_; 
lean_dec(v_x_3662_);
v_head_3665_ = lean_ctor_get(v_x_3661_, 0);
lean_inc(v_head_3665_);
lean_dec_ref_known(v_x_3661_, 2);
v___x_3666_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3665_);
return v___x_3666_;
}
else
{
lean_object* v_head_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
lean_inc(v_tail_3664_);
v_head_3667_ = lean_ctor_get(v_x_3661_, 0);
lean_inc(v_head_3667_);
lean_dec_ref_known(v_x_3661_, 2);
v___x_3668_ = l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__3(v_head_3667_);
v___x_3669_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4_spec__10(v_x_3662_, v___x_3668_, v_tail_3664_);
return v___x_3669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(lean_object* v_xs_3670_){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v___x_3671_ = lean_array_get_size(v_xs_3670_);
v___x_3672_ = lean_unsigned_to_nat(0u);
v___x_3673_ = lean_nat_dec_eq(v___x_3671_, v___x_3672_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3674_ = lean_array_to_list(v_xs_3670_);
v___x_3675_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__3));
v___x_3676_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1_spec__4(v___x_3674_, v___x_3675_);
v___x_3677_ = lean_obj_once(&l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5, &l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5_once, _init_l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__5);
v___x_3678_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__6));
v___x_3679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
lean_ctor_set(v___x_3679_, 1, v___x_3676_);
v___x_3680_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_FixedParams_Info_format_spec__3___closed__9));
v___x_3681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3677_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
v___x_3683_ = l_Std_Format_fill(v___x_3682_);
return v___x_3683_;
}
else
{
lean_object* v___x_3684_; 
lean_dec_ref(v_xs_3670_);
v___x_3684_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__8));
return v___x_3684_;
}
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_unsigned_to_nat(12u);
v___x_3699_ = lean_nat_to_int(v___x_3698_);
return v___x_3699_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = lean_unsigned_to_nat(9u);
v___x_3704_ = lean_nat_to_int(v___x_3703_);
return v___x_3704_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = lean_unsigned_to_nat(11u);
v___x_3709_ = lean_nat_to_int(v___x_3708_);
return v___x_3709_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__0));
v___x_3712_ = lean_string_length(v___x_3711_);
return v___x_3712_;
}
}
static lean_object* _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__15);
v___x_3714_ = lean_nat_to_int(v___x_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___redArg(lean_object* v_x_3719_){
_start:
{
lean_object* v_numFixed_3720_; lean_object* v_perms_3721_; lean_object* v_revDeps_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v_numFixed_3720_ = lean_ctor_get(v_x_3719_, 0);
lean_inc(v_numFixed_3720_);
v_perms_3721_ = lean_ctor_get(v_x_3719_, 1);
lean_inc_ref(v_perms_3721_);
v_revDeps_3722_ = lean_ctor_get(v_x_3719_, 2);
lean_inc_ref(v_revDeps_3722_);
lean_dec_ref(v_x_3719_);
v___x_3723_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__5));
v___x_3724_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__6));
v___x_3725_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__7);
v___x_3726_ = l_Nat_reprFast(v_numFixed_3720_);
v___x_3727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
v___x_3728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3725_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = 0;
v___x_3730_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3724_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = ((lean_object*)(l_Array_repr___at___00Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0_spec__0___closed__2));
v___x_3733_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_box(1);
v___x_3735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__9));
v___x_3737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v___x_3723_);
v___x_3739_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__10);
v___x_3740_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__0(v_perms_3721_);
v___x_3741_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set_uint8(v___x_3742_, sizeof(void*)*1, v___x_3729_);
v___x_3743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3738_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set(v___x_3744_, 1, v___x_3732_);
v___x_3745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
lean_ctor_set(v___x_3745_, 1, v___x_3734_);
v___x_3746_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__12));
v___x_3747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
lean_ctor_set(v___x_3748_, 1, v___x_3723_);
v___x_3749_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__13);
v___x_3750_ = l_Array_repr___at___00Lean_Elab_instReprFixedParamPerms_repr_spec__1(v_revDeps_3722_);
v___x_3751_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
lean_ctor_set_uint8(v___x_3752_, sizeof(void*)*1, v___x_3729_);
v___x_3753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3748_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_obj_once(&l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16, &l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16_once, _init_l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__16);
v___x_3755_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__17));
v___x_3756_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
lean_ctor_set(v___x_3756_, 1, v___x_3753_);
v___x_3757_ = ((lean_object*)(l_Lean_Elab_instReprFixedParamPerms_repr___redArg___closed__18));
v___x_3758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3756_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3754_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set_uint8(v___x_3760_, sizeof(void*)*1, v___x_3729_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr(lean_object* v_x_3761_, lean_object* v_prec_3762_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_Elab_instReprFixedParamPerms_repr___redArg(v_x_3761_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instReprFixedParamPerms_repr___boxed(lean_object* v_x_3764_, lean_object* v_prec_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_Elab_instReprFixedParamPerms_repr(v_x_3764_, v_prec_3765_);
lean_dec(v_prec_3765_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(lean_object* v_msg_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___f_3775_; lean_object* v___x_5728__overap_3776_; lean_object* v___x_3777_; 
v___f_3775_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5728__overap_3776_ = lean_panic_fn_borrowed(v___f_3775_, v_msg_3769_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
lean_inc(v___y_3771_);
lean_inc_ref(v___y_3770_);
v___x_3777_ = lean_apply_5(v___x_5728__overap_3776_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, lean_box(0));
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0___boxed(lean_object* v_msg_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v_msg_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(lean_object* v_msg_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___f_3791_; lean_object* v___x_5738__overap_3792_; lean_object* v___x_3793_; 
v___f_3791_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5738__overap_3792_ = lean_panic_fn_borrowed(v___f_3791_, v_msg_3785_);
lean_inc(v___y_3789_);
lean_inc_ref(v___y_3788_);
lean_inc(v___y_3787_);
lean_inc_ref(v___y_3786_);
v___x_3793_ = lean_apply_5(v___x_5738__overap_3792_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, lean_box(0));
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1___boxed(lean_object* v_msg_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v_msg_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(lean_object* v_msg_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___f_3807_; lean_object* v___x_5748__overap_3808_; lean_object* v___x_3809_; 
v___f_3807_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_5748__overap_3808_ = lean_panic_fn_borrowed(v___f_3807_, v_msg_3801_);
lean_inc(v___y_3805_);
lean_inc_ref(v___y_3804_);
lean_inc(v___y_3803_);
lean_inc_ref(v___y_3802_);
v___x_3809_ = lean_apply_5(v___x_5748__overap_3808_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, lean_box(0));
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2___boxed(lean_object* v_msg_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v_msg_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
return v_res_3816_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__1));
v___x_3820_ = lean_unsigned_to_nat(12u);
v___x_3821_ = lean_unsigned_to_nat(294u);
v___x_3822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3823_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3824_ = l_mkPanicMessageWithDecl(v___x_3823_, v___x_3822_, v___x_3821_, v___x_3820_, v___x_3819_);
return v___x_3824_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4(void){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__3));
v___x_3827_ = lean_unsigned_to_nat(12u);
v___x_3828_ = lean_unsigned_to_nat(297u);
v___x_3829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3830_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3831_ = l_mkPanicMessageWithDecl(v___x_3830_, v___x_3829_, v___x_3828_, v___x_3827_, v___x_3826_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(lean_object* v___x_3832_, lean_object* v_as_3833_, size_t v_sz_3834_, size_t v_i_3835_, lean_object* v_b_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v_a_3843_; uint8_t v___x_3847_; 
v___x_3847_ = lean_usize_dec_lt(v_i_3835_, v_sz_3834_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3848_, 0, v_b_3836_);
return v___x_3848_;
}
else
{
lean_object* v_a_3849_; 
v_a_3849_ = lean_array_uget_borrowed(v_as_3833_, v_i_3835_);
if (lean_obj_tag(v_a_3849_) == 1)
{
lean_object* v_val_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_val_3850_ = lean_ctor_get(v_a_3849_, 0);
v___x_3851_ = lean_box(0);
v___x_3852_ = lean_unsigned_to_nat(0u);
v___x_3853_ = lean_array_get_borrowed(v___x_3851_, v_val_3850_, v___x_3852_);
if (lean_obj_tag(v___x_3853_) == 1)
{
lean_object* v_val_3854_; lean_object* v___x_3855_; 
v_val_3854_ = lean_ctor_get(v___x_3853_, 0);
v___x_3855_ = lean_array_get_borrowed(v___x_3851_, v___x_3832_, v_val_3854_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec_ref(v_b_3836_);
v___x_3856_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__2);
v___x_3857_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__2(v___x_3856_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3867_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3867_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3867_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
if (lean_obj_tag(v_a_3858_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; 
v_a_3862_ = lean_ctor_get(v_a_3858_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v_a_3858_, 1);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v_a_3862_);
v___x_3864_ = v___x_3860_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3862_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
else
{
lean_object* v_a_3866_; 
lean_del_object(v___x_3860_);
v_a_3866_ = lean_ctor_get(v_a_3858_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v_a_3858_, 1);
v_a_3843_ = v_a_3866_;
goto v___jp_3842_;
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
v_a_3868_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3857_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3857_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v___x_3876_; 
lean_inc_ref(v___x_3855_);
v___x_3876_ = lean_array_push(v_b_3836_, v___x_3855_);
v_a_3843_ = v___x_3876_;
goto v___jp_3842_;
}
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__4);
v___x_3878_ = l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7(v___x_3877_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_dec_ref_known(v___x_3878_, 1);
v_a_3843_ = v_b_3836_;
goto v___jp_3842_;
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v_b_3836_);
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
else
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_box(0);
v___x_3888_ = lean_array_push(v_b_3836_, v___x_3887_);
v_a_3843_ = v___x_3888_;
goto v___jp_3842_;
}
}
v___jp_3842_:
{
size_t v___x_3844_; size_t v___x_3845_; 
v___x_3844_ = ((size_t)1ULL);
v___x_3845_ = lean_usize_add(v_i_3835_, v___x_3844_);
v_i_3835_ = v___x_3845_;
v_b_3836_ = v_a_3843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___boxed(lean_object* v___x_3889_, lean_object* v_as_3890_, lean_object* v_sz_3891_, lean_object* v_i_3892_, lean_object* v_b_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
size_t v_sz_boxed_3899_; size_t v_i_boxed_3900_; lean_object* v_res_3901_; 
v_sz_boxed_3899_ = lean_unbox_usize(v_sz_3891_);
lean_dec(v_sz_3891_);
v_i_boxed_3900_ = lean_unbox_usize(v_i_3892_);
lean_dec(v_i_3892_);
v_res_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3889_, v_as_3890_, v_sz_boxed_3899_, v_i_boxed_3900_, v_b_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v_as_3890_);
lean_dec_ref(v___x_3889_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(lean_object* v_upperBound_3904_, lean_object* v___x_3905_, lean_object* v___x_3906_, lean_object* v_a_3907_, lean_object* v_b_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
uint8_t v___x_3914_; 
v___x_3914_ = lean_nat_dec_lt(v_a_3907_, v_upperBound_3904_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; 
lean_dec(v_a_3907_);
v___x_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3915_, 0, v_b_3908_);
return v___x_3915_;
}
else
{
lean_object* v___x_3916_; lean_object* v___x_3917_; size_t v_sz_3918_; size_t v___x_3919_; lean_object* v___x_3920_; 
v___x_3916_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___closed__0));
v___x_3917_ = lean_array_fget_borrowed(v___x_3905_, v_a_3907_);
v_sz_3918_ = lean_array_size(v___x_3917_);
v___x_3919_ = ((size_t)0ULL);
v___x_3920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3(v___x_3906_, v___x_3917_, v_sz_3918_, v___x_3919_, v___x_3916_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___x_3920_, 1);
v___x_3922_ = lean_array_push(v_b_3908_, v_a_3921_);
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_nat_add(v_a_3907_, v___x_3923_);
lean_dec(v_a_3907_);
v_a_3907_ = v___x_3924_;
v_b_3908_ = v___x_3922_;
goto _start;
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_dec_ref(v_b_3908_);
lean_dec(v_a_3907_);
v_a_3926_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3920_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3920_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg___boxed(lean_object* v_upperBound_3934_, lean_object* v___x_3935_, lean_object* v___x_3936_, lean_object* v_a_3937_, lean_object* v_b_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_3934_, v___x_3935_, v___x_3936_, v_a_3937_, v_b_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec_ref(v___x_3936_);
lean_dec_ref(v___x_3935_);
lean_dec(v_upperBound_3934_);
return v_res_3944_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3946_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__0));
v___x_3947_ = lean_unsigned_to_nat(8u);
v___x_3948_ = lean_unsigned_to_nat(281u);
v___x_3949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_3950_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_3951_ = l_mkPanicMessageWithDecl(v___x_3950_, v___x_3949_, v___x_3948_, v___x_3947_, v___x_3946_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(lean_object* v_upperBound_3952_, lean_object* v_a_3953_, lean_object* v_b_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v_a_3961_; uint8_t v___x_3965_; 
v___x_3965_ = lean_nat_dec_lt(v_a_3953_, v_upperBound_3952_);
if (v___x_3965_ == 0)
{
lean_object* v___x_3966_; 
lean_dec(v_a_3953_);
v___x_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3966_, 0, v_b_3954_);
return v___x_3966_;
}
else
{
lean_object* v_snd_3967_; lean_object* v_snd_3968_; lean_object* v_snd_3969_; lean_object* v_fst_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_4094_; 
v_snd_3967_ = lean_ctor_get(v_b_3954_, 1);
lean_inc(v_snd_3967_);
v_snd_3968_ = lean_ctor_get(v_snd_3967_, 1);
lean_inc(v_snd_3968_);
v_snd_3969_ = lean_ctor_get(v_snd_3968_, 1);
lean_inc(v_snd_3969_);
v_fst_3970_ = lean_ctor_get(v_b_3954_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_b_3954_);
if (v_isSharedCheck_4094_ == 0)
{
lean_object* v_unused_4095_; 
v_unused_4095_ = lean_ctor_get(v_b_3954_, 1);
lean_dec(v_unused_4095_);
v___x_3972_ = v_b_3954_;
v_isShared_3973_ = v_isSharedCheck_4094_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_fst_3970_);
lean_dec(v_b_3954_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_4094_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v_fst_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_4092_; 
v_fst_3974_ = lean_ctor_get(v_snd_3967_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_snd_3967_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v_snd_3967_, 1);
lean_dec(v_unused_4093_);
v___x_3976_ = v_snd_3967_;
v_isShared_3977_ = v_isSharedCheck_4092_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_fst_3974_);
lean_dec(v_snd_3967_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_4092_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v_fst_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4090_; 
v_fst_3978_ = lean_ctor_get(v_snd_3968_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_snd_3968_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v_snd_3968_, 1);
lean_dec(v_unused_4091_);
v___x_3980_ = v_snd_3968_;
v_isShared_3981_ = v_isSharedCheck_4090_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_fst_3978_);
lean_dec(v_snd_3968_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4090_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v_array_3982_; lean_object* v_start_3983_; lean_object* v_stop_3984_; uint8_t v___x_3985_; 
v_array_3982_ = lean_ctor_get(v_snd_3969_, 0);
v_start_3983_ = lean_ctor_get(v_snd_3969_, 1);
v_stop_3984_ = lean_ctor_get(v_snd_3969_, 2);
v___x_3985_ = lean_nat_dec_lt(v_start_3983_, v_stop_3984_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3987_; 
lean_dec(v_a_3953_);
if (v_isShared_3981_ == 0)
{
v___x_3987_ = v___x_3980_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_fst_3978_);
lean_ctor_set(v_reuseFailAlloc_3995_, 1, v_snd_3969_);
v___x_3987_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3989_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 1, v___x_3987_);
v___x_3989_ = v___x_3976_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_fst_3974_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3991_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v___x_3989_);
v___x_3991_ = v___x_3972_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_fst_3970_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
return v___x_3992_;
}
}
}
}
else
{
lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4086_; 
lean_inc(v_stop_3984_);
lean_inc(v_start_3983_);
lean_inc_ref(v_array_3982_);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_snd_3969_);
if (v_isSharedCheck_4086_ == 0)
{
lean_object* v_unused_4087_; lean_object* v_unused_4088_; lean_object* v_unused_4089_; 
v_unused_4087_ = lean_ctor_get(v_snd_3969_, 2);
lean_dec(v_unused_4087_);
v_unused_4088_ = lean_ctor_get(v_snd_3969_, 1);
lean_dec(v_unused_4088_);
v_unused_4089_ = lean_ctor_get(v_snd_3969_, 0);
lean_dec(v_unused_4089_);
v___x_3997_ = v_snd_3969_;
v_isShared_3998_ = v_isSharedCheck_4086_;
goto v_resetjp_3996_;
}
else
{
lean_dec(v_snd_3969_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4086_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v_array_3999_; lean_object* v_start_4000_; lean_object* v_stop_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4006_; 
v_array_3999_ = lean_ctor_get(v_fst_3978_, 0);
v_start_4000_ = lean_ctor_get(v_fst_3978_, 1);
v_stop_4001_ = lean_ctor_get(v_fst_3978_, 2);
v___x_4002_ = lean_array_fget(v_array_3982_, v_start_3983_);
v___x_4003_ = lean_unsigned_to_nat(1u);
v___x_4004_ = lean_nat_add(v_start_3983_, v___x_4003_);
lean_dec(v_start_3983_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 1, v___x_4004_);
v___x_4006_ = v___x_3997_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_array_3982_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4085_, 2, v_stop_3984_);
v___x_4006_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_nat_dec_lt(v_start_4000_, v_stop_4001_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4009_; 
lean_dec(v___x_4002_);
lean_dec(v_a_3953_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 1, v___x_4006_);
v___x_4009_ = v___x_3980_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_fst_3978_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v___x_4006_);
v___x_4009_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4011_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 1, v___x_4009_);
v___x_4011_ = v___x_3976_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_fst_3974_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
lean_object* v___x_4013_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v___x_4011_);
v___x_4013_ = v___x_3972_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_fst_3970_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
return v___x_4014_;
}
}
}
}
else
{
lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4081_; 
lean_inc(v_stop_4001_);
lean_inc(v_start_4000_);
lean_inc_ref(v_array_3999_);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_fst_3978_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; lean_object* v_unused_4083_; lean_object* v_unused_4084_; 
v_unused_4082_ = lean_ctor_get(v_fst_3978_, 2);
lean_dec(v_unused_4082_);
v_unused_4083_ = lean_ctor_get(v_fst_3978_, 1);
lean_dec(v_unused_4083_);
v_unused_4084_ = lean_ctor_get(v_fst_3978_, 0);
lean_dec(v_unused_4084_);
v___x_4019_ = v_fst_3978_;
v_isShared_4020_ = v_isSharedCheck_4081_;
goto v_resetjp_4018_;
}
else
{
lean_dec(v_fst_3978_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4081_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v___x_4023_; 
v___x_4021_ = lean_nat_add(v_start_4000_, v___x_4003_);
lean_dec(v_start_4000_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 1, v___x_4021_);
v___x_4023_ = v___x_4019_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_array_3999_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v___x_4021_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_stop_4001_);
v___x_4023_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
if (lean_obj_tag(v___x_4002_) == 1)
{
lean_object* v_val_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4068_; 
v_val_4024_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4026_ = v___x_4002_;
v_isShared_4027_ = v_isSharedCheck_4068_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_val_4024_);
lean_dec(v___x_4002_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4068_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
v___x_4028_ = lean_box(0);
v___x_4029_ = lean_unsigned_to_nat(0u);
v___x_4030_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___x_4031_ = lean_array_get(v___x_4028_, v_val_4024_, v___x_4029_);
lean_dec(v_val_4024_);
lean_inc(v_a_3953_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v_a_3953_);
v___x_4033_ = v___x_4026_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_3953_);
v___x_4033_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
uint8_t v___x_4034_; 
v___x_4034_ = l_Option_instDecidableEq___redArg(v___x_4030_, v___x_4031_, v___x_4033_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
lean_dec_ref(v___x_4023_);
lean_dec_ref(v___x_4006_);
lean_del_object(v___x_3980_);
lean_del_object(v___x_3976_);
lean_dec(v_fst_3974_);
lean_del_object(v___x_3972_);
lean_dec(v_fst_3970_);
v___x_4035_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___closed__1);
v___x_4036_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__1(v___x_4035_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4046_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4039_ = v___x_4036_;
v_isShared_4040_ = v_isSharedCheck_4046_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4046_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
if (lean_obj_tag(v_a_4037_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; 
lean_dec(v_a_3953_);
v_a_4041_ = lean_ctor_get(v_a_4037_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v_a_4037_, 1);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v_a_4041_);
v___x_4043_ = v___x_4039_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4041_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
else
{
lean_object* v_a_4045_; 
lean_del_object(v___x_4039_);
v_a_4045_ = lean_ctor_get(v_a_4037_, 0);
lean_inc(v_a_4045_);
lean_dec_ref_known(v_a_4037_, 1);
v_a_3961_ = v_a_4045_;
goto v___jp_3960_;
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
lean_dec(v_a_3953_);
v_a_4047_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4036_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4036_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
else
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4059_; 
lean_inc(v_fst_3974_);
v___x_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4055_, 0, v_fst_3974_);
v___x_4056_ = lean_array_push(v_fst_3970_, v___x_4055_);
v___x_4057_ = lean_nat_add(v_fst_3974_, v___x_4003_);
lean_dec(v_fst_3974_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 1, v___x_4006_);
lean_ctor_set(v___x_3980_, 0, v___x_4023_);
v___x_4059_ = v___x_3980_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4023_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4006_);
v___x_4059_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4061_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 1, v___x_4059_);
lean_ctor_set(v___x_3976_, 0, v___x_4057_);
v___x_4061_ = v___x_3976_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4057_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4063_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v___x_4061_);
lean_ctor_set(v___x_3972_, 0, v___x_4056_);
v___x_4063_ = v___x_3972_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4056_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
v_a_3961_ = v___x_4063_;
goto v___jp_3960_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
lean_dec(v___x_4002_);
v___x_4069_ = lean_box(0);
v___x_4070_ = lean_array_push(v_fst_3970_, v___x_4069_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 1, v___x_4006_);
lean_ctor_set(v___x_3980_, 0, v___x_4023_);
v___x_4072_ = v___x_3980_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4023_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v___x_4006_);
v___x_4072_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4074_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 1, v___x_4072_);
v___x_4074_ = v___x_3976_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_fst_3974_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4076_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v___x_4074_);
lean_ctor_set(v___x_3972_, 0, v___x_4070_);
v___x_4076_ = v___x_3972_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4070_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4074_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
v_a_3961_ = v___x_4076_;
goto v___jp_3960_;
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
v___jp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_unsigned_to_nat(1u);
v___x_3963_ = lean_nat_add(v_a_3953_, v___x_3962_);
lean_dec(v_a_3953_);
v_a_3953_ = v___x_3963_;
v_b_3954_ = v_a_3961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg___boxed(lean_object* v_upperBound_4096_, lean_object* v_a_4097_, lean_object* v_b_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4096_, v_a_4097_, v_b_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v_upperBound_4096_);
return v_res_4104_;
}
}
static lean_object* _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4106_ = ((lean_object*)(l_Lean_Elab_getFixedParamPerms___lam__0___closed__0));
v___x_4107_ = lean_unsigned_to_nat(4u);
v___x_4108_ = lean_unsigned_to_nat(275u);
v___x_4109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_getFixedParamPerms_spec__3___closed__0));
v___x_4110_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4111_ = l_mkPanicMessageWithDecl(v___x_4110_, v___x_4109_, v___x_4108_, v___x_4107_, v___x_4106_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0(lean_object* v_a_4112_, lean_object* v___x_4113_, lean_object* v___x_4114_, lean_object* v_xs_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_graph_4122_; lean_object* v_revDeps_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4176_; 
v_graph_4122_ = lean_ctor_get(v_a_4112_, 0);
v_revDeps_4123_ = lean_ctor_get(v_a_4112_, 1);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_a_4112_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4125_ = v_a_4112_;
v_isShared_4126_ = v_isSharedCheck_4176_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_revDeps_4123_);
lean_inc(v_graph_4122_);
lean_dec(v_a_4112_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4176_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; uint8_t v___x_4130_; 
v___x_4127_ = lean_array_get_borrowed(v___x_4113_, v_graph_4122_, v___x_4114_);
v___x_4128_ = lean_array_get_size(v_xs_4115_);
v___x_4129_ = lean_array_get_size(v___x_4127_);
v___x_4130_ = lean_nat_dec_eq(v___x_4128_, v___x_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_del_object(v___x_4125_);
lean_dec_ref(v_revDeps_4123_);
lean_dec_ref(v_graph_4122_);
lean_dec_ref(v_xs_4115_);
lean_dec(v___x_4114_);
v___x_4131_ = lean_obj_once(&l_Lean_Elab_getFixedParamPerms___lam__0___closed__1, &l_Lean_Elab_getFixedParamPerms___lam__0___closed__1_once, _init_l_Lean_Elab_getFixedParamPerms___lam__0___closed__1);
v___x_4132_ = l_panic___at___00Lean_Elab_getFixedParamPerms_spec__0(v___x_4131_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
return v___x_4132_;
}
else
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
v___x_4133_ = lean_mk_empty_array_with_capacity(v___x_4114_);
lean_inc_n(v___x_4114_, 2);
v___x_4134_ = l_Array_toSubarray___redArg(v_xs_4115_, v___x_4114_, v___x_4128_);
lean_inc(v___x_4127_);
v___x_4135_ = l_Array_toSubarray___redArg(v___x_4127_, v___x_4114_, v___x_4129_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 1, v___x_4135_);
lean_ctor_set(v___x_4125_, 0, v___x_4134_);
v___x_4137_ = v___x_4125_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4134_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
lean_inc(v___x_4114_);
v___x_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4114_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4133_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v___x_4128_, v___x_4114_, v___x_4139_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v_snd_4142_; lean_object* v_fst_4143_; lean_object* v_fst_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v_snd_4142_ = lean_ctor_get(v_a_4141_, 1);
lean_inc(v_snd_4142_);
v_fst_4143_ = lean_ctor_get(v_a_4141_, 0);
lean_inc_n(v_fst_4143_, 2);
lean_dec(v_a_4141_);
v_fst_4144_ = lean_ctor_get(v_snd_4142_, 0);
lean_inc(v_fst_4144_);
lean_dec(v_snd_4142_);
v___x_4145_ = lean_unsigned_to_nat(1u);
v___x_4146_ = lean_array_get_size(v_graph_4122_);
v___x_4147_ = lean_mk_empty_array_with_capacity(v___x_4145_);
v___x_4148_ = lean_array_push(v___x_4147_, v_fst_4143_);
v___x_4149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v___x_4146_, v_graph_4122_, v_fst_4143_, v___x_4145_, v___x_4148_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec(v_fst_4143_);
lean_dec_ref(v_graph_4122_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4158_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4152_ = v___x_4149_;
v_isShared_4153_ = v_isSharedCheck_4158_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4149_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4158_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4154_; lean_object* v___x_4156_; 
v___x_4154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4154_, 0, v_fst_4144_);
lean_ctor_set(v___x_4154_, 1, v_a_4150_);
lean_ctor_set(v___x_4154_, 2, v_revDeps_4123_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v___x_4154_);
v___x_4156_ = v___x_4152_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4154_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec(v_fst_4144_);
lean_dec_ref(v_revDeps_4123_);
v_a_4159_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4149_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4149_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_dec_ref(v_revDeps_4123_);
lean_dec_ref(v_graph_4122_);
v_a_4167_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4140_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4140_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___lam__0___boxed(lean_object* v_a_4177_, lean_object* v___x_4178_, lean_object* v___x_4179_, lean_object* v_xs_4180_, lean_object* v_x_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Lean_Elab_getFixedParamPerms___lam__0(v_a_4177_, v___x_4178_, v___x_4179_, v_xs_4180_, v_x_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec_ref(v_x_4181_);
lean_dec_ref(v___x_4178_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms(lean_object* v_preDefs_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4194_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_4195_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
lean_inc_ref(v_preDefs_4188_);
v___x_4196_ = l_Lean_Elab_getFixedParamsInfo(v_preDefs_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v_value_4200_; lean_object* v___f_4201_; uint8_t v___x_4202_; lean_object* v___x_4203_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___x_4198_ = lean_unsigned_to_nat(0u);
v___x_4199_ = lean_array_get(v___x_4194_, v_preDefs_4188_, v___x_4198_);
lean_dec_ref(v_preDefs_4188_);
v_value_4200_ = lean_ctor_get(v___x_4199_, 7);
lean_inc_ref(v_value_4200_);
lean_dec(v___x_4199_);
v___f_4201_ = lean_alloc_closure((void*)(l_Lean_Elab_getFixedParamPerms___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4201_, 0, v_a_4197_);
lean_closure_set(v___f_4201_, 1, v___x_4195_);
lean_closure_set(v___f_4201_, 2, v___x_4198_);
v___x_4202_ = 0;
v___x_4203_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg(v_value_4200_, v___f_4201_, v___x_4202_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_);
return v___x_4203_;
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
lean_dec_ref(v_preDefs_4188_);
v_a_4204_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4196_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4196_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getFixedParamPerms___boxed(lean_object* v_preDefs_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(lean_object* v_upperBound_4219_, lean_object* v___x_4220_, lean_object* v___x_4221_, lean_object* v_inst_4222_, lean_object* v_R_4223_, lean_object* v_a_4224_, lean_object* v_b_4225_, lean_object* v_c_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___redArg(v_upperBound_4219_, v___x_4220_, v___x_4221_, v_a_4224_, v_b_4225_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4___boxed(lean_object* v_upperBound_4233_, lean_object* v___x_4234_, lean_object* v___x_4235_, lean_object* v_inst_4236_, lean_object* v_R_4237_, lean_object* v_a_4238_, lean_object* v_b_4239_, lean_object* v_c_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__4(v_upperBound_4233_, v___x_4234_, v___x_4235_, v_inst_4236_, v_R_4237_, v_a_4238_, v_b_4239_, v_c_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec_ref(v___x_4235_);
lean_dec_ref(v___x_4234_);
lean_dec(v_upperBound_4233_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(lean_object* v_upperBound_4247_, lean_object* v_inst_4248_, lean_object* v_R_4249_, lean_object* v_a_4250_, lean_object* v_b_4251_, lean_object* v_c_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___redArg(v_upperBound_4247_, v_a_4250_, v_b_4251_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5___boxed(lean_object* v_upperBound_4259_, lean_object* v_inst_4260_, lean_object* v_R_4261_, lean_object* v_a_4262_, lean_object* v_b_4263_, lean_object* v_c_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamPerms_spec__5(v_upperBound_4259_, v_inst_4260_, v_R_4261_, v_a_4262_, v_b_4263_, v_c_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v_upperBound_4259_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(lean_object* v_as_4271_, size_t v_i_4272_, size_t v_stop_4273_, lean_object* v_b_4274_){
_start:
{
uint8_t v___x_4275_; 
v___x_4275_ = lean_usize_dec_eq(v_i_4272_, v_stop_4273_);
if (v___x_4275_ == 0)
{
size_t v___x_4276_; size_t v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = ((size_t)1ULL);
v___x_4277_ = lean_usize_sub(v_i_4272_, v___x_4276_);
v___x_4278_ = lean_array_uget_borrowed(v_as_4271_, v___x_4277_);
if (lean_obj_tag(v___x_4278_) == 0)
{
v_i_4272_ = v___x_4277_;
goto _start;
}
else
{
lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4280_ = lean_unsigned_to_nat(1u);
v___x_4281_ = lean_nat_add(v_b_4274_, v___x_4280_);
lean_dec(v_b_4274_);
v_i_4272_ = v___x_4277_;
v_b_4274_ = v___x_4281_;
goto _start;
}
}
else
{
return v_b_4274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0___boxed(lean_object* v_as_4283_, lean_object* v_i_4284_, lean_object* v_stop_4285_, lean_object* v_b_4286_){
_start:
{
size_t v_i_boxed_4287_; size_t v_stop_boxed_4288_; lean_object* v_res_4289_; 
v_i_boxed_4287_ = lean_unbox_usize(v_i_4284_);
lean_dec(v_i_4284_);
v_stop_boxed_4288_ = lean_unbox_usize(v_stop_4285_);
lean_dec(v_stop_4285_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_as_4283_, v_i_boxed_4287_, v_stop_boxed_4288_, v_b_4286_);
lean_dec_ref(v_as_4283_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed(lean_object* v_perm_4290_){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_array_get_size(v_perm_4290_);
v___x_4293_ = lean_nat_dec_lt(v___x_4291_, v___x_4292_);
if (v___x_4293_ == 0)
{
return v___x_4291_;
}
else
{
size_t v___x_4294_; size_t v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = lean_usize_of_nat(v___x_4292_);
v___x_4295_ = ((size_t)0ULL);
v___x_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_FixedParamPerm_numFixed_spec__0(v_perm_4290_, v___x_4294_, v___x_4295_, v___x_4291_);
return v___x_4296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_numFixed___boxed(lean_object* v_perm_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4297_);
lean_dec_ref(v_perm_4297_);
return v_res_4298_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_FixedParamPerm_isFixed(lean_object* v_perm_4299_, lean_object* v_i_4300_){
_start:
{
lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4301_ = lean_array_get_size(v_perm_4299_);
v___x_4302_ = lean_nat_dec_lt(v_i_4300_, v___x_4301_);
if (v___x_4302_ == 0)
{
return v___x_4302_;
}
else
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_array_fget_borrowed(v_perm_4299_, v_i_4300_);
if (lean_obj_tag(v___x_4303_) == 0)
{
uint8_t v___x_4304_; 
v___x_4304_ = 0;
return v___x_4304_;
}
else
{
return v___x_4302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_isFixed___boxed(lean_object* v_perm_4305_, lean_object* v_i_4306_){
_start:
{
uint8_t v_res_4307_; lean_object* v_r_4308_; 
v_res_4307_ = l_Lean_Elab_FixedParamPerm_isFixed(v_perm_4305_, v_i_4306_);
lean_dec(v_i_4306_);
lean_dec_ref(v_perm_4305_);
v_r_4308_ = lean_box(v_res_4307_);
return v_r_4308_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(lean_object* v_msg_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___f_4315_; lean_object* v___x_907__overap_4316_; lean_object* v___x_4317_; 
v___f_4315_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_907__overap_4316_ = lean_panic_fn_borrowed(v___f_4315_, v_msg_4309_);
lean_inc(v___y_4313_);
lean_inc_ref(v___y_4312_);
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
v___x_4317_ = lean_apply_5(v___x_907__overap_4316_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, lean_box(0));
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg___boxed(lean_object* v_msg_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(lean_object* v_00_u03b1_4325_, lean_object* v_msg_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v___x_4332_; 
v___x_4332_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v_msg_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
return v___x_4332_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4333_, lean_object* v_msg_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0(v_00_u03b1_4333_, v_msg_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(lean_object* v_type_4341_, lean_object* v_maxFVars_x3f_4342_, lean_object* v_k_4343_, uint8_t v_cleanupAnnotations_4344_, uint8_t v_whnfType_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v___f_4351_; lean_object* v___x_4352_; 
v___f_4351_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4351_, 0, v_k_4343_);
v___x_4352_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4341_, v_maxFVars_x3f_4342_, v___f_4351_, v_cleanupAnnotations_4344_, v_whnfType_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
v_a_4361_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4352_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4352_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg___boxed(lean_object* v_type_4369_, lean_object* v_maxFVars_x3f_4370_, lean_object* v_k_4371_, lean_object* v_cleanupAnnotations_4372_, lean_object* v_whnfType_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4379_; uint8_t v_whnfType_boxed_4380_; lean_object* v_res_4381_; 
v_cleanupAnnotations_boxed_4379_ = lean_unbox(v_cleanupAnnotations_4372_);
v_whnfType_boxed_4380_ = lean_unbox(v_whnfType_4373_);
v_res_4381_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4369_, v_maxFVars_x3f_4370_, v_k_4371_, v_cleanupAnnotations_boxed_4379_, v_whnfType_boxed_4380_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(lean_object* v_00_u03b1_4382_, lean_object* v_type_4383_, lean_object* v_maxFVars_x3f_4384_, lean_object* v_k_4385_, uint8_t v_cleanupAnnotations_4386_, uint8_t v_whnfType_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4383_, v_maxFVars_x3f_4384_, v_k_4385_, v_cleanupAnnotations_4386_, v_whnfType_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___boxed(lean_object* v_00_u03b1_4394_, lean_object* v_type_4395_, lean_object* v_maxFVars_x3f_4396_, lean_object* v_k_4397_, lean_object* v_cleanupAnnotations_4398_, lean_object* v_whnfType_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4405_; uint8_t v_whnfType_boxed_4406_; lean_object* v_res_4407_; 
v_cleanupAnnotations_boxed_4405_ = lean_unbox(v_cleanupAnnotations_4398_);
v_whnfType_boxed_4406_ = lean_unbox(v_whnfType_4399_);
v_res_4407_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1(v_00_u03b1_4394_, v_type_4395_, v_maxFVars_x3f_4396_, v_k_4397_, v_cleanupAnnotations_boxed_4405_, v_whnfType_boxed_4406_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
return v_res_4407_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4410_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__1));
v___x_4411_ = lean_unsigned_to_nat(6u);
v___x_4412_ = lean_unsigned_to_nat(329u);
v___x_4413_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4414_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4415_ = l_mkPanicMessageWithDecl(v___x_4414_, v___x_4413_, v___x_4412_, v___x_4411_, v___x_4410_);
return v___x_4415_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4419_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__0));
v___x_4420_ = lean_unsigned_to_nat(8u);
v___x_4421_ = lean_unsigned_to_nat(322u);
v___x_4422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4423_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4424_ = l_mkPanicMessageWithDecl(v___x_4423_, v___x_4422_, v___x_4421_, v___x_4420_, v___x_4419_);
return v___x_4424_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4426_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4427_ = lean_unsigned_to_nat(8u);
v___x_4428_ = lean_unsigned_to_nat(325u);
v___x_4429_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4430_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4431_ = l_mkPanicMessageWithDecl(v___x_4430_, v___x_4429_, v___x_4428_, v___x_4427_, v___x_4426_);
return v___x_4431_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4433_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__4));
v___x_4434_ = lean_unsigned_to_nat(8u);
v___x_4435_ = lean_unsigned_to_nat(324u);
v___x_4436_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__0));
v___x_4437_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4438_ = l_mkPanicMessageWithDecl(v___x_4437_, v___x_4436_, v___x_4435_, v___x_4434_, v___x_4433_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(lean_object* v___x_4439_, lean_object* v___x_4440_, lean_object* v_xs_4441_, lean_object* v_val_4442_, lean_object* v_i_4443_, lean_object* v_perm_4444_, lean_object* v_k_4445_, lean_object* v_xs_x27_4446_, lean_object* v_type_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; uint8_t v___x_4454_; 
v___x_4453_ = lean_array_get_size(v_xs_x27_4446_);
v___x_4454_ = lean_nat_dec_eq(v___x_4453_, v___x_4439_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; lean_object* v___x_4456_; 
lean_dec_ref(v_type_4447_);
lean_dec_ref(v_k_4445_);
lean_dec_ref(v_perm_4444_);
lean_dec_ref(v_xs_4441_);
v___x_4455_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__1);
v___x_4456_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4455_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
return v___x_4456_;
}
else
{
lean_object* v___x_4457_; lean_object* v_x_4458_; lean_object* v___x_4459_; 
v___x_4457_ = lean_unsigned_to_nat(0u);
v_x_4458_ = lean_array_get_borrowed(v___x_4440_, v_xs_x27_4446_, v___x_4457_);
lean_inc(v___y_4451_);
lean_inc_ref(v___y_4450_);
lean_inc(v___y_4449_);
lean_inc_ref(v___y_4448_);
lean_inc(v_x_4458_);
v___x_4459_ = lean_infer_type(v_x_4458_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; uint8_t v___x_4461_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v___x_4461_ = l_Lean_Expr_hasLooseBVars(v_a_4460_);
lean_dec(v_a_4460_);
if (v___x_4461_ == 0)
{
lean_object* v___x_4462_; uint8_t v___x_4463_; 
v___x_4462_ = lean_array_get_size(v_xs_4441_);
v___x_4463_ = lean_nat_dec_lt(v_val_4442_, v___x_4462_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
lean_dec_ref(v_type_4447_);
lean_dec_ref(v_k_4445_);
lean_dec_ref(v_perm_4444_);
lean_dec_ref(v_xs_4441_);
v___x_4464_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__3);
v___x_4465_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4464_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
return v___x_4465_;
}
else
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4466_ = lean_nat_add(v_i_4443_, v___x_4439_);
lean_inc(v_x_4458_);
v___x_4467_ = lean_array_set(v_xs_4441_, v_val_4442_, v_x_4458_);
v___x_4468_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4444_, v_k_4445_, v___x_4466_, v_type_4447_, v___x_4467_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
return v___x_4468_;
}
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
lean_dec_ref(v_type_4447_);
lean_dec_ref(v_k_4445_);
lean_dec_ref(v_perm_4444_);
lean_dec_ref(v_xs_4441_);
v___x_4469_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__5);
v___x_4470_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4469_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
return v___x_4470_;
}
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec_ref(v_type_4447_);
lean_dec_ref(v_k_4445_);
lean_dec_ref(v_perm_4444_);
lean_dec_ref(v_xs_4441_);
v_a_4471_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4459_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4459_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed(lean_object* v___x_4479_, lean_object* v___x_4480_, lean_object* v_xs_4481_, lean_object* v_val_4482_, lean_object* v_i_4483_, lean_object* v_perm_4484_, lean_object* v_k_4485_, lean_object* v_xs_x27_4486_, lean_object* v_type_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0(v___x_4479_, v___x_4480_, v_xs_4481_, v_val_4482_, v_i_4483_, v_perm_4484_, v_k_4485_, v_xs_x27_4486_, v_type_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec_ref(v_xs_x27_4486_);
lean_dec(v_i_4483_);
lean_dec(v_val_4482_);
lean_dec_ref(v___x_4480_);
lean_dec(v___x_4479_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(lean_object* v_perm_4494_, lean_object* v_k_4495_, lean_object* v_i_4496_, lean_object* v_type_4497_, lean_object* v_xs_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4504_ = lean_array_get_size(v_perm_4494_);
v___x_4505_ = lean_nat_dec_lt(v_i_4496_, v___x_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4506_; 
lean_dec_ref(v_type_4497_);
lean_dec(v_i_4496_);
lean_dec_ref(v_perm_4494_);
lean_inc(v_a_4502_);
lean_inc_ref(v_a_4501_);
lean_inc(v_a_4500_);
lean_inc_ref(v_a_4499_);
v___x_4506_ = lean_apply_6(v_k_4495_, v_xs_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, lean_box(0));
return v___x_4506_;
}
else
{
lean_object* v___x_4507_; 
v___x_4507_ = lean_array_fget_borrowed(v_perm_4494_, v_i_4496_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v___x_4508_; 
lean_inc(v_a_4502_);
lean_inc_ref(v_a_4501_);
lean_inc(v_a_4500_);
lean_inc_ref(v_a_4499_);
v___x_4508_ = lean_whnf(v_type_4497_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
if (lean_obj_tag(v___x_4508_) == 0)
{
lean_object* v_a_4509_; uint8_t v___x_4510_; 
v_a_4509_ = lean_ctor_get(v___x_4508_, 0);
lean_inc(v_a_4509_);
lean_dec_ref_known(v___x_4508_, 1);
v___x_4510_ = l_Lean_Expr_isForall(v_a_4509_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_dec(v_a_4509_);
lean_dec_ref(v_xs_4498_);
lean_dec(v_i_4496_);
lean_dec_ref(v_k_4495_);
lean_dec_ref(v_perm_4494_);
v___x_4511_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__2);
v___x_4512_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__0___redArg(v___x_4511_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
return v___x_4512_;
}
else
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4513_ = lean_unsigned_to_nat(1u);
v___x_4514_ = lean_nat_add(v_i_4496_, v___x_4513_);
lean_dec(v_i_4496_);
v___x_4515_ = l_Lean_Expr_bindingBody_x21(v_a_4509_);
lean_dec(v_a_4509_);
v_i_4496_ = v___x_4514_;
v_type_4497_ = v___x_4515_;
goto _start;
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_dec_ref(v_xs_4498_);
lean_dec(v_i_4496_);
lean_dec_ref(v_k_4495_);
lean_dec_ref(v_perm_4494_);
v_a_4517_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4508_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4508_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
else
{
lean_object* v_val_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___f_4528_; lean_object* v___x_4529_; uint8_t v___x_4530_; lean_object* v___x_4531_; 
v_val_4525_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_val_4525_);
v___x_4526_ = l_Lean_instInhabitedExpr;
v___x_4527_ = lean_unsigned_to_nat(1u);
v___f_4528_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_4528_, 0, v___x_4527_);
lean_closure_set(v___f_4528_, 1, v___x_4526_);
lean_closure_set(v___f_4528_, 2, v_xs_4498_);
lean_closure_set(v___f_4528_, 3, v_val_4525_);
lean_closure_set(v___f_4528_, 4, v_i_4496_);
lean_closure_set(v___f_4528_, 5, v_perm_4494_);
lean_closure_set(v___f_4528_, 6, v_k_4495_);
v___x_4529_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4530_ = 0;
v___x_4531_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_type_4497_, v___x_4529_, v___f_4528_, v___x_4505_, v___x_4530_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
return v___x_4531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___boxed(lean_object* v_perm_4532_, lean_object* v_k_4533_, lean_object* v_i_4534_, lean_object* v_type_4535_, lean_object* v_xs_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4532_, v_k_4533_, v_i_4534_, v_type_4535_, v_xs_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(lean_object* v_00_u03b1_4543_, lean_object* v_perm_4544_, lean_object* v_k_4545_, lean_object* v_i_4546_, lean_object* v_type_4547_, lean_object* v_xs_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4544_, v_k_4545_, v_i_4546_, v_type_4547_, v_xs_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___boxed(lean_object* v_00_u03b1_4555_, lean_object* v_perm_4556_, lean_object* v_k_4557_, lean_object* v_i_4558_, lean_object* v_type_4559_, lean_object* v_xs_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go(v_00_u03b1_4555_, v_perm_4556_, v_k_4557_, v_i_4558_, v_type_4559_, v_xs_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
return v_res_4566_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0(void){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4567_ = lean_unsigned_to_nat(0u);
v___x_4568_ = l_Lean_Level_ofNat(v___x_4567_);
return v___x_4568_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1(void){
_start:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__0);
v___x_4570_ = l_Lean_mkSort(v___x_4569_);
return v___x_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(lean_object* v_perm_4571_, lean_object* v_type_4572_, lean_object* v_k_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4571_);
v___x_4581_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___closed__1);
v___x_4582_ = lean_mk_array(v___x_4580_, v___x_4581_);
v___x_4583_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg(v_perm_4571_, v_k_4573_, v___x_4579_, v_type_4572_, v___x_4582_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_);
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg___boxed(lean_object* v_perm_4584_, lean_object* v_type_4585_, lean_object* v_k_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4584_, v_type_4585_, v_k_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object* v_00_u03b1_4593_, lean_object* v_perm_4594_, lean_object* v_type_4595_, lean_object* v_k_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v___x_4602_; 
v___x_4602_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4594_, v_type_4595_, v_k_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
return v___x_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___boxed(lean_object* v_00_u03b1_4603_, lean_object* v_perm_4604_, lean_object* v_type_4605_, lean_object* v_k_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(v_00_u03b1_4603_, v_perm_4604_, v_type_4605_, v_k_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec_ref(v_a_4607_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(lean_object* v_k_4613_, lean_object* v_runInBase_4614_, lean_object* v_b_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = lean_apply_1(v_k_4613_, v_b_4615_);
lean_inc(v___y_4619_);
lean_inc_ref(v___y_4618_);
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
v___x_4622_ = lean_apply_7(v_runInBase_4614_, lean_box(0), v___x_4621_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, lean_box(0));
return v___x_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed(lean_object* v_k_4623_, lean_object* v_runInBase_4624_, lean_object* v_b_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0(v_k_4623_, v_runInBase_4624_, v_b_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(lean_object* v_k_4632_, lean_object* v_perm_4633_, lean_object* v_type_4634_, lean_object* v_runInBase_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
lean_object* v___f_4641_; lean_object* v___x_4642_; 
v___f_4641_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4641_, 0, v_k_4632_);
lean_closure_set(v___f_4641_, 1, v_runInBase_4635_);
v___x_4642_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___redArg(v_perm_4633_, v_type_4634_, v___f_4641_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed(lean_object* v_k_4643_, lean_object* v_perm_4644_, lean_object* v_type_4645_, lean_object* v_runInBase_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1(v_k_4643_, v_perm_4644_, v_type_4645_, v_runInBase_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(lean_object* v_inst_4653_, lean_object* v_inst_4654_, lean_object* v_perm_4655_, lean_object* v_type_4656_, lean_object* v_k_4657_){
_start:
{
lean_object* v_toBind_4658_; lean_object* v_liftWith_4659_; lean_object* v_restoreM_4660_; lean_object* v___f_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v_toBind_4658_ = lean_ctor_get(v_inst_4654_, 1);
lean_inc(v_toBind_4658_);
lean_dec_ref(v_inst_4654_);
v_liftWith_4659_ = lean_ctor_get(v_inst_4653_, 0);
lean_inc(v_liftWith_4659_);
v_restoreM_4660_ = lean_ctor_get(v_inst_4653_, 1);
lean_inc(v_restoreM_4660_);
lean_dec_ref(v_inst_4653_);
v___f_4661_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4661_, 0, v_k_4657_);
lean_closure_set(v___f_4661_, 1, v_perm_4655_);
lean_closure_set(v___f_4661_, 2, v_type_4656_);
v___x_4662_ = lean_apply_2(v_liftWith_4659_, lean_box(0), v___f_4661_);
v___x_4663_ = lean_apply_1(v_restoreM_4660_, lean_box(0));
v___x_4664_ = lean_apply_4(v_toBind_4658_, lean_box(0), lean_box(0), v___x_4662_, v___x_4663_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope(lean_object* v_n_4665_, lean_object* v_00_u03b1_4666_, lean_object* v_inst_4667_, lean_object* v_inst_4668_, lean_object* v_perm_4669_, lean_object* v_type_4670_, lean_object* v_k_4671_){
_start:
{
lean_object* v___x_4672_; 
v___x_4672_ = l_Lean_Elab_FixedParamPerm_forallTelescope___redArg(v_inst_4667_, v_inst_4668_, v_perm_4669_, v_type_4670_, v_k_4671_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(lean_object* v_msg_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_){
_start:
{
lean_object* v___f_4679_; lean_object* v___x_598__overap_4680_; lean_object* v___x_4681_; 
v___f_4679_ = ((lean_object*)(l_panic___at___00Lean_Elab_getFixedParamsInfo_spec__7___closed__0));
v___x_598__overap_4680_ = lean_panic_fn_borrowed(v___f_4679_, v_msg_4673_);
lean_inc(v___y_4677_);
lean_inc_ref(v___y_4676_);
lean_inc(v___y_4675_);
lean_inc_ref(v___y_4674_);
v___x_4681_ = lean_apply_5(v___x_598__overap_4680_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, lean_box(0));
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0___boxed(lean_object* v_msg_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v_msg_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
return v_res_4688_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4691_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__1));
v___x_4692_ = lean_unsigned_to_nat(10u);
v___x_4693_ = lean_unsigned_to_nat(353u);
v___x_4694_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4696_ = l_mkPanicMessageWithDecl(v___x_4695_, v___x_4694_, v___x_4693_, v___x_4692_, v___x_4691_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed(lean_object* v___x_4697_, lean_object* v_xs_4698_, lean_object* v_tail_4699_, lean_object* v_ys_4700_, lean_object* v_type_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(v___x_4697_, v_xs_4698_, v_tail_4699_, v_ys_4700_, v_type_4701_, v___y_4702_, v___y_4703_, v___y_4704_, v___y_4705_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec_ref(v_ys_4700_);
lean_dec(v___x_4697_);
return v_res_4707_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0(void){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4708_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4709_ = lean_unsigned_to_nat(8u);
v___x_4710_ = lean_unsigned_to_nat(349u);
v___x_4711_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__0));
v___x_4712_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4713_ = l_mkPanicMessageWithDecl(v___x_4712_, v___x_4711_, v___x_4710_, v___x_4709_, v___x_4708_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(lean_object* v_xs_4714_, lean_object* v_x_4715_, lean_object* v_x_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
if (lean_obj_tag(v_x_4715_) == 0)
{
lean_object* v___x_4722_; 
lean_dec_ref(v_xs_4714_);
v___x_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4722_, 0, v_x_4716_);
return v___x_4722_;
}
else
{
lean_object* v_head_4723_; 
v_head_4723_ = lean_ctor_get(v_x_4715_, 0);
if (lean_obj_tag(v_head_4723_) == 0)
{
lean_object* v_tail_4724_; lean_object* v___x_4725_; lean_object* v___f_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; lean_object* v___x_4729_; 
v_tail_4724_ = lean_ctor_get(v_x_4715_, 1);
lean_inc(v_tail_4724_);
lean_dec_ref_known(v_x_4715_, 2);
v___x_4725_ = lean_unsigned_to_nat(1u);
v___f_4726_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4726_, 0, v___x_4725_);
lean_closure_set(v___f_4726_, 1, v_xs_4714_);
lean_closure_set(v___f_4726_, 2, v_tail_4724_);
v___x_4727_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___closed__3));
v___x_4728_ = 0;
v___x_4729_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go_spec__1___redArg(v_x_4716_, v___x_4727_, v___f_4726_, v___x_4728_, v___x_4728_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
return v___x_4729_;
}
else
{
lean_object* v_tail_4730_; lean_object* v_val_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
lean_inc_ref(v_head_4723_);
v_tail_4730_ = lean_ctor_get(v_x_4715_, 1);
lean_inc(v_tail_4730_);
lean_dec_ref_known(v_x_4715_, 2);
v_val_4731_ = lean_ctor_get(v_head_4723_, 0);
lean_inc(v_val_4731_);
lean_dec_ref_known(v_head_4723_, 1);
v___x_4732_ = lean_array_get_size(v_xs_4714_);
v___x_4733_ = lean_nat_dec_lt(v_val_4731_, v___x_4732_);
if (v___x_4733_ == 0)
{
lean_object* v___x_4734_; lean_object* v___x_4735_; 
lean_dec(v_val_4731_);
lean_dec(v_tail_4730_);
lean_dec_ref(v_x_4716_);
lean_dec_ref(v_xs_4714_);
v___x_4734_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___closed__0);
v___x_4735_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4734_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
return v___x_4735_;
}
else
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4736_ = l_Lean_instInhabitedExpr;
v___x_4737_ = lean_array_get_borrowed(v___x_4736_, v_xs_4714_, v_val_4731_);
lean_dec(v_val_4731_);
v___x_4738_ = lean_unsigned_to_nat(1u);
v___x_4739_ = lean_mk_empty_array_with_capacity(v___x_4738_);
lean_inc(v___x_4737_);
v___x_4740_ = lean_array_push(v___x_4739_, v___x_4737_);
v___x_4741_ = l_Lean_Meta_instantiateForall(v_x_4716_, v___x_4740_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
lean_dec_ref(v___x_4740_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4742_);
lean_dec_ref_known(v___x_4741_, 1);
v_x_4715_ = v_tail_4730_;
v_x_4716_ = v_a_4742_;
goto _start;
}
else
{
lean_dec(v_tail_4730_);
lean_dec_ref(v_xs_4714_);
return v___x_4741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0(lean_object* v___x_4744_, lean_object* v_xs_4745_, lean_object* v_tail_4746_, lean_object* v_ys_4747_, lean_object* v_type_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
lean_object* v___x_4754_; uint8_t v___x_4755_; 
v___x_4754_ = lean_array_get_size(v_ys_4747_);
v___x_4755_ = lean_nat_dec_eq(v___x_4754_, v___x_4744_);
if (v___x_4755_ == 0)
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
lean_dec_ref(v_type_4748_);
lean_dec(v_tail_4746_);
lean_dec_ref(v_xs_4745_);
v___x_4756_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___lam__0___closed__2);
v___x_4757_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4756_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
return v___x_4757_;
}
else
{
lean_object* v___x_4758_; 
v___x_4758_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4745_, v_tail_4746_, v_type_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; uint8_t v___x_4760_; uint8_t v___x_4761_; lean_object* v___x_4762_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4759_);
lean_dec_ref_known(v___x_4758_, 1);
v___x_4760_ = 0;
v___x_4761_ = 1;
v___x_4762_ = l_Lean_Meta_mkForallFVars(v_ys_4747_, v_a_4759_, v___x_4760_, v___x_4755_, v___x_4755_, v___x_4761_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
return v___x_4762_;
}
else
{
return v___x_4758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go___boxed(lean_object* v_xs_4763_, lean_object* v_x_4764_, lean_object* v_x_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4763_, v_x_4764_, v_x_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
return v_res_4771_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2(void){
_start:
{
lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4774_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4775_ = lean_unsigned_to_nat(2u);
v___x_4776_ = lean_unsigned_to_nat(343u);
v___x_4777_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__0));
v___x_4778_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4779_ = l_mkPanicMessageWithDecl(v___x_4778_, v___x_4777_, v___x_4776_, v___x_4775_, v___x_4774_);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object* v_perm_4780_, lean_object* v_type_u2080_4781_, lean_object* v_xs_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; 
v___x_4788_ = lean_array_get_size(v_xs_4782_);
v___x_4789_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4780_);
v___x_4790_ = lean_nat_dec_eq(v___x_4788_, v___x_4789_);
lean_dec(v___x_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
lean_dec_ref(v_xs_4782_);
lean_dec_ref(v_type_u2080_4781_);
lean_dec_ref(v_perm_4780_);
v___x_4791_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2, &l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2_once, _init_l_Lean_Elab_FixedParamPerm_instantiateForall___closed__2);
v___x_4792_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4791_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
return v___x_4792_;
}
else
{
lean_object* v_mask_4793_; lean_object* v___x_4794_; 
v_mask_4793_ = lean_array_to_list(v_perm_4780_);
v___x_4794_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go(v_xs_4782_, v_mask_4793_, v_type_u2080_4781_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
return v___x_4794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall___boxed(lean_object* v_perm_4795_, lean_object* v_type_u2080_4796_, lean_object* v_xs_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v_perm_4795_, v_type_u2080_4796_, v_xs_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
lean_dec(v_a_4799_);
lean_dec_ref(v_a_4798_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(lean_object* v_e_4804_, lean_object* v_maxFVars_4805_, lean_object* v_k_4806_, uint8_t v_cleanupAnnotations_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v___f_4813_; uint8_t v___x_4814_; uint8_t v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___f_4813_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_getParamRevDeps_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4813_, 0, v_k_4806_);
v___x_4814_ = 1;
v___x_4815_ = 0;
v___x_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4816_, 0, v_maxFVars_4805_);
v___x_4817_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4804_, v___x_4814_, v___x_4815_, v___x_4814_, v___x_4815_, v___x_4816_, v___f_4813_, v_cleanupAnnotations_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
lean_dec_ref_known(v___x_4816_, 1);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
v_a_4826_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4817_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4817_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg___boxed(lean_object* v_e_4834_, lean_object* v_maxFVars_4835_, lean_object* v_k_4836_, lean_object* v_cleanupAnnotations_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4843_; lean_object* v_res_4844_; 
v_cleanupAnnotations_boxed_4843_ = lean_unbox(v_cleanupAnnotations_4837_);
v_res_4844_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4834_, v_maxFVars_4835_, v_k_4836_, v_cleanupAnnotations_boxed_4843_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(lean_object* v_00_u03b1_4845_, lean_object* v_e_4846_, lean_object* v_maxFVars_4847_, lean_object* v_k_4848_, uint8_t v_cleanupAnnotations_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v___x_4855_; 
v___x_4855_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_e_4846_, v_maxFVars_4847_, v_k_4848_, v_cleanupAnnotations_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___boxed(lean_object* v_00_u03b1_4856_, lean_object* v_e_4857_, lean_object* v_maxFVars_4858_, lean_object* v_k_4859_, lean_object* v_cleanupAnnotations_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4866_; lean_object* v_res_4867_; 
v_cleanupAnnotations_boxed_4866_ = lean_unbox(v_cleanupAnnotations_4860_);
v_res_4867_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1(v_00_u03b1_4856_, v_e_4857_, v_maxFVars_4858_, v_k_4859_, v_cleanupAnnotations_boxed_4866_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
lean_dec(v___y_4864_);
lean_dec_ref(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
return v_res_4867_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(lean_object* v_x_4868_){
_start:
{
if (lean_obj_tag(v_x_4868_) == 0)
{
uint8_t v___x_4869_; 
v___x_4869_ = 1;
return v___x_4869_;
}
else
{
lean_object* v_head_4870_; 
v_head_4870_ = lean_ctor_get(v_x_4868_, 0);
if (lean_obj_tag(v_head_4870_) == 0)
{
lean_object* v_tail_4871_; 
v_tail_4871_ = lean_ctor_get(v_x_4868_, 1);
v_x_4868_ = v_tail_4871_;
goto _start;
}
else
{
uint8_t v___x_4873_; 
v___x_4873_ = 0;
return v___x_4873_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0___boxed(lean_object* v_x_4874_){
_start:
{
uint8_t v_res_4875_; lean_object* v_r_4876_; 
v_res_4875_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_x_4874_);
lean_dec(v_x_4874_);
v_r_4876_ = lean_box(v_res_4875_);
return v_r_4876_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4879_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__1));
v___x_4880_ = lean_unsigned_to_nat(12u);
v___x_4881_ = lean_unsigned_to_nat(376u);
v___x_4882_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4883_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4884_ = l_mkPanicMessageWithDecl(v___x_4883_, v___x_4882_, v___x_4881_, v___x_4880_, v___x_4879_);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed(lean_object* v___x_4885_, lean_object* v_xs_4886_, lean_object* v_tail_4887_, lean_object* v___x_4888_, lean_object* v___x_4889_, lean_object* v_ys_4890_, lean_object* v_value_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
uint8_t v___x_1213__boxed_4897_; uint8_t v___x_1214__boxed_4898_; lean_object* v_res_4899_; 
v___x_1213__boxed_4897_ = lean_unbox(v___x_4888_);
v___x_1214__boxed_4898_ = lean_unbox(v___x_4889_);
v_res_4899_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(v___x_4885_, v_xs_4886_, v_tail_4887_, v___x_1213__boxed_4897_, v___x_1214__boxed_4898_, v_ys_4890_, v_value_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec_ref(v_ys_4890_);
lean_dec(v___x_4885_);
return v_res_4899_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0(void){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4900_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl_go___redArg___lam__0___closed__2));
v___x_4901_ = lean_unsigned_to_nat(8u);
v___x_4902_ = lean_unsigned_to_nat(368u);
v___x_4903_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__0));
v___x_4904_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4905_ = l_mkPanicMessageWithDecl(v___x_4904_, v___x_4903_, v___x_4902_, v___x_4901_, v___x_4900_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(lean_object* v_xs_4906_, lean_object* v_x_4907_, lean_object* v_x_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_){
_start:
{
if (lean_obj_tag(v_x_4907_) == 0)
{
lean_object* v___x_4914_; 
lean_dec_ref(v_xs_4906_);
v___x_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4914_, 0, v_x_4908_);
return v___x_4914_;
}
else
{
lean_object* v_head_4915_; 
v_head_4915_ = lean_ctor_get(v_x_4907_, 0);
if (lean_obj_tag(v_head_4915_) == 0)
{
lean_object* v_tail_4916_; uint8_t v___x_4917_; 
v_tail_4916_ = lean_ctor_get(v_x_4907_, 1);
lean_inc(v_tail_4916_);
lean_dec_ref_known(v_x_4907_, 2);
v___x_4917_ = l_List_all___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__0(v_tail_4916_);
if (v___x_4917_ == 0)
{
uint8_t v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___f_4922_; lean_object* v___x_4923_; 
v___x_4918_ = 1;
v___x_4919_ = lean_unsigned_to_nat(1u);
v___x_4920_ = lean_box(v___x_4917_);
v___x_4921_ = lean_box(v___x_4918_);
v___f_4922_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4922_, 0, v___x_4919_);
lean_closure_set(v___f_4922_, 1, v_xs_4906_);
lean_closure_set(v___f_4922_, 2, v_tail_4916_);
lean_closure_set(v___f_4922_, 3, v___x_4920_);
lean_closure_set(v___f_4922_, 4, v___x_4921_);
v___x_4923_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go_spec__1___redArg(v_x_4908_, v___x_4919_, v___f_4922_, v___x_4917_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_);
return v___x_4923_;
}
else
{
lean_object* v___x_4924_; 
lean_dec(v_tail_4916_);
lean_dec_ref(v_xs_4906_);
v___x_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4924_, 0, v_x_4908_);
return v___x_4924_;
}
}
else
{
lean_object* v_tail_4925_; lean_object* v_val_4926_; lean_object* v___x_4927_; uint8_t v___x_4928_; 
lean_inc_ref(v_head_4915_);
v_tail_4925_ = lean_ctor_get(v_x_4907_, 1);
lean_inc(v_tail_4925_);
lean_dec_ref_known(v_x_4907_, 2);
v_val_4926_ = lean_ctor_get(v_head_4915_, 0);
lean_inc(v_val_4926_);
lean_dec_ref_known(v_head_4915_, 1);
v___x_4927_ = lean_array_get_size(v_xs_4906_);
v___x_4928_ = lean_nat_dec_lt(v_val_4926_, v___x_4927_);
if (v___x_4928_ == 0)
{
lean_object* v___x_4929_; lean_object* v___x_4930_; 
lean_dec(v_val_4926_);
lean_dec(v_tail_4925_);
lean_dec_ref(v_x_4908_);
lean_dec_ref(v_xs_4906_);
v___x_4929_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___closed__0);
v___x_4930_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4929_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_);
return v___x_4930_;
}
else
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4931_ = l_Lean_instInhabitedExpr;
v___x_4932_ = lean_array_get_borrowed(v___x_4931_, v_xs_4906_, v_val_4926_);
lean_dec(v_val_4926_);
v___x_4933_ = lean_unsigned_to_nat(1u);
v___x_4934_ = lean_mk_empty_array_with_capacity(v___x_4933_);
lean_inc(v___x_4932_);
v___x_4935_ = lean_array_push(v___x_4934_, v___x_4932_);
v___x_4936_ = l_Lean_Meta_instantiateLambda(v_x_4908_, v___x_4935_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_);
lean_dec_ref(v___x_4935_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v_x_4907_ = v_tail_4925_;
v_x_4908_ = v_a_4937_;
goto _start;
}
else
{
lean_dec(v_tail_4925_);
lean_dec_ref(v_xs_4906_);
return v___x_4936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0(lean_object* v___x_4939_, lean_object* v_xs_4940_, lean_object* v_tail_4941_, uint8_t v___x_4942_, uint8_t v___x_4943_, lean_object* v_ys_4944_, lean_object* v_value_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
lean_object* v___x_4951_; uint8_t v___x_4952_; 
v___x_4951_ = lean_array_get_size(v_ys_4944_);
v___x_4952_ = lean_nat_dec_eq(v___x_4951_, v___x_4939_);
if (v___x_4952_ == 0)
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
lean_dec_ref(v_value_4945_);
lean_dec(v_tail_4941_);
lean_dec_ref(v_xs_4940_);
v___x_4953_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2, &l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___lam__0___closed__2);
v___x_4954_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4953_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
return v___x_4954_;
}
else
{
lean_object* v___x_4955_; 
v___x_4955_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4940_, v_tail_4941_, v_value_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v_a_4956_; uint8_t v___x_4957_; lean_object* v___x_4958_; 
v_a_4956_ = lean_ctor_get(v___x_4955_, 0);
lean_inc(v_a_4956_);
lean_dec_ref_known(v___x_4955_, 1);
v___x_4957_ = 1;
v___x_4958_ = l_Lean_Meta_mkLambdaFVars(v_ys_4944_, v_a_4956_, v___x_4942_, v___x_4943_, v___x_4942_, v___x_4943_, v___x_4957_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
return v___x_4958_;
}
else
{
return v___x_4955_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go___boxed(lean_object* v_xs_4959_, lean_object* v_x_4960_, lean_object* v_x_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4959_, v_x_4960_, v_x_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
return v_res_4967_;
}
}
static lean_object* _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4969_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateForall___closed__1));
v___x_4970_ = lean_unsigned_to_nat(2u);
v___x_4971_ = lean_unsigned_to_nat(362u);
v___x_4972_ = ((lean_object*)(l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__0));
v___x_4973_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_getFixedParamsInfo_spec__9___redArg___lam__2___closed__0));
v___x_4974_ = l_mkPanicMessageWithDecl(v___x_4973_, v___x_4972_, v___x_4971_, v___x_4970_, v___x_4969_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object* v_perm_4975_, lean_object* v_value_u2080_4976_, lean_object* v_xs_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
v___x_4983_ = lean_array_get_size(v_xs_4977_);
v___x_4984_ = l_Lean_Elab_FixedParamPerm_numFixed(v_perm_4975_);
v___x_4985_ = lean_nat_dec_eq(v___x_4983_, v___x_4984_);
lean_dec(v___x_4984_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
lean_dec_ref(v_xs_4977_);
lean_dec_ref(v_value_u2080_4976_);
lean_dec_ref(v_perm_4975_);
v___x_4986_ = lean_obj_once(&l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1, &l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1_once, _init_l_Lean_Elab_FixedParamPerm_instantiateLambda___closed__1);
v___x_4987_ = l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateForall_go_spec__0(v___x_4986_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
return v___x_4987_;
}
else
{
lean_object* v_mask_4988_; lean_object* v___x_4989_; 
v_mask_4988_ = lean_array_to_list(v_perm_4975_);
v___x_4989_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_instantiateLambda_go(v_xs_4977_, v_mask_4988_, v_value_u2080_4976_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
return v___x_4989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda___boxed(lean_object* v_perm_4990_, lean_object* v_value_u2080_4991_, lean_object* v_xs_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v_perm_4990_, v_value_u2080_4991_, v_xs_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_);
lean_dec(v_a_4996_);
lean_dec_ref(v_a_4995_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
return v_res_4998_;
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
v___x_5017_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
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
v___x_5148_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
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
v___x_5230_ = lean_nat_dec_lt(v___y_5227_, v___y_5229_);
if (v___x_5230_ == 0)
{
lean_dec(v___y_5229_);
lean_dec_ref(v___y_5228_);
lean_dec(v___y_5227_);
lean_dec(v_j_5201_);
lean_dec(v_i_5200_);
return v_xs_5202_;
}
else
{
size_t v___x_5231_; size_t v___x_5232_; uint8_t v___x_5233_; 
v___x_5231_ = lean_usize_of_nat(v___y_5227_);
lean_dec(v___y_5227_);
v___x_5232_ = lean_usize_of_nat(v___y_5229_);
lean_dec(v___y_5229_);
v___x_5233_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_buildArgs_go_spec__1(v_j_5201_, v___x_5225_, v_i_5200_, v___x_5209_, v___y_5228_, v___x_5231_, v___x_5232_);
lean_dec_ref(v___y_5228_);
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
v___y_5227_ = v_start_5241_;
v___y_5228_ = v_array_5240_;
v___y_5229_ = v___x_5244_;
goto v___jp_5226_;
}
else
{
v___y_5227_ = v_start_5241_;
v___y_5228_ = v_array_5240_;
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
lean_object* v___x_5415_; lean_object* v___x_5416_; 
v___x_5415_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5416_, 0, v___x_5415_);
lean_ctor_set(v___x_5416_, 1, v___x_5415_);
return v___x_5416_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0(lean_object* v_msg_5417_){
_start:
{
lean_object* v___f_5418_; lean_object* v___f_5419_; lean_object* v___f_5420_; lean_object* v___f_5421_; lean_object* v___f_5422_; lean_object* v___f_5423_; lean_object* v___f_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___f_5418_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5419_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5420_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5421_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5422_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5423_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5424_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5425_, 0, v___f_5418_);
lean_ctor_set(v___x_5425_, 1, v___f_5419_);
v___x_5426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5425_);
lean_ctor_set(v___x_5426_, 1, v___f_5420_);
lean_ctor_set(v___x_5426_, 2, v___f_5421_);
lean_ctor_set(v___x_5426_, 3, v___f_5422_);
lean_ctor_set(v___x_5426_, 4, v___f_5423_);
v___x_5427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5427_, 0, v___x_5426_);
lean_ctor_set(v___x_5427_, 1, v___f_5424_);
v___x_5428_ = ((lean_object*)(l_Lean_Elab_instInhabitedFixedParamPerms_default));
v___x_5429_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__0___closed__0);
v___x_5430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5430_, 0, v___x_5428_);
lean_ctor_set(v___x_5430_, 1, v___x_5429_);
v___x_5431_ = l_instInhabitedOfMonad___redArg(v___x_5427_, v___x_5430_);
v___x_5432_ = lean_panic_fn_borrowed(v___x_5431_, v_msg_5417_);
lean_dec(v___x_5431_);
return v___x_5432_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5433_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
v___x_5434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5434_, 0, v___x_5433_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3(lean_object* v_msg_5435_){
_start:
{
lean_object* v___f_5436_; lean_object* v___f_5437_; lean_object* v___f_5438_; lean_object* v___f_5439_; lean_object* v___f_5440_; lean_object* v___f_5441_; lean_object* v___f_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___f_5436_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__0));
v___f_5437_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__1));
v___f_5438_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__2));
v___f_5439_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__3));
v___f_5440_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__4));
v___f_5441_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__5));
v___f_5442_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_pickFixed_go_spec__0___redArg___closed__6));
v___x_5443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5443_, 0, v___f_5436_);
lean_ctor_set(v___x_5443_, 1, v___f_5437_);
v___x_5444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5443_);
lean_ctor_set(v___x_5444_, 1, v___f_5438_);
lean_ctor_set(v___x_5444_, 2, v___f_5439_);
lean_ctor_set(v___x_5444_, 3, v___f_5440_);
lean_ctor_set(v___x_5444_, 4, v___f_5441_);
v___x_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___x_5444_);
lean_ctor_set(v___x_5445_, 1, v___f_5442_);
v___x_5446_ = lean_obj_once(&l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0, &l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0_once, _init_l_panic___at___00Lean_Elab_FixedParamPerms_erase_spec__3___closed__0);
v___x_5447_ = l_instInhabitedOfMonad___redArg(v___x_5445_, v___x_5446_);
v___x_5448_ = lean_panic_fn_borrowed(v___x_5447_, v_msg_5435_);
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
uint8_t v___x_7006__boxed_5495_; size_t v_sz_boxed_5496_; size_t v_i_boxed_5497_; lean_object* v_res_5498_; 
v___x_7006__boxed_5495_ = lean_unbox(v___x_5488_);
v_sz_boxed_5496_ = lean_unbox_usize(v_sz_5492_);
lean_dec(v_sz_5492_);
v_i_boxed_5497_ = lean_unbox_usize(v_i_5493_);
lean_dec(v_i_5493_);
v_res_5498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_FixedParamPerms_erase_spec__5(v___x_5487_, v___x_7006__boxed_5495_, v___x_5489_, v___x_5490_, v_as_5491_, v_sz_boxed_5496_, v_i_boxed_5497_, v_b_5494_);
lean_dec_ref(v_as_5491_);
lean_dec(v___x_5490_);
lean_dec(v___x_5489_);
lean_dec_ref(v___x_5487_);
return v_res_5498_;
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
v___x_5528_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
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
v___x_5589_ = lean_obj_once(&l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0, &l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0_once, _init_l_Lean_Elab_FixedParams_Info_mayBeFixed___closed__0);
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
