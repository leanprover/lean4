// Lean compiler output
// Module: Lean.Meta.Sym.Util
// Imports: public import Lean.Meta.Sym.SymM public import Lean.Meta.Transform import Init.Grind.Util import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Lean.Util.ForEachExpr
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Level_isAlreadyNormalizedCheap(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "EqMatch"};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 191, 100, 49, 216, 68, 143, 22)}};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_unfoldReducibleStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducibleStep___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_unfoldReducible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_unfoldReducible___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducible___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_unfoldReducible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_unfoldReducibleStep___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_unfoldReducible___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_unfoldReducible___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "issues"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 90, 109, 68, 195, 255, 174, 185)}};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "found `Expr.proj` with invalid field index `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__9;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found `Expr.proj` but `"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_Sym_foldProjs___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not marked as structure"};
static const lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___lam__0___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Sym_foldProjs___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isProj___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_foldProjs___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__1_value;
static const lean_closure_object l_Lean_Meta_Sym_foldProjs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_foldProjs___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_foldProjs___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_foldProjs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "term is not in the maximally shared table"};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_normalizeLevels___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_normalizeLevels___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_normalizeLevels___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_normalizeLevels___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_normalizeLevels___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_normalizeLevels___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(lean_object* v_declName_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___closed__3));
v___x_10_ = lean_name_eq(v_declName_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget___boxed(lean_object* v_declName_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(v_declName_11_);
lean_dec(v_declName_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(lean_object* v_declName_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; lean_object* v_env_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_17_ = lean_st_ref_get(v___y_15_);
v_env_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_env_18_);
lean_dec(v___x_17_);
v___x_19_ = lean_get_reducibility_status(v_env_18_, v_declName_14_);
v___x_20_ = lean_box(v___x_19_);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg___boxed(lean_object* v_declName_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(v_declName_22_, v___y_23_);
lean_dec(v___y_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0(lean_object* v_declName_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_32_; lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_48_; 
v___x_32_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(v_declName_26_, v___y_30_);
v_a_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_48_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_48_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_48_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
uint8_t v___x_37_; 
v___x_37_ = lean_unbox(v_a_33_);
lean_dec(v_a_33_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_38_ = 1;
v___x_39_ = lean_box(v___x_38_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_39_);
v___x_41_ = v___x_35_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
else
{
uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_43_ = 0;
v___x_44_ = lean_box(v___x_43_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_44_);
v___x_46_ = v___x_35_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0___boxed(lean_object* v_declName_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0(v_declName_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep(lean_object* v_e_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Expr_getAppFn(v_e_58_);
if (lean_obj_tag(v___x_64_) == 4)
{
lean_object* v_declName_65_; lean_object* v___x_66_; 
v_declName_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc_n(v_declName_65_, 2);
lean_dec_ref(v___x_64_);
v___x_66_ = l_Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0(v_declName_65_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_117_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_117_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_117_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_117_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
uint8_t v___x_71_; 
v___x_71_ = lean_unbox(v_a_67_);
lean_dec(v_a_67_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_74_; 
lean_dec(v_declName_65_);
lean_dec_ref(v_e_58_);
v___x_72_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_72_);
v___x_74_ = v___x_69_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(v_declName_65_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v_env_78_; uint8_t v___x_79_; 
v___x_77_ = lean_st_ref_get(v_a_62_);
v_env_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref(v_env_78_);
lean_dec(v___x_77_);
v___x_79_ = l_Lean_Environment_isProjectionFn(v_env_78_, v_declName_65_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_del_object(v___x_69_);
v___x_80_ = l_Lean_Meta_unfoldDefinition_x3f(v_e_58_, v___x_79_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_100_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_100_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_100_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_100_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
if (lean_obj_tag(v_a_81_) == 1)
{
lean_object* v_val_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_95_; 
v_val_85_ = lean_ctor_get(v_a_81_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_a_81_);
if (v_isSharedCheck_95_ == 0)
{
v___x_87_ = v_a_81_;
v_isShared_88_ = v_isSharedCheck_95_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_val_85_);
lean_dec(v_a_81_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_95_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_val_85_);
v___x_90_ = v_reuseFailAlloc_94_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_92_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_90_);
v___x_92_ = v___x_83_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
else
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec(v_a_81_);
v___x_96_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_96_);
v___x_98_ = v___x_83_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v_a_101_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_80_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_80_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_111_; 
lean_dec_ref(v_e_58_);
v___x_109_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_109_);
v___x_111_ = v___x_69_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v___x_113_; lean_object* v___x_115_; 
lean_dec(v_declName_65_);
lean_dec_ref(v_e_58_);
v___x_113_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_113_);
v___x_115_ = v___x_69_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
lean_dec(v_declName_65_);
lean_dec_ref(v_e_58_);
v_a_118_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_66_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_66_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec_ref(v___x_64_);
lean_dec_ref(v_e_58_);
v___x_126_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducibleStep___boxed(lean_object* v_e_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Meta_Sym_unfoldReducibleStep(v_e_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0(lean_object* v_declName_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___redArg(v_declName_135_, v___y_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0___boxed(lean_object* v_declName_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Meta_Sym_unfoldReducibleStep_spec__0_spec__0(v_declName_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
return v_res_148_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(lean_object* v_env_149_, lean_object* v_e_150_){
_start:
{
if (lean_obj_tag(v_e_150_) == 4)
{
lean_object* v_declName_151_; uint8_t v___x_152_; 
v_declName_151_ = lean_ctor_get(v_e_150_, 0);
lean_inc_n(v_declName_151_, 2);
lean_dec_ref(v_e_150_);
lean_inc_ref(v_env_149_);
v___x_152_ = lean_get_reducibility_status(v_env_149_, v_declName_151_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isGrindGadget(v_declName_151_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; 
v___x_154_ = l_Lean_Environment_isProjectionFn(v_env_149_, v_declName_151_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 1;
return v___x_155_;
}
else
{
return v___x_153_;
}
}
else
{
uint8_t v___x_156_; 
lean_dec(v_declName_151_);
lean_dec_ref(v_env_149_);
v___x_156_ = 0;
return v___x_156_;
}
}
else
{
uint8_t v___x_157_; 
lean_dec(v_declName_151_);
lean_dec_ref(v_env_149_);
v___x_157_ = 0;
return v___x_157_;
}
}
else
{
uint8_t v___x_158_; 
lean_dec_ref(v_e_150_);
lean_dec_ref(v_env_149_);
v___x_158_ = 0;
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed(lean_object* v_env_159_, lean_object* v_e_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0(v_env_159_, v_e_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(lean_object* v_e_163_, lean_object* v_a_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_env_167_; lean_object* v___f_168_; lean_object* v___x_169_; 
v___x_166_ = lean_st_ref_get(v_a_164_);
v_env_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_166_);
v___f_168_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_168_, 0, v_env_167_);
v___x_169_ = lean_find_expr(v___f_168_, v_e_163_);
lean_dec_ref(v___f_168_);
if (lean_obj_tag(v___x_169_) == 0)
{
uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = 0;
v___x_171_ = lean_box(v___x_170_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
else
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_181_; 
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v___x_169_, 0);
lean_dec(v_unused_182_);
v___x_174_ = v___x_169_;
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
else
{
lean_dec(v___x_169_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = 1;
v___x_177_ = lean_box(v___x_176_);
if (v_isShared_175_ == 0)
{
lean_ctor_set_tag(v___x_174_, 0);
lean_ctor_set(v___x_174_, 0, v___x_177_);
v___x_179_ = v___x_174_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg___boxed(lean_object* v_e_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_e_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget(lean_object* v_e_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_187_, v_a_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___boxed(lean_object* v_e_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget(v_e_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec_ref(v_e_192_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0(lean_object* v_e_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_e_197_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___lam__0___boxed(lean_object* v_e_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Meta_Sym_unfoldReducible___lam__0(v_e_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_object* v_00_u03b1_212_, lean_object* v_x_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_apply_1(v_x_213_, lean_box(0));
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0___boxed(lean_object* v_00_u03b1_221_, lean_object* v_x_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(v_00_u03b1_221_, v_x_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_228_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
else
{
lean_object* v_key_232_; lean_object* v_tail_233_; uint8_t v___x_234_; 
v_key_232_ = lean_ctor_get(v_x_230_, 0);
v_tail_233_ = lean_ctor_get(v_x_230_, 2);
v___x_234_ = l_Lean_ExprStructEq_beq(v_key_232_, v_a_229_);
if (v___x_234_ == 0)
{
v_x_230_ = v_tail_233_;
goto _start;
}
else
{
return v___x_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_236_, lean_object* v_x_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_236_, v_x_237_);
lean_dec(v_x_237_);
lean_dec_ref(v_a_236_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
return v_x_240_;
}
else
{
lean_object* v_key_242_; lean_object* v_value_243_; lean_object* v_tail_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_267_; 
v_key_242_ = lean_ctor_get(v_x_241_, 0);
v_value_243_ = lean_ctor_get(v_x_241_, 1);
v_tail_244_ = lean_ctor_get(v_x_241_, 2);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_267_ == 0)
{
v___x_246_ = v_x_241_;
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_tail_244_);
lean_inc(v_value_243_);
lean_inc(v_key_242_);
lean_dec(v_x_241_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v_fold_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_248_ = lean_array_get_size(v_x_240_);
v___x_249_ = l_Lean_ExprStructEq_hash(v_key_242_);
v___x_250_ = 32ULL;
v___x_251_ = lean_uint64_shift_right(v___x_249_, v___x_250_);
v_fold_252_ = lean_uint64_xor(v___x_249_, v___x_251_);
v___x_253_ = 16ULL;
v___x_254_ = lean_uint64_shift_right(v_fold_252_, v___x_253_);
v___x_255_ = lean_uint64_xor(v_fold_252_, v___x_254_);
v___x_256_ = lean_uint64_to_usize(v___x_255_);
v___x_257_ = lean_usize_of_nat(v___x_248_);
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_sub(v___x_257_, v___x_258_);
v___x_260_ = lean_usize_land(v___x_256_, v___x_259_);
v___x_261_ = lean_array_uget_borrowed(v_x_240_, v___x_260_);
lean_inc(v___x_261_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 2, v___x_261_);
v___x_263_ = v___x_246_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_key_242_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_value_243_);
lean_ctor_set(v_reuseFailAlloc_266_, 2, v___x_261_);
v___x_263_ = v_reuseFailAlloc_266_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = lean_array_uset(v_x_240_, v___x_260_, v___x_263_);
v_x_240_ = v___x_264_;
v_x_241_ = v_tail_244_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_268_, lean_object* v_source_269_, lean_object* v_target_270_){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_array_get_size(v_source_269_);
v___x_272_ = lean_nat_dec_lt(v_i_268_, v___x_271_);
if (v___x_272_ == 0)
{
lean_dec_ref(v_source_269_);
lean_dec(v_i_268_);
return v_target_270_;
}
else
{
lean_object* v_es_273_; lean_object* v___x_274_; lean_object* v_source_275_; lean_object* v_target_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_es_273_ = lean_array_fget(v_source_269_, v_i_268_);
v___x_274_ = lean_box(0);
v_source_275_ = lean_array_fset(v_source_269_, v_i_268_, v___x_274_);
v_target_276_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_270_, v_es_273_);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_i_268_, v___x_277_);
lean_dec(v_i_268_);
v_i_268_ = v___x_278_;
v_source_269_ = v_source_275_;
v_target_270_ = v_target_276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_nbuckets_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_281_ = lean_array_get_size(v_data_280_);
v___x_282_ = lean_unsigned_to_nat(2u);
v_nbuckets_283_ = lean_nat_mul(v___x_281_, v___x_282_);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_box(0);
v___x_286_ = lean_mk_array(v_nbuckets_283_, v___x_285_);
v___x_287_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_284_, v_data_280_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_288_, lean_object* v_b_289_, lean_object* v_x_290_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_dec(v_b_289_);
lean_dec_ref(v_a_288_);
return v_x_290_;
}
else
{
lean_object* v_key_291_; lean_object* v_value_292_; lean_object* v_tail_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_305_; 
v_key_291_ = lean_ctor_get(v_x_290_, 0);
v_value_292_ = lean_ctor_get(v_x_290_, 1);
v_tail_293_ = lean_ctor_get(v_x_290_, 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_305_ == 0)
{
v___x_295_ = v_x_290_;
v_isShared_296_ = v_isSharedCheck_305_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_tail_293_);
lean_inc(v_value_292_);
lean_inc(v_key_291_);
lean_dec(v_x_290_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_305_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
uint8_t v___x_297_; 
v___x_297_ = l_Lean_ExprStructEq_beq(v_key_291_, v_a_288_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_288_, v_b_289_, v_tail_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 2, v___x_298_);
v___x_300_ = v___x_295_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_key_291_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_value_292_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
else
{
lean_object* v___x_303_; 
lean_dec(v_value_292_);
lean_dec(v_key_291_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v_b_289_);
lean_ctor_set(v___x_295_, 0, v_a_288_);
v___x_303_ = v___x_295_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_288_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_b_289_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_tail_293_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(lean_object* v_m_306_, lean_object* v_a_307_, lean_object* v_b_308_){
_start:
{
lean_object* v_size_309_; lean_object* v_buckets_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_353_; 
v_size_309_ = lean_ctor_get(v_m_306_, 0);
v_buckets_310_ = lean_ctor_get(v_m_306_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_m_306_);
if (v_isSharedCheck_353_ == 0)
{
v___x_312_ = v_m_306_;
v_isShared_313_ = v_isSharedCheck_353_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_buckets_310_);
lean_inc(v_size_309_);
lean_dec(v_m_306_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_353_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v_bkt_327_; uint8_t v___x_328_; 
v___x_314_ = lean_array_get_size(v_buckets_310_);
v___x_315_ = l_Lean_ExprStructEq_hash(v_a_307_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_314_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v_bkt_327_ = lean_array_uget_borrowed(v_buckets_310_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_307_, v_bkt_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v_size_x27_330_; lean_object* v___x_331_; lean_object* v_buckets_x27_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v_size_x27_330_ = lean_nat_add(v_size_309_, v___x_329_);
lean_dec(v_size_309_);
lean_inc(v_bkt_327_);
v___x_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_331_, 0, v_a_307_);
lean_ctor_set(v___x_331_, 1, v_b_308_);
lean_ctor_set(v___x_331_, 2, v_bkt_327_);
v_buckets_x27_332_ = lean_array_uset(v_buckets_310_, v___x_326_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = lean_nat_mul(v_size_x27_330_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(3u);
v___x_336_ = lean_nat_div(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_array_get_size(v_buckets_x27_332_);
v___x_338_ = lean_nat_dec_le(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
if (v___x_338_ == 0)
{
lean_object* v_val_339_; lean_object* v___x_341_; 
v_val_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_332_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_val_339_);
lean_ctor_set(v___x_312_, 0, v_size_x27_330_);
v___x_341_ = v___x_312_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_val_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_buckets_x27_332_);
lean_ctor_set(v___x_312_, 0, v_size_x27_330_);
v___x_344_ = v___x_312_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_buckets_x27_332_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v___x_346_; lean_object* v_buckets_x27_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
lean_inc(v_bkt_327_);
v___x_346_ = lean_box(0);
v_buckets_x27_347_ = lean_array_uset(v_buckets_310_, v___x_326_, v___x_346_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_307_, v_b_308_, v_bkt_327_);
v___x_349_ = lean_array_uset(v_buckets_x27_347_, v___x_326_, v___x_348_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_349_);
v___x_351_ = v___x_312_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_size_309_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(lean_object* v_a_354_, lean_object* v_e_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = lean_st_ref_take(v_a_354_);
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v___x_358_, v_e_355_, v_a_356_);
v___x_360_ = lean_st_ref_set(v_a_354_, v___x_359_);
v___x_361_ = lean_box(0);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed(lean_object* v_a_362_, lean_object* v_e_363_, lean_object* v_a_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2(v_a_362_, v_e_363_, v_a_364_);
lean_dec(v_a_362_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = l_Lean_maxRecDepthErrorMessage;
v___x_373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_375_ = l_Lean_MessageData_ofFormat(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_377_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_378_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_379_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_ref_379_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(lean_object* v_x_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___y_395_; lean_object* v_fileName_404_; lean_object* v_fileMap_405_; lean_object* v_options_406_; lean_object* v_currRecDepth_407_; lean_object* v_maxRecDepth_408_; lean_object* v_ref_409_; lean_object* v_currNamespace_410_; lean_object* v_openDecls_411_; lean_object* v_initHeartbeats_412_; lean_object* v_maxHeartbeats_413_; lean_object* v_quotContext_414_; lean_object* v_currMacroScope_415_; uint8_t v_diag_416_; lean_object* v_cancelTk_x3f_417_; uint8_t v_suppressElabErrors_418_; lean_object* v_inheritedTraceOptions_419_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_fileName_404_ = lean_ctor_get(v___y_391_, 0);
v_fileMap_405_ = lean_ctor_get(v___y_391_, 1);
v_options_406_ = lean_ctor_get(v___y_391_, 2);
v_currRecDepth_407_ = lean_ctor_get(v___y_391_, 3);
v_maxRecDepth_408_ = lean_ctor_get(v___y_391_, 4);
v_ref_409_ = lean_ctor_get(v___y_391_, 5);
v_currNamespace_410_ = lean_ctor_get(v___y_391_, 6);
v_openDecls_411_ = lean_ctor_get(v___y_391_, 7);
v_initHeartbeats_412_ = lean_ctor_get(v___y_391_, 8);
v_maxHeartbeats_413_ = lean_ctor_get(v___y_391_, 9);
v_quotContext_414_ = lean_ctor_get(v___y_391_, 10);
v_currMacroScope_415_ = lean_ctor_get(v___y_391_, 11);
v_diag_416_ = lean_ctor_get_uint8(v___y_391_, sizeof(void*)*14);
v_cancelTk_x3f_417_ = lean_ctor_get(v___y_391_, 12);
v_suppressElabErrors_418_ = lean_ctor_get_uint8(v___y_391_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_419_ = lean_ctor_get(v___y_391_, 13);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_nat_dec_eq(v_maxRecDepth_408_, v___x_425_);
if (v___x_426_ == 0)
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_eq(v_currRecDepth_407_, v_maxRecDepth_408_);
if (v___x_427_ == 0)
{
goto v___jp_420_;
}
else
{
lean_object* v___x_428_; 
lean_dec_ref(v_x_387_);
lean_inc(v_ref_409_);
v___x_428_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_409_);
v___y_395_ = v___x_428_;
goto v___jp_394_;
}
}
else
{
goto v___jp_420_;
}
v___jp_394_:
{
if (lean_obj_tag(v___y_395_) == 0)
{
return v___y_395_;
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_a_396_ = lean_ctor_get(v___y_395_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___y_395_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___y_395_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___y_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
v___jp_420_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_currRecDepth_407_, v___x_421_);
lean_inc_ref(v_inheritedTraceOptions_419_);
lean_inc(v_cancelTk_x3f_417_);
lean_inc(v_currMacroScope_415_);
lean_inc(v_quotContext_414_);
lean_inc(v_maxHeartbeats_413_);
lean_inc(v_initHeartbeats_412_);
lean_inc(v_openDecls_411_);
lean_inc(v_currNamespace_410_);
lean_inc(v_ref_409_);
lean_inc(v_maxRecDepth_408_);
lean_inc_ref(v_options_406_);
lean_inc_ref(v_fileMap_405_);
lean_inc_ref(v_fileName_404_);
v___x_423_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_423_, 0, v_fileName_404_);
lean_ctor_set(v___x_423_, 1, v_fileMap_405_);
lean_ctor_set(v___x_423_, 2, v_options_406_);
lean_ctor_set(v___x_423_, 3, v___x_422_);
lean_ctor_set(v___x_423_, 4, v_maxRecDepth_408_);
lean_ctor_set(v___x_423_, 5, v_ref_409_);
lean_ctor_set(v___x_423_, 6, v_currNamespace_410_);
lean_ctor_set(v___x_423_, 7, v_openDecls_411_);
lean_ctor_set(v___x_423_, 8, v_initHeartbeats_412_);
lean_ctor_set(v___x_423_, 9, v_maxHeartbeats_413_);
lean_ctor_set(v___x_423_, 10, v_quotContext_414_);
lean_ctor_set(v___x_423_, 11, v_currMacroScope_415_);
lean_ctor_set(v___x_423_, 12, v_cancelTk_x3f_417_);
lean_ctor_set(v___x_423_, 13, v_inheritedTraceOptions_419_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*14, v_diag_416_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*14 + 1, v_suppressElabErrors_418_);
lean_inc(v___y_392_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
lean_inc(v___y_388_);
v___x_424_ = lean_apply_6(v_x_387_, v___y_388_, v___y_389_, v___y_390_, v___x_423_, v___y_392_, lean_box(0));
v___y_395_ = v___x_424_;
goto v___jp_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_437_, lean_object* v_x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_apply_1(v_x_438_, lean_box(0));
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(v_00_u03b1_446_, v_x_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_454_, lean_object* v_x_455_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
else
{
lean_object* v_key_457_; lean_object* v_value_458_; lean_object* v_tail_459_; uint8_t v___x_460_; 
v_key_457_ = lean_ctor_get(v_x_455_, 0);
v_value_458_ = lean_ctor_get(v_x_455_, 1);
v_tail_459_ = lean_ctor_get(v_x_455_, 2);
v___x_460_ = l_Lean_ExprStructEq_beq(v_key_457_, v_a_454_);
if (v___x_460_ == 0)
{
v_x_455_ = v_tail_459_;
goto _start;
}
else
{
lean_object* v___x_462_; 
lean_inc(v_value_458_);
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v_value_458_);
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec_ref(v_a_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(lean_object* v_m_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_buckets_468_; lean_object* v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v_fold_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_buckets_468_ = lean_ctor_get(v_m_466_, 1);
v___x_469_ = lean_array_get_size(v_buckets_468_);
v___x_470_ = l_Lean_ExprStructEq_hash(v_a_467_);
v___x_471_ = 32ULL;
v___x_472_ = lean_uint64_shift_right(v___x_470_, v___x_471_);
v_fold_473_ = lean_uint64_xor(v___x_470_, v___x_472_);
v___x_474_ = 16ULL;
v___x_475_ = lean_uint64_shift_right(v_fold_473_, v___x_474_);
v___x_476_ = lean_uint64_xor(v_fold_473_, v___x_475_);
v___x_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = lean_usize_of_nat(v___x_469_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_sub(v___x_478_, v___x_479_);
v___x_481_ = lean_usize_land(v___x_477_, v___x_480_);
v___x_482_ = lean_array_uget_borrowed(v_buckets_468_, v___x_481_);
v___x_483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_467_, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_484_, v_a_485_);
lean_dec_ref(v_a_485_);
lean_dec_ref(v_m_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_487_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2(v___x_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_501_, lean_object* v___y_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; 
lean_inc(v___y_507_);
lean_inc_ref(v___y_506_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_502_);
v___x_509_ = lean_apply_7(v_k_501_, v_b_503_, v___y_502_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, lean_box(0));
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_510_, lean_object* v___y_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_510_, v___y_511_, v_b_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_511_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_519_, uint8_t v_bi_520_, lean_object* v_type_521_, lean_object* v_k_522_, uint8_t v_kind_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___f_530_; lean_object* v___x_531_; 
lean_inc(v___y_524_);
v___f_530_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_530_, 0, v_k_522_);
lean_closure_set(v___f_530_, 1, v___y_524_);
v___x_531_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_519_, v_bi_520_, v_type_521_, v___f_530_, v_kind_523_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_531_) == 0)
{
return v___x_531_;
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_540_, lean_object* v_bi_541_, lean_object* v_type_542_, lean_object* v_k_543_, lean_object* v_kind_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v_bi_boxed_551_; uint8_t v_kind_boxed_552_; lean_object* v_res_553_; 
v_bi_boxed_551_ = lean_unbox(v_bi_541_);
v_kind_boxed_552_ = lean_unbox(v_kind_544_);
v_res_553_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_540_, v_bi_boxed_551_, v_type_542_, v_k_543_, v_kind_boxed_552_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_554_, lean_object* v_type_555_, lean_object* v_val_556_, lean_object* v_k_557_, uint8_t v_nondep_558_, uint8_t v_kind_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___f_566_; lean_object* v___x_567_; 
lean_inc(v___y_560_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_566_, 0, v_k_557_);
lean_closure_set(v___f_566_, 1, v___y_560_);
v___x_567_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_554_, v_type_555_, v_val_556_, v___f_566_, v_nondep_558_, v_kind_559_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_567_) == 0)
{
return v___x_567_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_576_, lean_object* v_type_577_, lean_object* v_val_578_, lean_object* v_k_579_, lean_object* v_nondep_580_, lean_object* v_kind_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v_nondep_boxed_588_; uint8_t v_kind_boxed_589_; lean_object* v_res_590_; 
v_nondep_boxed_588_ = lean_unbox(v_nondep_580_);
v_kind_boxed_589_ = lean_unbox(v_kind_581_);
v_res_590_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_576_, v_type_577_, v_val_578_, v_k_579_, v_nondep_boxed_588_, v_kind_boxed_589_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_594_, lean_object* v_pre_595_, lean_object* v_post_596_, uint8_t v_usedLetOnly_597_, uint8_t v_skipConstInApp_598_, uint8_t v_skipInstances_599_, lean_object* v_body_600_, lean_object* v_x_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_array_push(v_fvars_594_, v_x_601_);
v___x_609_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_595_, v_post_596_, v_usedLetOnly_597_, v_skipConstInApp_598_, v_skipInstances_599_, v___x_608_, v_body_600_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_610_, lean_object* v_pre_611_, lean_object* v_post_612_, lean_object* v_usedLetOnly_613_, lean_object* v_skipConstInApp_614_, lean_object* v_skipInstances_615_, lean_object* v_body_616_, lean_object* v_x_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
uint8_t v_usedLetOnly_boxed_624_; uint8_t v_skipConstInApp_boxed_625_; uint8_t v_skipInstances_boxed_626_; lean_object* v_res_627_; 
v_usedLetOnly_boxed_624_ = lean_unbox(v_usedLetOnly_613_);
v_skipConstInApp_boxed_625_ = lean_unbox(v_skipConstInApp_614_);
v_skipInstances_boxed_626_ = lean_unbox(v_skipInstances_615_);
v_res_627_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0(v_fvars_610_, v_pre_611_, v_post_612_, v_usedLetOnly_boxed_624_, v_skipConstInApp_boxed_625_, v_skipInstances_boxed_626_, v_body_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(lean_object* v_pre_628_, lean_object* v_post_629_, uint8_t v_usedLetOnly_630_, uint8_t v_skipConstInApp_631_, uint8_t v_skipInstances_632_, lean_object* v_e_633_, lean_object* v_a_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; 
lean_inc_ref(v_post_629_);
lean_inc(v___y_638_);
lean_inc_ref(v___y_637_);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc_ref(v_e_633_);
v___x_640_ = lean_apply_6(v_post_629_, v_e_633_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, lean_box(0));
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_659_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_659_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_659_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_659_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
switch(lean_obj_tag(v_a_641_))
{
case 0:
{
lean_object* v_e_645_; lean_object* v___x_647_; 
lean_dec_ref(v_e_633_);
lean_dec_ref(v_post_629_);
lean_dec_ref(v_pre_628_);
v_e_645_ = lean_ctor_get(v_a_641_, 0);
lean_inc_ref(v_e_645_);
lean_dec_ref(v_a_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_e_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_e_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
case 1:
{
lean_object* v_e_649_; lean_object* v___x_650_; 
lean_del_object(v___x_643_);
lean_dec_ref(v_e_633_);
v_e_649_ = lean_ctor_get(v_a_641_, 0);
lean_inc_ref(v_e_649_);
lean_dec_ref(v_a_641_);
v___x_650_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_628_, v_post_629_, v_usedLetOnly_630_, v_skipConstInApp_631_, v_skipInstances_632_, v_e_649_, v_a_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_650_;
}
default: 
{
lean_object* v_e_x3f_651_; 
lean_dec_ref(v_post_629_);
lean_dec_ref(v_pre_628_);
v_e_x3f_651_ = lean_ctor_get(v_a_641_, 0);
lean_inc(v_e_x3f_651_);
lean_dec_ref(v_a_641_);
if (lean_obj_tag(v_e_x3f_651_) == 0)
{
lean_object* v___x_653_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_e_633_);
v___x_653_ = v___x_643_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_e_633_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v_val_655_; lean_object* v___x_657_; 
lean_dec_ref(v_e_633_);
v_val_655_ = lean_ctor_get(v_e_x3f_651_, 0);
lean_inc(v_val_655_);
lean_dec_ref(v_e_x3f_651_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_val_655_);
v___x_657_ = v___x_643_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_val_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_e_633_);
lean_dec_ref(v_post_629_);
lean_dec_ref(v_pre_628_);
v_a_660_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_640_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_640_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(lean_object* v_pre_668_, lean_object* v_post_669_, uint8_t v_usedLetOnly_670_, uint8_t v_skipConstInApp_671_, uint8_t v_skipInstances_672_, lean_object* v_fvars_673_, lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
if (lean_obj_tag(v_e_674_) == 6)
{
lean_object* v_binderName_681_; lean_object* v_binderType_682_; lean_object* v_body_683_; uint8_t v_binderInfo_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_binderName_681_ = lean_ctor_get(v_e_674_, 0);
lean_inc(v_binderName_681_);
v_binderType_682_ = lean_ctor_get(v_e_674_, 1);
lean_inc_ref(v_binderType_682_);
v_body_683_ = lean_ctor_get(v_e_674_, 2);
lean_inc_ref(v_body_683_);
v_binderInfo_684_ = lean_ctor_get_uint8(v_e_674_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_674_);
v___x_685_ = lean_expr_instantiate_rev(v_binderType_682_, v_fvars_673_);
lean_dec_ref(v_binderType_682_);
lean_inc_ref(v_post_669_);
lean_inc_ref(v_pre_668_);
v___x_686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_668_, v_post_669_, v_usedLetOnly_670_, v_skipConstInApp_671_, v_skipInstances_672_, v___x_685_, v_a_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___f_691_; uint8_t v___x_692_; lean_object* v___x_693_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref(v___x_686_);
v___x_688_ = lean_box(v_usedLetOnly_670_);
v___x_689_ = lean_box(v_skipConstInApp_671_);
v___x_690_ = lean_box(v_skipInstances_672_);
v___f_691_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_691_, 0, v_fvars_673_);
lean_closure_set(v___f_691_, 1, v_pre_668_);
lean_closure_set(v___f_691_, 2, v_post_669_);
lean_closure_set(v___f_691_, 3, v___x_688_);
lean_closure_set(v___f_691_, 4, v___x_689_);
lean_closure_set(v___f_691_, 5, v___x_690_);
lean_closure_set(v___f_691_, 6, v_body_683_);
v___x_692_ = 0;
v___x_693_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_681_, v_binderInfo_684_, v_a_687_, v___f_691_, v___x_692_, v_a_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
return v___x_693_;
}
else
{
lean_dec_ref(v_body_683_);
lean_dec(v_binderName_681_);
lean_dec_ref(v_fvars_673_);
lean_dec_ref(v_post_669_);
lean_dec_ref(v_pre_668_);
return v___x_686_;
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_expr_instantiate_rev(v_e_674_, v_fvars_673_);
lean_dec_ref(v_e_674_);
lean_inc_ref(v_post_669_);
lean_inc_ref(v_pre_668_);
v___x_695_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_668_, v_post_669_, v_usedLetOnly_670_, v_skipConstInApp_671_, v_skipInstances_672_, v___x_694_, v_a_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; uint8_t v___x_697_; uint8_t v___x_698_; uint8_t v___x_699_; lean_object* v___x_700_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
v___x_697_ = 0;
v___x_698_ = 1;
v___x_699_ = 1;
v___x_700_ = l_Lean_Meta_mkLambdaFVars(v_fvars_673_, v_a_696_, v___x_697_, v_usedLetOnly_670_, v___x_697_, v___x_698_, v___x_699_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec_ref(v_fvars_673_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref(v___x_700_);
v___x_702_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_668_, v_post_669_, v_usedLetOnly_670_, v_skipConstInApp_671_, v_skipInstances_672_, v_a_701_, v_a_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
return v___x_702_;
}
else
{
lean_dec_ref(v_post_669_);
lean_dec_ref(v_pre_668_);
return v___x_700_;
}
}
else
{
lean_dec_ref(v_fvars_673_);
lean_dec_ref(v_post_669_);
lean_dec_ref(v_pre_668_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_703_, lean_object* v_pre_704_, lean_object* v_post_705_, uint8_t v_usedLetOnly_706_, uint8_t v_skipConstInApp_707_, uint8_t v_skipInstances_708_, lean_object* v_body_709_, lean_object* v_x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_array_push(v_fvars_703_, v_x_710_);
v___x_718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_704_, v_post_705_, v_usedLetOnly_706_, v_skipConstInApp_707_, v_skipInstances_708_, v___x_717_, v_body_709_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_719_, lean_object* v_pre_720_, lean_object* v_post_721_, lean_object* v_usedLetOnly_722_, lean_object* v_skipConstInApp_723_, lean_object* v_skipInstances_724_, lean_object* v_body_725_, lean_object* v_x_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v_usedLetOnly_boxed_733_; uint8_t v_skipConstInApp_boxed_734_; uint8_t v_skipInstances_boxed_735_; lean_object* v_res_736_; 
v_usedLetOnly_boxed_733_ = lean_unbox(v_usedLetOnly_722_);
v_skipConstInApp_boxed_734_ = lean_unbox(v_skipConstInApp_723_);
v_skipInstances_boxed_735_ = lean_unbox(v_skipInstances_724_);
v_res_736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0(v_fvars_719_, v_pre_720_, v_post_721_, v_usedLetOnly_boxed_733_, v_skipConstInApp_boxed_734_, v_skipInstances_boxed_735_, v_body_725_, v_x_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(lean_object* v_pre_737_, lean_object* v_post_738_, uint8_t v_usedLetOnly_739_, uint8_t v_skipConstInApp_740_, uint8_t v_skipInstances_741_, lean_object* v_fvars_742_, lean_object* v_e_743_, lean_object* v_a_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
if (lean_obj_tag(v_e_743_) == 8)
{
lean_object* v_declName_750_; lean_object* v_type_751_; lean_object* v_value_752_; lean_object* v_body_753_; uint8_t v_nondep_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_declName_750_ = lean_ctor_get(v_e_743_, 0);
lean_inc(v_declName_750_);
v_type_751_ = lean_ctor_get(v_e_743_, 1);
lean_inc_ref(v_type_751_);
v_value_752_ = lean_ctor_get(v_e_743_, 2);
lean_inc_ref(v_value_752_);
v_body_753_ = lean_ctor_get(v_e_743_, 3);
lean_inc_ref(v_body_753_);
v_nondep_754_ = lean_ctor_get_uint8(v_e_743_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_743_);
v___x_755_ = lean_expr_instantiate_rev(v_type_751_, v_fvars_742_);
lean_dec_ref(v_type_751_);
lean_inc_ref(v_post_738_);
lean_inc_ref(v_pre_737_);
v___x_756_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_737_, v_post_738_, v_usedLetOnly_739_, v_skipConstInApp_740_, v_skipInstances_741_, v___x_755_, v_a_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref(v___x_756_);
v___x_758_ = lean_expr_instantiate_rev(v_value_752_, v_fvars_742_);
lean_dec_ref(v_value_752_);
lean_inc_ref(v_post_738_);
lean_inc_ref(v_pre_737_);
v___x_759_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_737_, v_post_738_, v_usedLetOnly_739_, v_skipConstInApp_740_, v_skipInstances_741_, v___x_758_, v_a_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___f_764_; uint8_t v___x_765_; lean_object* v___x_766_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
v___x_761_ = lean_box(v_usedLetOnly_739_);
v___x_762_ = lean_box(v_skipConstInApp_740_);
v___x_763_ = lean_box(v_skipInstances_741_);
v___f_764_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_764_, 0, v_fvars_742_);
lean_closure_set(v___f_764_, 1, v_pre_737_);
lean_closure_set(v___f_764_, 2, v_post_738_);
lean_closure_set(v___f_764_, 3, v___x_761_);
lean_closure_set(v___f_764_, 4, v___x_762_);
lean_closure_set(v___f_764_, 5, v___x_763_);
lean_closure_set(v___f_764_, 6, v_body_753_);
v___x_765_ = 0;
v___x_766_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_750_, v_a_757_, v_a_760_, v___f_764_, v_nondep_754_, v___x_765_, v_a_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
return v___x_766_;
}
else
{
lean_dec(v_a_757_);
lean_dec_ref(v_body_753_);
lean_dec(v_declName_750_);
lean_dec_ref(v_fvars_742_);
lean_dec_ref(v_post_738_);
lean_dec_ref(v_pre_737_);
return v___x_759_;
}
}
else
{
lean_dec_ref(v_body_753_);
lean_dec_ref(v_value_752_);
lean_dec(v_declName_750_);
lean_dec_ref(v_fvars_742_);
lean_dec_ref(v_post_738_);
lean_dec_ref(v_pre_737_);
return v___x_756_;
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_expr_instantiate_rev(v_e_743_, v_fvars_742_);
lean_dec_ref(v_e_743_);
lean_inc_ref(v_post_738_);
lean_inc_ref(v_pre_737_);
v___x_768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_737_, v_post_738_, v_usedLetOnly_739_, v_skipConstInApp_740_, v_skipInstances_741_, v___x_767_, v_a_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; uint8_t v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v___x_770_ = 0;
v___x_771_ = 1;
v___x_772_ = l_Lean_Meta_mkLetFVars(v_fvars_742_, v_a_769_, v_usedLetOnly_739_, v___x_770_, v___x_771_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec_ref(v_fvars_742_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v___x_774_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_737_, v_post_738_, v_usedLetOnly_739_, v_skipConstInApp_740_, v_skipInstances_741_, v_a_773_, v_a_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
return v___x_774_;
}
else
{
lean_dec_ref(v_post_738_);
lean_dec_ref(v_pre_737_);
return v___x_772_;
}
}
else
{
lean_dec_ref(v_fvars_742_);
lean_dec_ref(v_post_738_);
lean_dec_ref(v_pre_737_);
return v___x_768_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_775_; lean_object* v_dummy_776_; 
v___x_775_ = lean_box(0);
v_dummy_776_ = l_Lean_Expr_sort___override(v___x_775_);
return v_dummy_776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(lean_object* v_pre_777_, lean_object* v_post_778_, uint8_t v_usedLetOnly_779_, uint8_t v_skipConstInApp_780_, uint8_t v_skipInstances_781_, size_t v_sz_782_, size_t v_i_783_, lean_object* v_bs_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_usize_dec_lt(v_i_783_, v_sz_782_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec_ref(v_post_778_);
lean_dec_ref(v_pre_777_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_bs_784_);
return v___x_792_;
}
else
{
lean_object* v_v_793_; lean_object* v___x_794_; 
v_v_793_ = lean_array_uget_borrowed(v_bs_784_, v_i_783_);
lean_inc(v_v_793_);
lean_inc_ref(v_post_778_);
lean_inc_ref(v_pre_777_);
v___x_794_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_777_, v_post_778_, v_usedLetOnly_779_, v_skipConstInApp_780_, v_skipInstances_781_, v_v_793_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v_bs_x27_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_796_ = lean_unsigned_to_nat(0u);
v_bs_x27_797_ = lean_array_uset(v_bs_784_, v_i_783_, v___x_796_);
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_i_783_, v___x_798_);
v___x_800_ = lean_array_uset(v_bs_x27_797_, v_i_783_, v_a_795_);
v_i_783_ = v___x_799_;
v_bs_784_ = v___x_800_;
goto _start;
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_bs_784_);
lean_dec_ref(v_post_778_);
lean_dec_ref(v_pre_777_);
v_a_802_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_794_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_794_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_810_, lean_object* v_post_811_, uint8_t v_usedLetOnly_812_, uint8_t v_skipConstInApp_813_, uint8_t v_skipInstances_814_, lean_object* v___x_815_, lean_object* v___y_816_, lean_object* v_b_817_, lean_object* v_a_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_810_, v_post_811_, v_usedLetOnly_812_, v_skipConstInApp_813_, v_skipInstances_814_, v___x_815_, v___y_816_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_834_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_834_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_834_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_834_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_829_ = lean_array_fset(v_b_817_, v_a_818_, v_a_825_);
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_830_);
v___x_832_ = v___x_827_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v_b_817_);
v_a_835_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_824_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_824_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_843_, lean_object* v_post_844_, lean_object* v_usedLetOnly_845_, lean_object* v_skipConstInApp_846_, lean_object* v_skipInstances_847_, lean_object* v___x_848_, lean_object* v___y_849_, lean_object* v_b_850_, lean_object* v_a_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v_usedLetOnly_boxed_857_; uint8_t v_skipConstInApp_boxed_858_; uint8_t v_skipInstances_boxed_859_; lean_object* v_res_860_; 
v_usedLetOnly_boxed_857_ = lean_unbox(v_usedLetOnly_845_);
v_skipConstInApp_boxed_858_ = lean_unbox(v_skipConstInApp_846_);
v_skipInstances_boxed_859_ = lean_unbox(v_skipInstances_847_);
v_res_860_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_843_, v_post_844_, v_usedLetOnly_boxed_857_, v_skipConstInApp_boxed_858_, v_skipInstances_boxed_859_, v___x_848_, v___y_849_, v_b_850_, v_a_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v_a_851_);
lean_dec(v___y_849_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_861_, lean_object* v___x_862_, lean_object* v_pre_863_, lean_object* v_post_864_, uint8_t v_usedLetOnly_865_, uint8_t v_skipConstInApp_866_, uint8_t v_skipInstances_867_, lean_object* v_a_868_, lean_object* v_b_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___y_877_; uint8_t v___x_900_; 
v___x_900_ = lean_nat_dec_lt(v_a_868_, v_upperBound_861_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v_a_868_);
lean_dec_ref(v_post_864_);
lean_dec_ref(v_pre_863_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_b_869_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_array_fget_borrowed(v_b_869_, v_a_868_);
v___x_903_ = lean_array_get_size(v___x_862_);
v___x_904_ = lean_nat_dec_lt(v_a_868_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; 
lean_inc(v___x_902_);
v___x_905_ = lean_box(v_usedLetOnly_865_);
v___x_906_ = lean_box(v_skipConstInApp_866_);
v___x_907_ = lean_box(v_skipInstances_867_);
lean_inc(v_a_868_);
lean_inc(v___y_870_);
lean_inc_ref(v_post_864_);
lean_inc_ref(v_pre_863_);
v___f_908_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_908_, 0, v_pre_863_);
lean_closure_set(v___f_908_, 1, v_post_864_);
lean_closure_set(v___f_908_, 2, v___x_905_);
lean_closure_set(v___f_908_, 3, v___x_906_);
lean_closure_set(v___f_908_, 4, v___x_907_);
lean_closure_set(v___f_908_, 5, v___x_902_);
lean_closure_set(v___f_908_, 6, v___y_870_);
lean_closure_set(v___f_908_, 7, v_b_869_);
lean_closure_set(v___f_908_, 8, v_a_868_);
v___y_877_ = v___f_908_;
goto v___jp_876_;
}
else
{
lean_object* v___x_909_; uint8_t v_isInstance_910_; 
v___x_909_ = lean_array_fget_borrowed(v___x_862_, v_a_868_);
v_isInstance_910_ = lean_ctor_get_uint8(v___x_909_, sizeof(void*)*1 + 4);
if (v_isInstance_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___f_914_; 
lean_inc(v___x_902_);
v___x_911_ = lean_box(v_usedLetOnly_865_);
v___x_912_ = lean_box(v_skipConstInApp_866_);
v___x_913_ = lean_box(v_skipInstances_867_);
lean_inc(v_a_868_);
lean_inc(v___y_870_);
lean_inc_ref(v_post_864_);
lean_inc_ref(v_pre_863_);
v___f_914_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_914_, 0, v_pre_863_);
lean_closure_set(v___f_914_, 1, v_post_864_);
lean_closure_set(v___f_914_, 2, v___x_911_);
lean_closure_set(v___f_914_, 3, v___x_912_);
lean_closure_set(v___f_914_, 4, v___x_913_);
lean_closure_set(v___f_914_, 5, v___x_902_);
lean_closure_set(v___f_914_, 6, v___y_870_);
lean_closure_set(v___f_914_, 7, v_b_869_);
lean_closure_set(v___f_914_, 8, v_a_868_);
v___y_877_ = v___f_914_;
goto v___jp_876_;
}
else
{
lean_object* v___x_915_; lean_object* v___f_916_; 
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v_b_869_);
v___f_916_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_916_, 0, v___x_915_);
v___y_877_ = v___f_916_;
goto v___jp_876_;
}
}
}
v___jp_876_:
{
lean_object* v___x_878_; 
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
lean_inc(v___y_872_);
lean_inc_ref(v___y_871_);
v___x_878_ = lean_apply_5(v___y_877_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, lean_box(0));
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_891_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_891_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_891_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
if (lean_obj_tag(v_a_879_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; 
lean_dec(v_a_868_);
lean_dec_ref(v_post_864_);
lean_dec_ref(v_pre_863_);
v_a_883_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v_a_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_a_883_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_del_object(v___x_881_);
v_a_887_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v_a_879_);
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_add(v_a_868_, v___x_888_);
lean_dec(v_a_868_);
v_a_868_ = v___x_889_;
v_b_869_ = v_a_887_;
goto _start;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_a_868_);
lean_dec_ref(v_post_864_);
lean_dec_ref(v_pre_863_);
v_a_892_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_878_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_878_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(uint8_t v_skipInstances_917_, lean_object* v_pre_918_, lean_object* v_post_919_, uint8_t v_usedLetOnly_920_, uint8_t v_skipConstInApp_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_x_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_f_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; 
if (lean_obj_tag(v_x_922_) == 5)
{
lean_object* v_fn_980_; lean_object* v_arg_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_fn_980_ = lean_ctor_get(v_x_922_, 0);
lean_inc_ref(v_fn_980_);
v_arg_981_ = lean_ctor_get(v_x_922_, 1);
lean_inc_ref(v_arg_981_);
lean_dec_ref(v_x_922_);
v___x_982_ = lean_array_set(v_x_923_, v_x_924_, v_arg_981_);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_sub(v_x_924_, v___x_983_);
lean_dec(v_x_924_);
v_x_922_ = v_fn_980_;
v_x_923_ = v___x_982_;
v_x_924_ = v___x_984_;
goto _start;
}
else
{
lean_dec(v_x_924_);
if (v_skipConstInApp_921_ == 0)
{
goto v___jp_977_;
}
else
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_Expr_isConst(v_x_922_);
if (v___x_986_ == 0)
{
goto v___jp_977_;
}
else
{
v_f_932_ = v_x_922_;
v___y_933_ = v___y_925_;
v___y_934_ = v___y_926_;
v___y_935_ = v___y_927_;
v___y_936_ = v___y_928_;
v___y_937_ = v___y_929_;
goto v___jp_931_;
}
}
}
v___jp_931_:
{
if (v_skipInstances_917_ == 0)
{
size_t v_sz_938_; size_t v___x_939_; lean_object* v___x_940_; 
v_sz_938_ = lean_array_size(v_x_923_);
v___x_939_ = ((size_t)0ULL);
lean_inc_ref(v_post_919_);
lean_inc_ref(v_pre_918_);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_918_, v_post_919_, v_usedLetOnly_920_, v_skipConstInApp_921_, v_skipInstances_917_, v_sz_938_, v___x_939_, v_x_923_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref(v___x_940_);
v___x_942_ = l_Lean_mkAppN(v_f_932_, v_a_941_);
lean_dec(v_a_941_);
v___x_943_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_918_, v_post_919_, v_usedLetOnly_920_, v_skipConstInApp_921_, v_skipInstances_917_, v___x_942_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_943_;
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v_f_932_);
lean_dec_ref(v_post_919_);
lean_dec_ref(v_pre_918_);
v_a_944_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_940_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_940_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_array_get_size(v_x_923_);
lean_inc_ref(v_f_932_);
v___x_953_ = l_Lean_Meta_getFunInfoNArgs(v_f_932_, v___x_952_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_paramInfo_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref(v___x_953_);
v_paramInfo_955_ = lean_ctor_get(v_a_954_, 0);
lean_inc_ref(v_paramInfo_955_);
lean_dec(v_a_954_);
v___x_956_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_919_);
lean_inc_ref(v_pre_918_);
v___x_957_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v___x_952_, v_paramInfo_955_, v_pre_918_, v_post_919_, v_usedLetOnly_920_, v_skipConstInApp_921_, v_skipInstances_917_, v___x_956_, v_x_923_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v_paramInfo_955_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref(v___x_957_);
v___x_959_ = l_Lean_mkAppN(v_f_932_, v_a_958_);
lean_dec(v_a_958_);
v___x_960_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_918_, v_post_919_, v_usedLetOnly_920_, v_skipConstInApp_921_, v_skipInstances_917_, v___x_959_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_960_;
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v_f_932_);
lean_dec_ref(v_post_919_);
lean_dec_ref(v_pre_918_);
v_a_961_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_957_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_957_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_f_932_);
lean_dec_ref(v_x_923_);
lean_dec_ref(v_post_919_);
lean_dec_ref(v_pre_918_);
v_a_969_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_953_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_953_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
v___jp_977_:
{
lean_object* v___x_978_; 
lean_inc_ref(v_post_919_);
lean_inc_ref(v_pre_918_);
v___x_978_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_918_, v_post_919_, v_usedLetOnly_920_, v_skipConstInApp_921_, v_skipInstances_917_, v_x_922_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref(v___x_978_);
v_f_932_ = v_a_979_;
v___y_933_ = v___y_925_;
v___y_934_ = v___y_926_;
v___y_935_ = v___y_927_;
v___y_936_ = v___y_928_;
v___y_937_ = v___y_929_;
goto v___jp_931_;
}
else
{
lean_dec_ref(v_x_923_);
lean_dec_ref(v_post_919_);
lean_dec_ref(v_pre_918_);
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(lean_object* v___x_987_, lean_object* v_pre_988_, lean_object* v_e_989_, lean_object* v_post_990_, uint8_t v_usedLetOnly_991_, uint8_t v_skipConstInApp_992_, uint8_t v_skipInstances_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Core_checkSystem(v___x_987_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v___x_1001_; 
lean_dec_ref(v___x_1000_);
lean_inc_ref(v_pre_988_);
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc_ref(v_e_989_);
v___x_1001_ = lean_apply_6(v_pre_988_, v_e_989_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, lean_box(0));
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1050_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1050_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1050_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___y_1007_; 
switch(lean_obj_tag(v_a_1002_))
{
case 0:
{
lean_object* v_e_1042_; lean_object* v___x_1044_; 
lean_dec_ref(v_post_990_);
lean_dec_ref(v_e_989_);
lean_dec_ref(v_pre_988_);
v_e_1042_ = lean_ctor_get(v_a_1002_, 0);
lean_inc_ref(v_e_1042_);
lean_dec_ref(v_a_1002_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v_e_1042_);
v___x_1044_ = v___x_1004_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_e_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
case 1:
{
lean_object* v_e_1046_; lean_object* v___x_1047_; 
lean_del_object(v___x_1004_);
lean_dec_ref(v_e_989_);
v_e_1046_ = lean_ctor_get(v_a_1002_, 0);
lean_inc_ref(v_e_1046_);
lean_dec_ref(v_a_1002_);
v___x_1047_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v_e_1046_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1047_;
}
default: 
{
lean_object* v_e_x3f_1048_; 
lean_del_object(v___x_1004_);
v_e_x3f_1048_ = lean_ctor_get(v_a_1002_, 0);
lean_inc(v_e_x3f_1048_);
lean_dec_ref(v_a_1002_);
if (lean_obj_tag(v_e_x3f_1048_) == 0)
{
v___y_1007_ = v_e_989_;
goto v___jp_1006_;
}
else
{
lean_object* v_val_1049_; 
lean_dec_ref(v_e_989_);
v_val_1049_ = lean_ctor_get(v_e_x3f_1048_, 0);
lean_inc(v_val_1049_);
lean_dec_ref(v_e_x3f_1048_);
v___y_1007_ = v_val_1049_;
goto v___jp_1006_;
}
}
}
v___jp_1006_:
{
switch(lean_obj_tag(v___y_1007_))
{
case 7:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v___x_1008_, v___y_1007_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1009_;
}
case 6:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1011_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v___x_1010_, v___y_1007_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1011_;
}
case 8:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__0));
v___x_1013_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v___x_1012_, v___y_1007_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1013_;
}
case 5:
{
lean_object* v_dummy_1014_; lean_object* v_nargs_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_dummy_1014_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_1015_ = l_Lean_Expr_getAppNumArgs(v___y_1007_);
lean_inc(v_nargs_1015_);
v___x_1016_ = lean_mk_array(v_nargs_1015_, v_dummy_1014_);
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = lean_nat_sub(v_nargs_1015_, v___x_1017_);
lean_dec(v_nargs_1015_);
v___x_1019_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_993_, v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v___y_1007_, v___x_1016_, v___x_1018_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1019_;
}
case 10:
{
lean_object* v_data_1020_; lean_object* v_expr_1021_; lean_object* v___x_1022_; 
v_data_1020_ = lean_ctor_get(v___y_1007_, 0);
v_expr_1021_ = lean_ctor_get(v___y_1007_, 1);
lean_inc_ref(v_expr_1021_);
lean_inc_ref(v_post_990_);
lean_inc_ref(v_pre_988_);
v___x_1022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v_expr_1021_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; size_t v___x_1024_; size_t v___x_1025_; uint8_t v___x_1026_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = lean_ptr_addr(v_expr_1021_);
v___x_1025_ = lean_ptr_addr(v_a_1023_);
v___x_1026_ = lean_usize_dec_eq(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_inc(v_data_1020_);
lean_dec_ref(v___y_1007_);
v___x_1027_ = l_Lean_Expr_mdata___override(v_data_1020_, v_a_1023_);
v___x_1028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v___x_1027_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1028_;
}
else
{
lean_object* v___x_1029_; 
lean_dec(v_a_1023_);
v___x_1029_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v___y_1007_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1029_;
}
}
else
{
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_post_990_);
lean_dec_ref(v_pre_988_);
return v___x_1022_;
}
}
case 11:
{
lean_object* v_typeName_1030_; lean_object* v_idx_1031_; lean_object* v_struct_1032_; lean_object* v___x_1033_; 
v_typeName_1030_ = lean_ctor_get(v___y_1007_, 0);
v_idx_1031_ = lean_ctor_get(v___y_1007_, 1);
v_struct_1032_ = lean_ctor_get(v___y_1007_, 2);
lean_inc_ref(v_struct_1032_);
lean_inc_ref(v_post_990_);
lean_inc_ref(v_pre_988_);
v___x_1033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v_struct_1032_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; size_t v___x_1035_; size_t v___x_1036_; uint8_t v___x_1037_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref(v___x_1033_);
v___x_1035_ = lean_ptr_addr(v_struct_1032_);
v___x_1036_ = lean_ptr_addr(v_a_1034_);
v___x_1037_ = lean_usize_dec_eq(v___x_1035_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_inc(v_idx_1031_);
lean_inc(v_typeName_1030_);
lean_dec_ref(v___y_1007_);
v___x_1038_ = l_Lean_Expr_proj___override(v_typeName_1030_, v_idx_1031_, v_a_1034_);
v___x_1039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v___x_1038_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1039_;
}
else
{
lean_object* v___x_1040_; 
lean_dec(v_a_1034_);
v___x_1040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v___y_1007_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1040_;
}
}
else
{
lean_dec_ref(v___y_1007_);
lean_dec_ref(v_post_990_);
lean_dec_ref(v_pre_988_);
return v___x_1033_;
}
}
default: 
{
lean_object* v___x_1041_; 
v___x_1041_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_988_, v_post_990_, v_usedLetOnly_991_, v_skipConstInApp_992_, v_skipInstances_993_, v___y_1007_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
return v___x_1041_;
}
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v_post_990_);
lean_dec_ref(v_e_989_);
lean_dec_ref(v_pre_988_);
v_a_1051_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1001_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1001_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_post_990_);
lean_dec_ref(v_e_989_);
lean_dec_ref(v_pre_988_);
v_a_1059_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1000_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1000_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed(lean_object* v___x_1067_, lean_object* v_pre_1068_, lean_object* v_e_1069_, lean_object* v_post_1070_, lean_object* v_usedLetOnly_1071_, lean_object* v_skipConstInApp_1072_, lean_object* v_skipInstances_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
uint8_t v_usedLetOnly_boxed_1080_; uint8_t v_skipConstInApp_boxed_1081_; uint8_t v_skipInstances_boxed_1082_; lean_object* v_res_1083_; 
v_usedLetOnly_boxed_1080_ = lean_unbox(v_usedLetOnly_1071_);
v_skipConstInApp_boxed_1081_ = lean_unbox(v_skipConstInApp_1072_);
v_skipInstances_boxed_1082_ = lean_unbox(v_skipInstances_1073_);
v_res_1083_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1(v___x_1067_, v_pre_1068_, v_e_1069_, v_post_1070_, v_usedLetOnly_boxed_1080_, v_skipConstInApp_boxed_1081_, v_skipInstances_boxed_1082_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(lean_object* v_pre_1084_, lean_object* v_post_1085_, uint8_t v_usedLetOnly_1086_, uint8_t v_skipConstInApp_1087_, uint8_t v_skipInstances_1088_, lean_object* v_e_1089_, lean_object* v_a_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_inc(v_a_1090_);
v___x_1096_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1096_, 0, lean_box(0));
lean_closure_set(v___x_1096_, 1, lean_box(0));
lean_closure_set(v___x_1096_, 2, v_a_1090_);
v___x_1097_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___x_1096_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1132_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1132_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1132_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_1098_, v_e_1089_);
lean_dec(v_a_1098_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; 
lean_del_object(v___x_1100_);
v___x_1103_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
v___x_1104_ = lean_box(v_usedLetOnly_1086_);
v___x_1105_ = lean_box(v_skipConstInApp_1087_);
v___x_1106_ = lean_box(v_skipInstances_1088_);
lean_inc_ref(v_e_1089_);
v___f_1107_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___boxed), 13, 7);
lean_closure_set(v___f_1107_, 0, v___x_1103_);
lean_closure_set(v___f_1107_, 1, v_pre_1084_);
lean_closure_set(v___f_1107_, 2, v_e_1089_);
lean_closure_set(v___f_1107_, 3, v_post_1085_);
lean_closure_set(v___f_1107_, 4, v___x_1104_);
lean_closure_set(v___f_1107_, 5, v___x_1105_);
lean_closure_set(v___f_1107_, 6, v___x_1106_);
v___x_1108_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v___f_1107_, v_a_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___f_1110_; lean_object* v___x_1111_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_n(v_a_1109_, 2);
lean_dec_ref(v___x_1108_);
lean_inc(v_a_1090_);
v___f_1110_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1110_, 0, v_a_1090_);
lean_closure_set(v___f_1110_, 1, v_e_1089_);
lean_closure_set(v___f_1110_, 2, v_a_1109_);
v___x_1111_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__0(lean_box(0), v___f_1110_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v___x_1111_, 0);
lean_dec(v_unused_1119_);
v___x_1113_ = v___x_1111_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v___x_1111_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v_a_1109_);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1109_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_a_1109_);
v_a_1120_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1111_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1111_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_dec_ref(v_e_1089_);
return v___x_1108_;
}
}
else
{
lean_object* v_val_1128_; lean_object* v___x_1130_; 
lean_dec_ref(v_e_1089_);
lean_dec_ref(v_post_1085_);
lean_dec_ref(v_pre_1084_);
v_val_1128_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1128_);
lean_dec_ref(v___x_1102_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v_val_1128_);
v___x_1130_ = v___x_1100_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_val_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_e_1089_);
lean_dec_ref(v_post_1085_);
lean_dec_ref(v_pre_1084_);
v_a_1133_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1097_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1097_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_1141_, lean_object* v_pre_1142_, lean_object* v_post_1143_, lean_object* v_usedLetOnly_1144_, lean_object* v_skipConstInApp_1145_, lean_object* v_skipInstances_1146_, lean_object* v_body_1147_, lean_object* v_x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
uint8_t v_usedLetOnly_boxed_1155_; uint8_t v_skipConstInApp_boxed_1156_; uint8_t v_skipInstances_boxed_1157_; lean_object* v_res_1158_; 
v_usedLetOnly_boxed_1155_ = lean_unbox(v_usedLetOnly_1144_);
v_skipConstInApp_boxed_1156_ = lean_unbox(v_skipConstInApp_1145_);
v_skipInstances_boxed_1157_ = lean_unbox(v_skipInstances_1146_);
v_res_1158_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(v_fvars_1141_, v_pre_1142_, v_post_1143_, v_usedLetOnly_boxed_1155_, v_skipConstInApp_boxed_1156_, v_skipInstances_boxed_1157_, v_body_1147_, v_x_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(lean_object* v_pre_1159_, lean_object* v_post_1160_, uint8_t v_usedLetOnly_1161_, uint8_t v_skipConstInApp_1162_, uint8_t v_skipInstances_1163_, lean_object* v_fvars_1164_, lean_object* v_e_1165_, lean_object* v_a_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
if (lean_obj_tag(v_e_1165_) == 7)
{
lean_object* v_binderName_1172_; lean_object* v_binderType_1173_; lean_object* v_body_1174_; uint8_t v_binderInfo_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_binderName_1172_ = lean_ctor_get(v_e_1165_, 0);
lean_inc(v_binderName_1172_);
v_binderType_1173_ = lean_ctor_get(v_e_1165_, 1);
lean_inc_ref(v_binderType_1173_);
v_body_1174_ = lean_ctor_get(v_e_1165_, 2);
lean_inc_ref(v_body_1174_);
v_binderInfo_1175_ = lean_ctor_get_uint8(v_e_1165_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1165_);
v___x_1176_ = lean_expr_instantiate_rev(v_binderType_1173_, v_fvars_1164_);
lean_dec_ref(v_binderType_1173_);
lean_inc_ref(v_post_1160_);
lean_inc_ref(v_pre_1159_);
v___x_1177_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1159_, v_post_1160_, v_usedLetOnly_1161_, v_skipConstInApp_1162_, v_skipInstances_1163_, v___x_1176_, v_a_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___f_1182_; uint8_t v___x_1183_; lean_object* v___x_1184_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
v___x_1179_ = lean_box(v_usedLetOnly_1161_);
v___x_1180_ = lean_box(v_skipConstInApp_1162_);
v___x_1181_ = lean_box(v_skipInstances_1163_);
v___f_1182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1182_, 0, v_fvars_1164_);
lean_closure_set(v___f_1182_, 1, v_pre_1159_);
lean_closure_set(v___f_1182_, 2, v_post_1160_);
lean_closure_set(v___f_1182_, 3, v___x_1179_);
lean_closure_set(v___f_1182_, 4, v___x_1180_);
lean_closure_set(v___f_1182_, 5, v___x_1181_);
lean_closure_set(v___f_1182_, 6, v_body_1174_);
v___x_1183_ = 0;
v___x_1184_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_1172_, v_binderInfo_1175_, v_a_1178_, v___f_1182_, v___x_1183_, v_a_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1184_;
}
else
{
lean_dec_ref(v_body_1174_);
lean_dec(v_binderName_1172_);
lean_dec_ref(v_fvars_1164_);
lean_dec_ref(v_post_1160_);
lean_dec_ref(v_pre_1159_);
return v___x_1177_;
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_expr_instantiate_rev(v_e_1165_, v_fvars_1164_);
lean_dec_ref(v_e_1165_);
lean_inc_ref(v_post_1160_);
lean_inc_ref(v_pre_1159_);
v___x_1186_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1159_, v_post_1160_, v_usedLetOnly_1161_, v_skipConstInApp_1162_, v_skipInstances_1163_, v___x_1185_, v_a_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; uint8_t v___x_1188_; uint8_t v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = 0;
v___x_1189_ = 1;
v___x_1190_ = 1;
v___x_1191_ = l_Lean_Meta_mkForallFVars(v_fvars_1164_, v_a_1187_, v___x_1188_, v_usedLetOnly_1161_, v___x_1189_, v___x_1190_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec_ref(v_fvars_1164_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref(v___x_1191_);
v___x_1193_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1159_, v_post_1160_, v_usedLetOnly_1161_, v_skipConstInApp_1162_, v_skipInstances_1163_, v_a_1192_, v_a_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1193_;
}
else
{
lean_dec_ref(v_post_1160_);
lean_dec_ref(v_pre_1159_);
return v___x_1191_;
}
}
else
{
lean_dec_ref(v_fvars_1164_);
lean_dec_ref(v_post_1160_);
lean_dec_ref(v_pre_1159_);
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_1194_, lean_object* v_pre_1195_, lean_object* v_post_1196_, uint8_t v_usedLetOnly_1197_, uint8_t v_skipConstInApp_1198_, uint8_t v_skipInstances_1199_, lean_object* v_body_1200_, lean_object* v_x_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_array_push(v_fvars_1194_, v_x_1201_);
v___x_1209_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1195_, v_post_1196_, v_usedLetOnly_1197_, v_skipConstInApp_1198_, v_skipInstances_1199_, v___x_1208_, v_body_1200_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_1210_, lean_object* v_post_1211_, lean_object* v_usedLetOnly_1212_, lean_object* v_skipConstInApp_1213_, lean_object* v_skipInstances_1214_, lean_object* v_e_1215_, lean_object* v_a_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
uint8_t v_usedLetOnly_boxed_1222_; uint8_t v_skipConstInApp_boxed_1223_; uint8_t v_skipInstances_boxed_1224_; lean_object* v_res_1225_; 
v_usedLetOnly_boxed_1222_ = lean_unbox(v_usedLetOnly_1212_);
v_skipConstInApp_boxed_1223_ = lean_unbox(v_skipConstInApp_1213_);
v_skipInstances_boxed_1224_ = lean_unbox(v_skipInstances_1214_);
v_res_1225_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__2(v_pre_1210_, v_post_1211_, v_usedLetOnly_boxed_1222_, v_skipConstInApp_boxed_1223_, v_skipInstances_boxed_1224_, v_e_1215_, v_a_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v_a_1216_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_1226_, lean_object* v_post_1227_, lean_object* v_usedLetOnly_1228_, lean_object* v_skipConstInApp_1229_, lean_object* v_skipInstances_1230_, lean_object* v_sz_1231_, lean_object* v_i_1232_, lean_object* v_bs_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_usedLetOnly_boxed_1240_; uint8_t v_skipConstInApp_boxed_1241_; uint8_t v_skipInstances_boxed_1242_; size_t v_sz_boxed_1243_; size_t v_i_boxed_1244_; lean_object* v_res_1245_; 
v_usedLetOnly_boxed_1240_ = lean_unbox(v_usedLetOnly_1228_);
v_skipConstInApp_boxed_1241_ = lean_unbox(v_skipConstInApp_1229_);
v_skipInstances_boxed_1242_ = lean_unbox(v_skipInstances_1230_);
v_sz_boxed_1243_ = lean_unbox_usize(v_sz_1231_);
lean_dec(v_sz_1231_);
v_i_boxed_1244_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_res_1245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__1(v_pre_1226_, v_post_1227_, v_usedLetOnly_boxed_1240_, v_skipConstInApp_boxed_1241_, v_skipInstances_boxed_1242_, v_sz_boxed_1243_, v_i_boxed_1244_, v_bs_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___boxed(lean_object* v_pre_1246_, lean_object* v_post_1247_, lean_object* v_usedLetOnly_1248_, lean_object* v_skipConstInApp_1249_, lean_object* v_skipInstances_1250_, lean_object* v_e_1251_, lean_object* v_a_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v_usedLetOnly_boxed_1258_; uint8_t v_skipConstInApp_boxed_1259_; uint8_t v_skipInstances_boxed_1260_; lean_object* v_res_1261_; 
v_usedLetOnly_boxed_1258_ = lean_unbox(v_usedLetOnly_1248_);
v_skipConstInApp_boxed_1259_ = lean_unbox(v_skipConstInApp_1249_);
v_skipInstances_boxed_1260_ = lean_unbox(v_skipInstances_1250_);
v_res_1261_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1246_, v_post_1247_, v_usedLetOnly_boxed_1258_, v_skipConstInApp_boxed_1259_, v_skipInstances_boxed_1260_, v_e_1251_, v_a_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v_a_1252_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_1262_, lean_object* v_post_1263_, lean_object* v_usedLetOnly_1264_, lean_object* v_skipConstInApp_1265_, lean_object* v_skipInstances_1266_, lean_object* v_fvars_1267_, lean_object* v_e_1268_, lean_object* v_a_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v_usedLetOnly_boxed_1275_; uint8_t v_skipConstInApp_boxed_1276_; uint8_t v_skipInstances_boxed_1277_; lean_object* v_res_1278_; 
v_usedLetOnly_boxed_1275_ = lean_unbox(v_usedLetOnly_1264_);
v_skipConstInApp_boxed_1276_ = lean_unbox(v_skipConstInApp_1265_);
v_skipInstances_boxed_1277_ = lean_unbox(v_skipInstances_1266_);
v_res_1278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5(v_pre_1262_, v_post_1263_, v_usedLetOnly_boxed_1275_, v_skipConstInApp_boxed_1276_, v_skipInstances_boxed_1277_, v_fvars_1267_, v_e_1268_, v_a_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v_a_1269_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_1279_, lean_object* v_post_1280_, lean_object* v_usedLetOnly_1281_, lean_object* v_skipConstInApp_1282_, lean_object* v_skipInstances_1283_, lean_object* v_fvars_1284_, lean_object* v_e_1285_, lean_object* v_a_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
uint8_t v_usedLetOnly_boxed_1292_; uint8_t v_skipConstInApp_boxed_1293_; uint8_t v_skipInstances_boxed_1294_; lean_object* v_res_1295_; 
v_usedLetOnly_boxed_1292_ = lean_unbox(v_usedLetOnly_1281_);
v_skipConstInApp_boxed_1293_ = lean_unbox(v_skipConstInApp_1282_);
v_skipInstances_boxed_1294_ = lean_unbox(v_skipInstances_1283_);
v_res_1295_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__6(v_pre_1279_, v_post_1280_, v_usedLetOnly_boxed_1292_, v_skipConstInApp_boxed_1293_, v_skipInstances_boxed_1294_, v_fvars_1284_, v_e_1285_, v_a_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v_a_1286_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_1296_, lean_object* v_post_1297_, lean_object* v_usedLetOnly_1298_, lean_object* v_skipConstInApp_1299_, lean_object* v_skipInstances_1300_, lean_object* v_fvars_1301_, lean_object* v_e_1302_, lean_object* v_a_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v_usedLetOnly_boxed_1309_; uint8_t v_skipConstInApp_boxed_1310_; uint8_t v_skipInstances_boxed_1311_; lean_object* v_res_1312_; 
v_usedLetOnly_boxed_1309_ = lean_unbox(v_usedLetOnly_1298_);
v_skipConstInApp_boxed_1310_ = lean_unbox(v_skipConstInApp_1299_);
v_skipInstances_boxed_1311_ = lean_unbox(v_skipInstances_1300_);
v_res_1312_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7(v_pre_1296_, v_post_1297_, v_usedLetOnly_boxed_1309_, v_skipConstInApp_boxed_1310_, v_skipInstances_boxed_1311_, v_fvars_1301_, v_e_1302_, v_a_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v_a_1303_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_1313_, lean_object* v___x_1314_, lean_object* v_pre_1315_, lean_object* v_post_1316_, lean_object* v_usedLetOnly_1317_, lean_object* v_skipConstInApp_1318_, lean_object* v_skipInstances_1319_, lean_object* v_a_1320_, lean_object* v_b_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
uint8_t v_usedLetOnly_boxed_1328_; uint8_t v_skipConstInApp_boxed_1329_; uint8_t v_skipInstances_boxed_1330_; lean_object* v_res_1331_; 
v_usedLetOnly_boxed_1328_ = lean_unbox(v_usedLetOnly_1317_);
v_skipConstInApp_boxed_1329_ = lean_unbox(v_skipConstInApp_1318_);
v_skipInstances_boxed_1330_ = lean_unbox(v_skipInstances_1319_);
v_res_1331_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1313_, v___x_1314_, v_pre_1315_, v_post_1316_, v_usedLetOnly_boxed_1328_, v_skipConstInApp_boxed_1329_, v_skipInstances_boxed_1330_, v_a_1320_, v_b_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___x_1314_);
lean_dec(v_upperBound_1313_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_1332_, lean_object* v_pre_1333_, lean_object* v_post_1334_, lean_object* v_usedLetOnly_1335_, lean_object* v_skipConstInApp_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_skipInstances_boxed_1346_; uint8_t v_usedLetOnly_boxed_1347_; uint8_t v_skipConstInApp_boxed_1348_; lean_object* v_res_1349_; 
v_skipInstances_boxed_1346_ = lean_unbox(v_skipInstances_1332_);
v_usedLetOnly_boxed_1347_ = lean_unbox(v_usedLetOnly_1335_);
v_skipConstInApp_boxed_1348_ = lean_unbox(v_skipConstInApp_1336_);
v_res_1349_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__8(v_skipInstances_boxed_1346_, v_pre_1333_, v_post_1334_, v_usedLetOnly_boxed_1347_, v_skipConstInApp_boxed_1348_, v_x_1337_, v_x_1338_, v_x_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
return v_res_1349_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_unsigned_to_nat(16u);
v___x_1352_ = lean_mk_array(v___x_1351_, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__0);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___x_1353_);
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_1357_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1357_, 0, lean_box(0));
lean_closure_set(v___x_1357_, 1, lean_box(0));
lean_closure_set(v___x_1357_, 2, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(lean_object* v_input_1358_, lean_object* v_pre_1359_, lean_object* v_post_1360_, uint8_t v_usedLetOnly_1361_, uint8_t v_skipConstInApp_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_a_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; 
v___x_1368_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_1369_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1368_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = 0;
v___x_1372_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0(v_pre_1359_, v_post_1360_, v_usedLetOnly_1361_, v_skipConstInApp_1362_, v___x_1371_, v_input_1358_, v_a_1370_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1374_, 0, lean_box(0));
lean_closure_set(v___x_1374_, 1, lean_box(0));
lean_closure_set(v___x_1374_, 2, v_a_1370_);
v___x_1375_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___lam__0(lean_box(0), v___x_1374_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v___x_1375_, 0);
lean_dec(v_unused_1383_);
v___x_1377_ = v___x_1375_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_dec(v___x_1375_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v_a_1373_);
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1373_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_dec(v_a_1370_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___boxed(lean_object* v_input_1384_, lean_object* v_pre_1385_, lean_object* v_post_1386_, lean_object* v_usedLetOnly_1387_, lean_object* v_skipConstInApp_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v_usedLetOnly_boxed_1394_; uint8_t v_skipConstInApp_boxed_1395_; lean_object* v_res_1396_; 
v_usedLetOnly_boxed_1394_ = lean_unbox(v_usedLetOnly_1387_);
v_skipConstInApp_boxed_1395_ = lean_unbox(v_skipConstInApp_1388_);
v_res_1396_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_input_1384_, v_pre_1385_, v_post_1386_, v_usedLetOnly_boxed_1394_, v_skipConstInApp_boxed_1395_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object* v_e_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1405_; lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1418_; 
v___x_1405_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_isUnfoldReducibleTarget___redArg(v_e_1399_, v_a_1403_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1418_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1418_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_unbox(v_a_1406_);
lean_dec(v_a_1406_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1412_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v_e_1399_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_e_1399_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
else
{
lean_object* v___f_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_del_object(v___x_1408_);
v___f_1414_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__0));
v___x_1415_ = 0;
v___x_1416_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducible___closed__1));
v___x_1417_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1399_, v___x_1416_, v___f_1414_, v___x_1415_, v___x_1415_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_unfoldReducible___boxed(lean_object* v_e_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_Sym_unfoldReducible(v_e_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(lean_object* v_upperBound_1426_, lean_object* v___x_1427_, lean_object* v_pre_1428_, lean_object* v_post_1429_, uint8_t v_usedLetOnly_1430_, uint8_t v_skipConstInApp_1431_, uint8_t v_skipInstances_1432_, lean_object* v___x_1433_, lean_object* v_inst_1434_, lean_object* v_R_1435_, lean_object* v_a_1436_, lean_object* v_b_1437_, lean_object* v_c_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___redArg(v_upperBound_1426_, v___x_1427_, v_pre_1428_, v_post_1429_, v_usedLetOnly_1430_, v_skipConstInApp_1431_, v_skipInstances_1432_, v_a_1436_, v_b_1437_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_1446_ = _args[0];
lean_object* v___x_1447_ = _args[1];
lean_object* v_pre_1448_ = _args[2];
lean_object* v_post_1449_ = _args[3];
lean_object* v_usedLetOnly_1450_ = _args[4];
lean_object* v_skipConstInApp_1451_ = _args[5];
lean_object* v_skipInstances_1452_ = _args[6];
lean_object* v___x_1453_ = _args[7];
lean_object* v_inst_1454_ = _args[8];
lean_object* v_R_1455_ = _args[9];
lean_object* v_a_1456_ = _args[10];
lean_object* v_b_1457_ = _args[11];
lean_object* v_c_1458_ = _args[12];
lean_object* v___y_1459_ = _args[13];
lean_object* v___y_1460_ = _args[14];
lean_object* v___y_1461_ = _args[15];
lean_object* v___y_1462_ = _args[16];
lean_object* v___y_1463_ = _args[17];
lean_object* v___y_1464_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_1465_; uint8_t v_skipConstInApp_boxed_1466_; uint8_t v_skipInstances_boxed_1467_; lean_object* v_res_1468_; 
v_usedLetOnly_boxed_1465_ = lean_unbox(v_usedLetOnly_1450_);
v_skipConstInApp_boxed_1466_ = lean_unbox(v_skipConstInApp_1451_);
v_skipInstances_boxed_1467_ = lean_unbox(v_skipInstances_1452_);
v_res_1468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__3(v_upperBound_1446_, v___x_1447_, v_pre_1448_, v_post_1449_, v_usedLetOnly_boxed_1465_, v_skipConstInApp_boxed_1466_, v_skipInstances_boxed_1467_, v___x_1453_, v_inst_1454_, v_R_1455_, v_a_1456_, v_b_1457_, v_c_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v___x_1453_);
lean_dec_ref(v___x_1447_);
lean_dec(v_upperBound_1446_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_1469_, lean_object* v_m_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_m_1470_, v_a_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_1473_, lean_object* v_m_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4(v_00_u03b2_1473_, v_m_1474_, v_a_1475_);
lean_dec_ref(v_a_1475_);
lean_dec_ref(v_m_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_1477_, lean_object* v_name_1478_, uint8_t v_bi_1479_, lean_object* v_type_1480_, lean_object* v_k_1481_, uint8_t v_kind_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___redArg(v_name_1478_, v_bi_1479_, v_type_1480_, v_k_1481_, v_kind_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1490_, lean_object* v_name_1491_, lean_object* v_bi_1492_, lean_object* v_type_1493_, lean_object* v_k_1494_, lean_object* v_kind_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_bi_boxed_1502_; uint8_t v_kind_boxed_1503_; lean_object* v_res_1504_; 
v_bi_boxed_1502_ = lean_unbox(v_bi_1492_);
v_kind_boxed_1503_ = lean_unbox(v_kind_1495_);
v_res_1504_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_1490_, v_name_1491_, v_bi_boxed_1502_, v_type_1493_, v_k_1494_, v_kind_boxed_1503_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_1505_, lean_object* v_name_1506_, lean_object* v_type_1507_, lean_object* v_val_1508_, lean_object* v_k_1509_, uint8_t v_nondep_1510_, uint8_t v_kind_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1506_, v_type_1507_, v_val_1508_, v_k_1509_, v_nondep_1510_, v_kind_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_name_1520_, lean_object* v_type_1521_, lean_object* v_val_1522_, lean_object* v_k_1523_, lean_object* v_nondep_1524_, lean_object* v_kind_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_nondep_boxed_1532_; uint8_t v_kind_boxed_1533_; lean_object* v_res_1534_; 
v_nondep_boxed_1532_ = lean_unbox(v_nondep_1524_);
v_kind_boxed_1533_ = lean_unbox(v_kind_1525_);
v_res_1534_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_1519_, v_name_1520_, v_type_1521_, v_val_1522_, v_k_1523_, v_nondep_boxed_1532_, v_kind_boxed_1533_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_1535_, lean_object* v_ref_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1536_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1543_, lean_object* v_ref_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_1543_, v_ref_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___redArg(v_x_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9(v_00_u03b1_1560_, v_x_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_1569_, lean_object* v_m_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10___redArg(v_m_1570_, v_a_1571_, v_b_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_1574_, lean_object* v_a_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1575_, v_x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1578_, lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_1578_, v_a_1579_, v_x_1580_);
lean_dec(v_x_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_1582_, lean_object* v_a_1583_, lean_object* v_x_1584_){
_start:
{
uint8_t v___x_1585_; 
v___x_1585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___redArg(v_a_1583_, v_x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_1586_, lean_object* v_a_1587_, lean_object* v_x_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_1586_, v_a_1587_, v_x_1588_);
lean_dec(v_x_1588_);
lean_dec_ref(v_a_1587_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_1591_, lean_object* v_data_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16___redArg(v_data_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_1594_, lean_object* v_a_1595_, lean_object* v_b_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__17___redArg(v_a_1595_, v_b_1596_, v_x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_1599_, lean_object* v_i_1600_, lean_object* v_source_1601_, lean_object* v_target_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_1600_, v_source_1601_, v_target_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_1605_, v_x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(lean_object* v_msgData_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v_env_1615_; lean_object* v___x_1616_; lean_object* v_mctx_1617_; lean_object* v_lctx_1618_; lean_object* v_options_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1614_ = lean_st_ref_get(v___y_1612_);
v_env_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc_ref(v_env_1615_);
lean_dec(v___x_1614_);
v___x_1616_ = lean_st_ref_get(v___y_1610_);
v_mctx_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc_ref(v_mctx_1617_);
lean_dec(v___x_1616_);
v_lctx_1618_ = lean_ctor_get(v___y_1609_, 2);
v_options_1619_ = lean_ctor_get(v___y_1611_, 2);
lean_inc_ref(v_options_1619_);
lean_inc_ref(v_lctx_1618_);
v___x_1620_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1620_, 0, v_env_1615_);
lean_ctor_set(v___x_1620_, 1, v_mctx_1617_);
lean_ctor_set(v___x_1620_, 2, v_lctx_1618_);
lean_ctor_set(v___x_1620_, 3, v_options_1619_);
v___x_1621_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v_msgData_1608_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msgData_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1629_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1630_; double v___x_1631_; 
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_float_of_nat(v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(lean_object* v_cls_1635_, lean_object* v_msg_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_ref_1642_; lean_object* v___x_1643_; lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1688_; 
v_ref_1642_ = lean_ctor_get(v___y_1639_, 5);
v___x_1643_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1688_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1688_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v_traceState_1649_; lean_object* v_env_1650_; lean_object* v_nextMacroScope_1651_; lean_object* v_ngen_1652_; lean_object* v_auxDeclNGen_1653_; lean_object* v_cache_1654_; lean_object* v_messages_1655_; lean_object* v_infoState_1656_; lean_object* v_snapshotTasks_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1687_; 
v___x_1648_ = lean_st_ref_take(v___y_1640_);
v_traceState_1649_ = lean_ctor_get(v___x_1648_, 4);
v_env_1650_ = lean_ctor_get(v___x_1648_, 0);
v_nextMacroScope_1651_ = lean_ctor_get(v___x_1648_, 1);
v_ngen_1652_ = lean_ctor_get(v___x_1648_, 2);
v_auxDeclNGen_1653_ = lean_ctor_get(v___x_1648_, 3);
v_cache_1654_ = lean_ctor_get(v___x_1648_, 5);
v_messages_1655_ = lean_ctor_get(v___x_1648_, 6);
v_infoState_1656_ = lean_ctor_get(v___x_1648_, 7);
v_snapshotTasks_1657_ = lean_ctor_get(v___x_1648_, 8);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1659_ = v___x_1648_;
v_isShared_1660_ = v_isSharedCheck_1687_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_snapshotTasks_1657_);
lean_inc(v_infoState_1656_);
lean_inc(v_messages_1655_);
lean_inc(v_cache_1654_);
lean_inc(v_traceState_1649_);
lean_inc(v_auxDeclNGen_1653_);
lean_inc(v_ngen_1652_);
lean_inc(v_nextMacroScope_1651_);
lean_inc(v_env_1650_);
lean_dec(v___x_1648_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1687_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
uint64_t v_tid_1661_; lean_object* v_traces_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1686_; 
v_tid_1661_ = lean_ctor_get_uint64(v_traceState_1649_, sizeof(void*)*1);
v_traces_1662_ = lean_ctor_get(v_traceState_1649_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_traceState_1649_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1664_ = v_traceState_1649_;
v_isShared_1665_ = v_isSharedCheck_1686_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_traces_1662_);
lean_dec(v_traceState_1649_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1686_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; double v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__0);
v___x_1668_ = 0;
v___x_1669_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_1670_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1670_, 0, v_cls_1635_);
lean_ctor_set(v___x_1670_, 1, v___x_1666_);
lean_ctor_set(v___x_1670_, 2, v___x_1669_);
lean_ctor_set_float(v___x_1670_, sizeof(void*)*3, v___x_1667_);
lean_ctor_set_float(v___x_1670_, sizeof(void*)*3 + 8, v___x_1667_);
lean_ctor_set_uint8(v___x_1670_, sizeof(void*)*3 + 16, v___x_1668_);
v___x_1671_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__2));
v___x_1672_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v_a_1644_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
lean_inc(v_ref_1642_);
v___x_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1673_, 0, v_ref_1642_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_PersistentArray_push___redArg(v_traces_1662_, v___x_1673_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1674_);
v___x_1676_ = v___x_1664_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1674_);
lean_ctor_set_uint64(v_reuseFailAlloc_1685_, sizeof(void*)*1, v_tid_1661_);
v___x_1676_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1678_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 4, v___x_1676_);
v___x_1678_ = v___x_1659_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_env_1650_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_nextMacroScope_1651_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_ngen_1652_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_auxDeclNGen_1653_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1684_, 5, v_cache_1654_);
lean_ctor_set(v_reuseFailAlloc_1684_, 6, v_messages_1655_);
lean_ctor_set(v_reuseFailAlloc_1684_, 7, v_infoState_1656_);
lean_ctor_set(v_reuseFailAlloc_1684_, 8, v_snapshotTasks_1657_);
v___x_1678_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1679_ = lean_st_ref_set(v___y_1640_, v___x_1678_);
v___x_1680_ = lean_box(0);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1680_);
v___x_1682_ = v___x_1646_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___boxed(lean_object* v_cls_1689_, lean_object* v_msg_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v_cls_1689_, v_msg_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1696_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__2));
v___x_1706_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__4));
v___x_1707_ = l_Lean_Name_append(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__6));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__8));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
static uint64_t _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__10(void){
_start:
{
uint8_t v___x_1714_; uint64_t v___x_1715_; 
v___x_1714_ = 1;
v___x_1715_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1714_);
return v___x_1715_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__11));
v___x_1718_ = l_Lean_stringToMessageData(v___x_1717_);
return v___x_1718_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__14(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__13));
v___x_1721_ = l_Lean_stringToMessageData(v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0(lean_object* v_e_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
if (lean_obj_tag(v_e_1722_) == 11)
{
lean_object* v_typeName_1734_; lean_object* v_idx_1735_; lean_object* v_struct_1736_; lean_object* v___x_1737_; lean_object* v_env_1738_; lean_object* v___x_1739_; 
v_typeName_1734_ = lean_ctor_get(v_e_1722_, 0);
v_idx_1735_ = lean_ctor_get(v_e_1722_, 1);
v_struct_1736_ = lean_ctor_get(v_e_1722_, 2);
v___x_1737_ = lean_st_ref_get(v___y_1726_);
v_env_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc_ref(v_env_1738_);
lean_dec(v___x_1737_);
lean_inc(v_typeName_1734_);
v___x_1739_ = l_Lean_getStructureInfo_x3f(v_env_1738_, v_typeName_1734_);
if (lean_obj_tag(v___x_1739_) == 1)
{
lean_object* v_val_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1839_; 
v_val_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1839_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_val_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1839_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_fieldNames_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v_fieldNames_1744_ = lean_ctor_get(v_val_1740_, 1);
lean_inc_ref(v_fieldNames_1744_);
lean_dec(v_val_1740_);
v___x_1745_ = lean_array_get_size(v_fieldNames_1744_);
v___x_1746_ = lean_nat_dec_lt(v_idx_1735_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v_options_1747_; uint8_t v_hasTrace_1748_; 
lean_dec_ref(v_fieldNames_1744_);
v_options_1747_ = lean_ctor_get(v___y_1725_, 2);
v_hasTrace_1748_ = lean_ctor_get_uint8(v_options_1747_, sizeof(void*)*1);
if (v_hasTrace_1748_ == 0)
{
lean_del_object(v___x_1742_);
goto v___jp_1728_;
}
else
{
lean_object* v_inheritedTraceOptions_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_inheritedTraceOptions_1749_ = lean_ctor_get(v___y_1725_, 13);
v___x_1750_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__2));
v___x_1751_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__5, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5);
v___x_1752_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1749_, v_options_1747_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_del_object(v___x_1742_);
goto v___jp_1728_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1753_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__7, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__7_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__7);
lean_inc(v_idx_1735_);
v___x_1754_ = l_Nat_reprFast(v_idx_1735_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 3);
lean_ctor_set(v___x_1742_, 0, v___x_1754_);
v___x_1756_ = v___x_1742_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1757_ = l_Lean_MessageData_ofFormat(v___x_1756_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1753_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__9, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__9_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__9);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
lean_inc_ref(v_e_1722_);
v___x_1761_ = l_Lean_indentExpr(v_e_1722_);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1750_, v___x_1762_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_dec_ref(v___x_1763_);
goto v___jp_1728_;
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_e_1722_);
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1763_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1763_);
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
}
else
{
lean_object* v___x_1773_; uint8_t v_foApprox_1774_; uint8_t v_ctxApprox_1775_; uint8_t v_quasiPatternApprox_1776_; uint8_t v_constApprox_1777_; uint8_t v_isDefEqStuckEx_1778_; uint8_t v_unificationHints_1779_; uint8_t v_proofIrrelevance_1780_; uint8_t v_assignSyntheticOpaque_1781_; uint8_t v_offsetCnstrs_1782_; uint8_t v_etaStruct_1783_; uint8_t v_univApprox_1784_; uint8_t v_iota_1785_; uint8_t v_beta_1786_; uint8_t v_proj_1787_; uint8_t v_zeta_1788_; uint8_t v_zetaDelta_1789_; uint8_t v_zetaUnused_1790_; uint8_t v_zetaHave_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1838_; 
lean_inc_ref(v_struct_1736_);
lean_inc(v_idx_1735_);
lean_dec_ref(v_e_1722_);
v___x_1773_ = l_Lean_Meta_Context_config(v___y_1723_);
v_foApprox_1774_ = lean_ctor_get_uint8(v___x_1773_, 0);
v_ctxApprox_1775_ = lean_ctor_get_uint8(v___x_1773_, 1);
v_quasiPatternApprox_1776_ = lean_ctor_get_uint8(v___x_1773_, 2);
v_constApprox_1777_ = lean_ctor_get_uint8(v___x_1773_, 3);
v_isDefEqStuckEx_1778_ = lean_ctor_get_uint8(v___x_1773_, 4);
v_unificationHints_1779_ = lean_ctor_get_uint8(v___x_1773_, 5);
v_proofIrrelevance_1780_ = lean_ctor_get_uint8(v___x_1773_, 6);
v_assignSyntheticOpaque_1781_ = lean_ctor_get_uint8(v___x_1773_, 7);
v_offsetCnstrs_1782_ = lean_ctor_get_uint8(v___x_1773_, 8);
v_etaStruct_1783_ = lean_ctor_get_uint8(v___x_1773_, 10);
v_univApprox_1784_ = lean_ctor_get_uint8(v___x_1773_, 11);
v_iota_1785_ = lean_ctor_get_uint8(v___x_1773_, 12);
v_beta_1786_ = lean_ctor_get_uint8(v___x_1773_, 13);
v_proj_1787_ = lean_ctor_get_uint8(v___x_1773_, 14);
v_zeta_1788_ = lean_ctor_get_uint8(v___x_1773_, 15);
v_zetaDelta_1789_ = lean_ctor_get_uint8(v___x_1773_, 16);
v_zetaUnused_1790_ = lean_ctor_get_uint8(v___x_1773_, 17);
v_zetaHave_1791_ = lean_ctor_get_uint8(v___x_1773_, 18);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1793_ = v___x_1773_;
v_isShared_1794_ = v_isSharedCheck_1838_;
goto v_resetjp_1792_;
}
else
{
lean_dec(v___x_1773_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1838_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
uint8_t v_trackZetaDelta_1795_; lean_object* v_zetaDeltaSet_1796_; lean_object* v_lctx_1797_; lean_object* v_localInstances_1798_; lean_object* v_defEqCtx_x3f_1799_; lean_object* v_synthPendingDepth_1800_; lean_object* v_canUnfold_x3f_1801_; uint8_t v_univApprox_1802_; uint8_t v_inTypeClassResolution_1803_; uint8_t v_cacheInferType_1804_; uint8_t v___x_1805_; lean_object* v_config_1807_; 
v_trackZetaDelta_1795_ = lean_ctor_get_uint8(v___y_1723_, sizeof(void*)*7);
v_zetaDeltaSet_1796_ = lean_ctor_get(v___y_1723_, 1);
v_lctx_1797_ = lean_ctor_get(v___y_1723_, 2);
v_localInstances_1798_ = lean_ctor_get(v___y_1723_, 3);
v_defEqCtx_x3f_1799_ = lean_ctor_get(v___y_1723_, 4);
v_synthPendingDepth_1800_ = lean_ctor_get(v___y_1723_, 5);
v_canUnfold_x3f_1801_ = lean_ctor_get(v___y_1723_, 6);
v_univApprox_1802_ = lean_ctor_get_uint8(v___y_1723_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1803_ = lean_ctor_get_uint8(v___y_1723_, sizeof(void*)*7 + 2);
v_cacheInferType_1804_ = lean_ctor_get_uint8(v___y_1723_, sizeof(void*)*7 + 3);
v___x_1805_ = 1;
if (v_isShared_1794_ == 0)
{
v_config_1807_ = v___x_1793_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 0, v_foApprox_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 1, v_ctxApprox_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 2, v_quasiPatternApprox_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 3, v_constApprox_1777_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 4, v_isDefEqStuckEx_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 5, v_unificationHints_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 6, v_proofIrrelevance_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 7, v_assignSyntheticOpaque_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 8, v_offsetCnstrs_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 10, v_etaStruct_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 11, v_univApprox_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 12, v_iota_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 13, v_beta_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 14, v_proj_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 15, v_zeta_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 16, v_zetaDelta_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 17, v_zetaUnused_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, 18, v_zetaHave_1791_);
v_config_1807_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
uint64_t v___x_1808_; uint64_t v___x_1809_; uint64_t v___x_1810_; lean_object* v___x_1811_; uint64_t v___x_1812_; uint64_t v___x_1813_; uint64_t v_key_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_ctor_set_uint8(v_config_1807_, 9, v___x_1805_);
v___x_1808_ = l_Lean_Meta_Context_configKey(v___y_1723_);
v___x_1809_ = 2ULL;
v___x_1810_ = lean_uint64_shift_right(v___x_1808_, v___x_1809_);
v___x_1811_ = lean_array_fget(v_fieldNames_1744_, v_idx_1735_);
lean_dec(v_idx_1735_);
lean_dec_ref(v_fieldNames_1744_);
v___x_1812_ = lean_uint64_shift_left(v___x_1810_, v___x_1809_);
v___x_1813_ = lean_uint64_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__10, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__10_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__10);
v_key_1814_ = lean_uint64_lor(v___x_1812_, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1815_, 0, v_config_1807_);
lean_ctor_set_uint64(v___x_1815_, sizeof(void*)*1, v_key_1814_);
lean_inc(v_canUnfold_x3f_1801_);
lean_inc(v_synthPendingDepth_1800_);
lean_inc(v_defEqCtx_x3f_1799_);
lean_inc_ref(v_localInstances_1798_);
lean_inc_ref(v_lctx_1797_);
lean_inc(v_zetaDeltaSet_1796_);
v___x_1816_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v_zetaDeltaSet_1796_);
lean_ctor_set(v___x_1816_, 2, v_lctx_1797_);
lean_ctor_set(v___x_1816_, 3, v_localInstances_1798_);
lean_ctor_set(v___x_1816_, 4, v_defEqCtx_x3f_1799_);
lean_ctor_set(v___x_1816_, 5, v_synthPendingDepth_1800_);
lean_ctor_set(v___x_1816_, 6, v_canUnfold_x3f_1801_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*7, v_trackZetaDelta_1795_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*7 + 1, v_univApprox_1802_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1803_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*7 + 3, v_cacheInferType_1804_);
v___x_1817_ = l_Lean_Meta_mkProjection(v_struct_1736_, v___x_1811_, v___x_1816_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec_ref(v___x_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1828_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v_a_1818_);
v___x_1823_ = v___x_1742_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1825_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1823_);
v___x_1825_ = v___x_1820_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_del_object(v___x_1742_);
v_a_1829_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1817_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1817_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
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
lean_object* v_options_1840_; uint8_t v_hasTrace_1841_; 
lean_dec(v___x_1739_);
v_options_1840_ = lean_ctor_get(v___y_1725_, 2);
v_hasTrace_1841_ = lean_ctor_get_uint8(v_options_1840_, sizeof(void*)*1);
if (v_hasTrace_1841_ == 0)
{
goto v___jp_1731_;
}
else
{
lean_object* v_inheritedTraceOptions_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v_inheritedTraceOptions_1842_ = lean_ctor_get(v___y_1725_, 13);
v___x_1843_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___lam__0___closed__2));
v___x_1844_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__5, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__5);
v___x_1845_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1842_, v_options_1840_, v___x_1844_);
if (v___x_1845_ == 0)
{
goto v___jp_1731_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1846_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__12, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__12_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__12);
lean_inc(v_typeName_1734_);
v___x_1847_ = l_Lean_MessageData_ofName(v_typeName_1734_);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_obj_once(&l_Lean_Meta_Sym_foldProjs___lam__0___closed__14, &l_Lean_Meta_Sym_foldProjs___lam__0___closed__14_once, _init_l_Lean_Meta_Sym_foldProjs___lam__0___closed__14);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
lean_inc_ref(v_e_1722_);
v___x_1851_ = l_Lean_indentExpr(v_e_1722_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0(v___x_1843_, v___x_1852_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_dec_ref(v___x_1853_);
goto v___jp_1731_;
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_e_1722_);
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
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
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_e_1722_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
v___jp_1728_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_e_1722_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
v___jp_1731_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_e_1722_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__0___boxed(lean_object* v_e_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Meta_Sym_foldProjs___lam__0(v_e_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1(lean_object* v_x_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___lam__1___boxed(lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Meta_Sym_foldProjs___lam__1(v_x_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec_ref(v_x_1879_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs(lean_object* v_e_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v___f_1895_; lean_object* v___x_1896_; 
v___f_1895_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__0));
v___x_1896_ = lean_find_expr(v___f_1895_, v_e_1889_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v_e_1889_);
return v___x_1897_;
}
else
{
lean_object* v_post_1898_; lean_object* v___f_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; 
lean_dec_ref(v___x_1896_);
v_post_1898_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__1));
v___f_1899_ = ((lean_object*)(l_Lean_Meta_Sym_foldProjs___closed__2));
v___x_1900_ = 0;
v___x_1901_ = l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0(v_e_1889_, v___f_1899_, v_post_1898_, v___x_1900_, v___x_1900_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_foldProjs___boxed(lean_object* v_e_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Meta_Sym_foldProjs(v_e_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(lean_object* v_e_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v___x_1912_; 
v___x_1912_ = l_Lean_Expr_hasMVar(v_e_1909_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_e_1909_);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; lean_object* v_mctx_1915_; lean_object* v___x_1916_; lean_object* v_fst_1917_; lean_object* v_snd_1918_; lean_object* v___x_1919_; lean_object* v_cache_1920_; lean_object* v_zetaDeltaFVarIds_1921_; lean_object* v_postponed_1922_; lean_object* v_diag_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1932_; 
v___x_1914_ = lean_st_ref_get(v___y_1910_);
v_mctx_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_ref(v_mctx_1915_);
lean_dec(v___x_1914_);
v___x_1916_ = l_Lean_instantiateMVarsCore(v_mctx_1915_, v_e_1909_);
v_fst_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_fst_1917_);
v_snd_1918_ = lean_ctor_get(v___x_1916_, 1);
lean_inc(v_snd_1918_);
lean_dec_ref(v___x_1916_);
v___x_1919_ = lean_st_ref_take(v___y_1910_);
v_cache_1920_ = lean_ctor_get(v___x_1919_, 1);
v_zetaDeltaFVarIds_1921_ = lean_ctor_get(v___x_1919_, 2);
v_postponed_1922_ = lean_ctor_get(v___x_1919_, 3);
v_diag_1923_ = lean_ctor_get(v___x_1919_, 4);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1919_, 0);
lean_dec(v_unused_1933_);
v___x_1925_ = v___x_1919_;
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_diag_1923_);
lean_inc(v_postponed_1922_);
lean_inc(v_zetaDeltaFVarIds_1921_);
lean_inc(v_cache_1920_);
lean_dec(v___x_1919_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1932_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v_snd_1918_);
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_snd_1918_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_cache_1920_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_zetaDeltaFVarIds_1921_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_postponed_1922_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_diag_1923_);
v___x_1928_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = lean_st_ref_set(v___y_1910_, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_fst_1917_);
return v___x_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg___boxed(lean_object* v_e_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1934_, v___y_1935_);
lean_dec(v___y_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(lean_object* v_e_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1938_, v___y_1942_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___boxed(lean_object* v_e_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0(v_e_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(lean_object* v_e_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v___x_1964_; lean_object* v_a_1965_; lean_object* v___x_1966_; 
v___x_1964_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr_spec__0___redArg(v_e_1956_, v_a_1960_);
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1964_);
v___x_1966_ = l_Lean_Meta_Sym_unfoldReducible(v_a_1965_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1968_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref(v___x_1966_);
v___x_1968_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1967_, v_a_1958_);
return v___x_1968_;
}
else
{
return v___x_1966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr___boxed(lean_object* v_e_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_e_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_, lean_object* v_x_1981_){
_start:
{
lean_object* v_ks_1982_; lean_object* v_vs_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2007_; 
v_ks_1982_ = lean_ctor_get(v_x_1978_, 0);
v_vs_1983_ = lean_ctor_get(v_x_1978_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_x_1978_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1985_ = v_x_1978_;
v_isShared_1986_ = v_isSharedCheck_2007_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_vs_1983_);
lean_inc(v_ks_1982_);
lean_dec(v_x_1978_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2007_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = lean_array_get_size(v_ks_1982_);
v___x_1988_ = lean_nat_dec_lt(v_x_1979_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_dec(v_x_1979_);
v___x_1989_ = lean_array_push(v_ks_1982_, v_x_1980_);
v___x_1990_ = lean_array_push(v_vs_1983_, v_x_1981_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v___x_1990_);
lean_ctor_set(v___x_1985_, 0, v___x_1989_);
v___x_1992_ = v___x_1985_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v_k_x27_1994_; uint8_t v___x_1995_; 
v_k_x27_1994_ = lean_array_fget_borrowed(v_ks_1982_, v_x_1979_);
v___x_1995_ = l_Lean_instBEqFVarId_beq(v_x_1980_, v_k_x27_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1997_; 
if (v_isShared_1986_ == 0)
{
v___x_1997_ = v___x_1985_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_ks_1982_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_vs_1983_);
v___x_1997_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_nat_add(v_x_1979_, v___x_1998_);
lean_dec(v_x_1979_);
v_x_1978_ = v___x_1997_;
v_x_1979_ = v___x_1999_;
goto _start;
}
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2002_ = lean_array_fset(v_ks_1982_, v_x_1979_, v_x_1980_);
v___x_2003_ = lean_array_fset(v_vs_1983_, v_x_1979_, v_x_1981_);
lean_dec(v_x_1979_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v___x_2003_);
lean_ctor_set(v___x_1985_, 0, v___x_2002_);
v___x_2005_ = v___x_1985_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_2003_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2008_, lean_object* v_k_2009_, lean_object* v_v_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_n_2008_, v___x_2011_, v_k_2009_, v_v_2010_);
return v___x_2012_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_2013_; size_t v___x_2014_; size_t v___x_2015_; 
v___x_2013_ = ((size_t)5ULL);
v___x_2014_ = ((size_t)1ULL);
v___x_2015_ = lean_usize_shift_left(v___x_2014_, v___x_2013_);
return v___x_2015_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; 
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__0);
v___x_2018_ = lean_usize_sub(v___x_2017_, v___x_2016_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(lean_object* v_x_2020_, size_t v_x_2021_, size_t v_x_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
if (lean_obj_tag(v_x_2020_) == 0)
{
lean_object* v_es_2025_; size_t v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; size_t v___x_2029_; lean_object* v_j_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v_es_2025_ = lean_ctor_get(v_x_2020_, 0);
v___x_2026_ = ((size_t)5ULL);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_2029_ = lean_usize_land(v_x_2021_, v___x_2028_);
v_j_2030_ = lean_usize_to_nat(v___x_2029_);
v___x_2031_ = lean_array_get_size(v_es_2025_);
v___x_2032_ = lean_nat_dec_lt(v_j_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_dec(v_j_2030_);
lean_dec(v_x_2024_);
lean_dec(v_x_2023_);
return v_x_2020_;
}
else
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2069_; 
lean_inc_ref(v_es_2025_);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_x_2020_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; 
v_unused_2070_ = lean_ctor_get(v_x_2020_, 0);
lean_dec(v_unused_2070_);
v___x_2034_ = v_x_2020_;
v_isShared_2035_ = v_isSharedCheck_2069_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v_x_2020_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2069_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_v_2036_; lean_object* v___x_2037_; lean_object* v_xs_x27_2038_; lean_object* v___y_2040_; 
v_v_2036_ = lean_array_fget(v_es_2025_, v_j_2030_);
v___x_2037_ = lean_box(0);
v_xs_x27_2038_ = lean_array_fset(v_es_2025_, v_j_2030_, v___x_2037_);
switch(lean_obj_tag(v_v_2036_))
{
case 0:
{
lean_object* v_key_2045_; lean_object* v_val_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2056_; 
v_key_2045_ = lean_ctor_get(v_v_2036_, 0);
v_val_2046_ = lean_ctor_get(v_v_2036_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_v_2036_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2048_ = v_v_2036_;
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_val_2046_);
lean_inc(v_key_2045_);
lean_dec(v_v_2036_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
uint8_t v___x_2050_; 
v___x_2050_ = l_Lean_instBEqFVarId_beq(v_x_2023_, v_key_2045_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_del_object(v___x_2048_);
v___x_2051_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2045_, v_val_2046_, v_x_2023_, v_x_2024_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
v___y_2040_ = v___x_2052_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2054_; 
lean_dec(v_val_2046_);
lean_dec(v_key_2045_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 1, v_x_2024_);
lean_ctor_set(v___x_2048_, 0, v_x_2023_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_x_2023_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_x_2024_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
v___y_2040_ = v___x_2054_;
goto v___jp_2039_;
}
}
}
}
case 1:
{
lean_object* v_node_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2067_; 
v_node_2057_ = lean_ctor_get(v_v_2036_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_v_2036_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2059_ = v_v_2036_;
v_isShared_2060_ = v_isSharedCheck_2067_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_node_2057_);
lean_dec(v_v_2036_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2067_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2061_ = lean_usize_shift_right(v_x_2021_, v___x_2026_);
v___x_2062_ = lean_usize_add(v_x_2022_, v___x_2027_);
v___x_2063_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_node_2057_, v___x_2061_, v___x_2062_, v_x_2023_, v_x_2024_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2063_);
v___x_2065_ = v___x_2059_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
v___y_2040_ = v___x_2065_;
goto v___jp_2039_;
}
}
}
default: 
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v_x_2023_);
lean_ctor_set(v___x_2068_, 1, v_x_2024_);
v___y_2040_ = v___x_2068_;
goto v___jp_2039_;
}
}
v___jp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2041_ = lean_array_fset(v_xs_x27_2038_, v_j_2030_, v___y_2040_);
lean_dec(v_j_2030_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2041_);
v___x_2043_ = v___x_2034_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
else
{
lean_object* v_ks_2071_; lean_object* v_vs_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2092_; 
v_ks_2071_ = lean_ctor_get(v_x_2020_, 0);
v_vs_2072_ = lean_ctor_get(v_x_2020_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_x_2020_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2074_ = v_x_2020_;
v_isShared_2075_ = v_isSharedCheck_2092_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_vs_2072_);
lean_inc(v_ks_2071_);
lean_dec(v_x_2020_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2092_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_ks_2071_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_vs_2072_);
v___x_2077_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v_newNode_2078_; uint8_t v___y_2080_; size_t v___x_2086_; uint8_t v___x_2087_; 
v_newNode_2078_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v___x_2077_, v_x_2023_, v_x_2024_);
v___x_2086_ = ((size_t)7ULL);
v___x_2087_ = lean_usize_dec_le(v___x_2086_, v_x_2022_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2088_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2078_);
v___x_2089_ = lean_unsigned_to_nat(4u);
v___x_2090_ = lean_nat_dec_lt(v___x_2088_, v___x_2089_);
lean_dec(v___x_2088_);
v___y_2080_ = v___x_2090_;
goto v___jp_2079_;
}
else
{
v___y_2080_ = v___x_2087_;
goto v___jp_2079_;
}
v___jp_2079_:
{
if (v___y_2080_ == 0)
{
lean_object* v_ks_2081_; lean_object* v_vs_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v_ks_2081_ = lean_ctor_get(v_newNode_2078_, 0);
lean_inc_ref(v_ks_2081_);
v_vs_2082_ = lean_ctor_get(v_newNode_2078_, 1);
lean_inc_ref(v_vs_2082_);
lean_dec_ref(v_newNode_2078_);
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_2085_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_x_2022_, v_ks_2081_, v_vs_2082_, v___x_2083_, v___x_2084_);
lean_dec_ref(v_vs_2082_);
lean_dec_ref(v_ks_2081_);
return v___x_2085_;
}
else
{
return v_newNode_2078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(size_t v_depth_2093_, lean_object* v_keys_2094_, lean_object* v_vals_2095_, lean_object* v_i_2096_, lean_object* v_entries_2097_){
_start:
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = lean_array_get_size(v_keys_2094_);
v___x_2099_ = lean_nat_dec_lt(v_i_2096_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_dec(v_i_2096_);
return v_entries_2097_;
}
else
{
lean_object* v_k_2100_; lean_object* v_v_2101_; uint64_t v___x_2102_; size_t v_h_2103_; size_t v___x_2104_; lean_object* v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; size_t v_h_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_k_2100_ = lean_array_fget_borrowed(v_keys_2094_, v_i_2096_);
v_v_2101_ = lean_array_fget_borrowed(v_vals_2095_, v_i_2096_);
v___x_2102_ = l_Lean_instHashableFVarId_hash(v_k_2100_);
v_h_2103_ = lean_uint64_to_usize(v___x_2102_);
v___x_2104_ = ((size_t)5ULL);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_sub(v_depth_2093_, v___x_2106_);
v___x_2108_ = lean_usize_mul(v___x_2104_, v___x_2107_);
v_h_2109_ = lean_usize_shift_right(v_h_2103_, v___x_2108_);
v___x_2110_ = lean_nat_add(v_i_2096_, v___x_2105_);
lean_dec(v_i_2096_);
lean_inc(v_v_2101_);
lean_inc(v_k_2100_);
v___x_2111_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_entries_2097_, v_h_2109_, v_depth_2093_, v_k_2100_, v_v_2101_);
v_i_2096_ = v___x_2110_;
v_entries_2097_ = v___x_2111_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2113_, lean_object* v_keys_2114_, lean_object* v_vals_2115_, lean_object* v_i_2116_, lean_object* v_entries_2117_){
_start:
{
size_t v_depth_boxed_2118_; lean_object* v_res_2119_; 
v_depth_boxed_2118_ = lean_unbox_usize(v_depth_2113_);
lean_dec(v_depth_2113_);
v_res_2119_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2118_, v_keys_2114_, v_vals_2115_, v_i_2116_, v_entries_2117_);
lean_dec_ref(v_vals_2115_);
lean_dec_ref(v_keys_2114_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___boxed(lean_object* v_x_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_){
_start:
{
size_t v_x_9235__boxed_2125_; size_t v_x_9236__boxed_2126_; lean_object* v_res_2127_; 
v_x_9235__boxed_2125_ = lean_unbox_usize(v_x_2121_);
lean_dec(v_x_2121_);
v_x_9236__boxed_2126_ = lean_unbox_usize(v_x_2122_);
lean_dec(v_x_2122_);
v_res_2127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2120_, v_x_9235__boxed_2125_, v_x_9236__boxed_2126_, v_x_2123_, v_x_2124_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(lean_object* v_x_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_){
_start:
{
uint64_t v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2131_ = l_Lean_instHashableFVarId_hash(v_x_2129_);
v___x_2132_ = lean_uint64_to_usize(v___x_2131_);
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2128_, v___x_2132_, v___x_2133_, v_x_2129_, v_x_2130_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(lean_object* v_as_2135_, size_t v_sz_2136_, size_t v_i_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
uint8_t v___x_2146_; 
v___x_2146_ = lean_usize_dec_lt(v_i_2137_, v_sz_2136_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_b_2138_);
return v___x_2147_;
}
else
{
lean_object* v_snd_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2253_; 
v_snd_2148_ = lean_ctor_get(v_b_2138_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_b_2138_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v_b_2138_, 0);
lean_dec(v_unused_2254_);
v___x_2150_ = v_b_2138_;
v_isShared_2151_ = v_isSharedCheck_2253_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_snd_2148_);
lean_dec(v_b_2138_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2253_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v_a_2154_; lean_object* v_a_2161_; 
v___x_2152_ = lean_box(0);
v_a_2161_ = lean_array_uget(v_as_2135_, v_i_2137_);
if (lean_obj_tag(v_a_2161_) == 0)
{
v_a_2154_ = v_snd_2148_;
goto v___jp_2153_;
}
else
{
lean_object* v_snd_2162_; lean_object* v_val_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2252_; 
v_snd_2162_ = lean_ctor_get(v_snd_2148_, 1);
lean_inc(v_snd_2162_);
v_val_2163_ = lean_ctor_get(v_a_2161_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_a_2161_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2165_ = v_a_2161_;
v_isShared_2166_ = v_isSharedCheck_2252_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_val_2163_);
lean_dec(v_a_2161_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2252_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v_fst_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2250_; 
v_fst_2167_ = lean_ctor_get(v_snd_2148_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_snd_2148_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v_snd_2148_, 1);
lean_dec(v_unused_2251_);
v___x_2169_ = v_snd_2148_;
v_isShared_2170_ = v_isSharedCheck_2250_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_fst_2167_);
lean_dec(v_snd_2148_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2250_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v_fst_2171_; lean_object* v_snd_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2249_; 
v_fst_2171_ = lean_ctor_get(v_snd_2162_, 0);
v_snd_2172_ = lean_ctor_get(v_snd_2162_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_snd_2162_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2174_ = v_snd_2162_;
v_isShared_2175_ = v_isSharedCheck_2249_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snd_2172_);
lean_inc(v_fst_2171_);
lean_dec(v_snd_2162_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2249_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v_decl_2177_; 
if (lean_obj_tag(v_val_2163_) == 0)
{
lean_object* v_fvarId_2192_; lean_object* v_userName_2193_; lean_object* v_type_2194_; uint8_t v_bi_2195_; uint8_t v_kind_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2213_; 
v_fvarId_2192_ = lean_ctor_get(v_val_2163_, 1);
v_userName_2193_ = lean_ctor_get(v_val_2163_, 2);
v_type_2194_ = lean_ctor_get(v_val_2163_, 3);
v_bi_2195_ = lean_ctor_get_uint8(v_val_2163_, sizeof(void*)*4);
v_kind_2196_ = lean_ctor_get_uint8(v_val_2163_, sizeof(void*)*4 + 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_val_2163_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v_val_2163_, 0);
lean_dec(v_unused_2214_);
v___x_2198_ = v_val_2163_;
v_isShared_2199_ = v_isSharedCheck_2213_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_type_2194_);
lean_inc(v_userName_2193_);
lean_inc(v_fvarId_2192_);
lean_dec(v_val_2163_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2213_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; 
v___x_2200_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2194_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
lean_inc(v_snd_2172_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 3, v_a_2201_);
lean_ctor_set(v___x_2198_, 0, v_snd_2172_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_snd_2172_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_fvarId_2192_);
lean_ctor_set(v_reuseFailAlloc_2204_, 2, v_userName_2193_);
lean_ctor_set(v_reuseFailAlloc_2204_, 3, v_a_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*4, v_bi_2195_);
lean_ctor_set_uint8(v_reuseFailAlloc_2204_, sizeof(void*)*4 + 1, v_kind_2196_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
v_decl_2177_ = v___x_2203_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_del_object(v___x_2198_);
lean_dec(v_userName_2193_);
lean_dec(v_fvarId_2192_);
lean_del_object(v___x_2174_);
lean_dec(v_snd_2172_);
lean_dec(v_fst_2171_);
lean_del_object(v___x_2169_);
lean_dec(v_fst_2167_);
lean_del_object(v___x_2165_);
lean_del_object(v___x_2150_);
v_a_2205_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2200_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2200_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2215_; lean_object* v_userName_2216_; lean_object* v_type_2217_; lean_object* v_value_2218_; uint8_t v_nondep_2219_; uint8_t v_kind_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2247_; 
v_fvarId_2215_ = lean_ctor_get(v_val_2163_, 1);
v_userName_2216_ = lean_ctor_get(v_val_2163_, 2);
v_type_2217_ = lean_ctor_get(v_val_2163_, 3);
v_value_2218_ = lean_ctor_get(v_val_2163_, 4);
v_nondep_2219_ = lean_ctor_get_uint8(v_val_2163_, sizeof(void*)*5);
v_kind_2220_ = lean_ctor_get_uint8(v_val_2163_, sizeof(void*)*5 + 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_val_2163_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v_val_2163_, 0);
lean_dec(v_unused_2248_);
v___x_2222_ = v_val_2163_;
v_isShared_2223_ = v_isSharedCheck_2247_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_value_2218_);
lean_inc(v_type_2217_);
lean_inc(v_userName_2216_);
lean_inc(v_fvarId_2215_);
lean_dec(v_val_2163_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2247_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; 
v___x_2224_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2217_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2218_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref(v___x_2226_);
lean_inc(v_snd_2172_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 4, v_a_2227_);
lean_ctor_set(v___x_2222_, 3, v_a_2225_);
lean_ctor_set(v___x_2222_, 0, v_snd_2172_);
v___x_2229_ = v___x_2222_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_snd_2172_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_fvarId_2215_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_userName_2216_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_a_2225_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_a_2227_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*5, v_nondep_2219_);
lean_ctor_set_uint8(v_reuseFailAlloc_2230_, sizeof(void*)*5 + 1, v_kind_2220_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
v_decl_2177_ = v___x_2229_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_a_2225_);
lean_del_object(v___x_2222_);
lean_dec(v_userName_2216_);
lean_dec(v_fvarId_2215_);
lean_del_object(v___x_2174_);
lean_dec(v_snd_2172_);
lean_dec(v_fst_2171_);
lean_del_object(v___x_2169_);
lean_dec(v_fst_2167_);
lean_del_object(v___x_2165_);
lean_del_object(v___x_2150_);
v_a_2231_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2226_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2226_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_del_object(v___x_2222_);
lean_dec_ref(v_value_2218_);
lean_dec(v_userName_2216_);
lean_dec(v_fvarId_2215_);
lean_del_object(v___x_2174_);
lean_dec(v_snd_2172_);
lean_dec(v_fst_2171_);
lean_del_object(v___x_2169_);
lean_dec(v_fst_2167_);
lean_del_object(v___x_2165_);
lean_del_object(v___x_2150_);
v_a_2239_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2224_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2224_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
v___jp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_snd_2172_, v___x_2178_);
lean_dec(v_snd_2172_);
lean_inc_ref(v_decl_2177_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v_decl_2177_);
v___x_2181_ = v___x_2165_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_decl_2177_);
v___x_2181_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2182_ = l_Lean_PersistentArray_push___redArg(v_fst_2171_, v___x_2181_);
v___x_2183_ = l_Lean_LocalDecl_fvarId(v_decl_2177_);
v___x_2184_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2167_, v___x_2183_, v_decl_2177_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v___x_2179_);
lean_ctor_set(v___x_2174_, 0, v___x_2182_);
v___x_2186_ = v___x_2174_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2179_);
v___x_2186_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2188_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v___x_2186_);
lean_ctor_set(v___x_2169_, 0, v___x_2184_);
v___x_2188_ = v___x_2169_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v___x_2186_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
v_a_2154_ = v___x_2188_;
goto v___jp_2153_;
}
}
}
}
}
}
}
}
v___jp_2153_:
{
lean_object* v___x_2156_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_a_2154_);
lean_ctor_set(v___x_2150_, 0, v___x_2152_);
v___x_2156_ = v___x_2150_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_a_2154_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
size_t v___x_2157_; size_t v___x_2158_; 
v___x_2157_ = ((size_t)1ULL);
v___x_2158_ = lean_usize_add(v_i_2137_, v___x_2157_);
v_i_2137_ = v___x_2158_;
v_b_2138_ = v___x_2156_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8___boxed(lean_object* v_as_2255_, lean_object* v_sz_2256_, lean_object* v_i_2257_, lean_object* v_b_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
size_t v_sz_boxed_2266_; size_t v_i_boxed_2267_; lean_object* v_res_2268_; 
v_sz_boxed_2266_ = lean_unbox_usize(v_sz_2256_);
lean_dec(v_sz_2256_);
v_i_boxed_2267_ = lean_unbox_usize(v_i_2257_);
lean_dec(v_i_2257_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_2255_, v_sz_boxed_2266_, v_i_boxed_2267_, v_b_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v_as_2255_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(lean_object* v_as_2269_, size_t v_sz_2270_, size_t v_i_2271_, lean_object* v_b_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
uint8_t v___x_2280_; 
v___x_2280_ = lean_usize_dec_lt(v_i_2271_, v_sz_2270_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v_b_2272_);
return v___x_2281_;
}
else
{
lean_object* v_snd_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2387_; 
v_snd_2282_ = lean_ctor_get(v_b_2272_, 1);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_b_2272_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; 
v_unused_2388_ = lean_ctor_get(v_b_2272_, 0);
lean_dec(v_unused_2388_);
v___x_2284_ = v_b_2272_;
v_isShared_2285_ = v_isSharedCheck_2387_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_snd_2282_);
lean_dec(v_b_2272_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2387_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v_a_2288_; lean_object* v_a_2295_; 
v___x_2286_ = lean_box(0);
v_a_2295_ = lean_array_uget(v_as_2269_, v_i_2271_);
if (lean_obj_tag(v_a_2295_) == 0)
{
v_a_2288_ = v_snd_2282_;
goto v___jp_2287_;
}
else
{
lean_object* v_snd_2296_; lean_object* v_val_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2386_; 
v_snd_2296_ = lean_ctor_get(v_snd_2282_, 1);
lean_inc(v_snd_2296_);
v_val_2297_ = lean_ctor_get(v_a_2295_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_a_2295_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2299_ = v_a_2295_;
v_isShared_2300_ = v_isSharedCheck_2386_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_val_2297_);
lean_dec(v_a_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2386_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v_fst_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2384_; 
v_fst_2301_ = lean_ctor_get(v_snd_2282_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_snd_2282_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; 
v_unused_2385_ = lean_ctor_get(v_snd_2282_, 1);
lean_dec(v_unused_2385_);
v___x_2303_ = v_snd_2282_;
v_isShared_2304_ = v_isSharedCheck_2384_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_fst_2301_);
lean_dec(v_snd_2282_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2384_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_fst_2305_; lean_object* v_snd_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2383_; 
v_fst_2305_ = lean_ctor_get(v_snd_2296_, 0);
v_snd_2306_ = lean_ctor_get(v_snd_2296_, 1);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_snd_2296_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2308_ = v_snd_2296_;
v_isShared_2309_ = v_isSharedCheck_2383_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_snd_2306_);
lean_inc(v_fst_2305_);
lean_dec(v_snd_2296_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2383_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_decl_2311_; 
if (lean_obj_tag(v_val_2297_) == 0)
{
lean_object* v_fvarId_2326_; lean_object* v_userName_2327_; lean_object* v_type_2328_; uint8_t v_bi_2329_; uint8_t v_kind_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2347_; 
v_fvarId_2326_ = lean_ctor_get(v_val_2297_, 1);
v_userName_2327_ = lean_ctor_get(v_val_2297_, 2);
v_type_2328_ = lean_ctor_get(v_val_2297_, 3);
v_bi_2329_ = lean_ctor_get_uint8(v_val_2297_, sizeof(void*)*4);
v_kind_2330_ = lean_ctor_get_uint8(v_val_2297_, sizeof(void*)*4 + 1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_val_2297_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v_val_2297_, 0);
lean_dec(v_unused_2348_);
v___x_2332_ = v_val_2297_;
v_isShared_2333_ = v_isSharedCheck_2347_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_type_2328_);
lean_inc(v_userName_2327_);
lean_inc(v_fvarId_2326_);
lean_dec(v_val_2297_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2347_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; 
v___x_2334_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2328_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2337_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v___x_2334_);
lean_inc(v_snd_2306_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 3, v_a_2335_);
lean_ctor_set(v___x_2332_, 0, v_snd_2306_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_snd_2306_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_fvarId_2326_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_userName_2327_);
lean_ctor_set(v_reuseFailAlloc_2338_, 3, v_a_2335_);
lean_ctor_set_uint8(v_reuseFailAlloc_2338_, sizeof(void*)*4, v_bi_2329_);
lean_ctor_set_uint8(v_reuseFailAlloc_2338_, sizeof(void*)*4 + 1, v_kind_2330_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
v_decl_2311_ = v___x_2337_;
goto v___jp_2310_;
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_del_object(v___x_2332_);
lean_dec(v_userName_2327_);
lean_dec(v_fvarId_2326_);
lean_del_object(v___x_2308_);
lean_dec(v_snd_2306_);
lean_dec(v_fst_2305_);
lean_del_object(v___x_2303_);
lean_dec(v_fst_2301_);
lean_del_object(v___x_2299_);
lean_del_object(v___x_2284_);
v_a_2339_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2334_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2334_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2349_; lean_object* v_userName_2350_; lean_object* v_type_2351_; lean_object* v_value_2352_; uint8_t v_nondep_2353_; uint8_t v_kind_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2381_; 
v_fvarId_2349_ = lean_ctor_get(v_val_2297_, 1);
v_userName_2350_ = lean_ctor_get(v_val_2297_, 2);
v_type_2351_ = lean_ctor_get(v_val_2297_, 3);
v_value_2352_ = lean_ctor_get(v_val_2297_, 4);
v_nondep_2353_ = lean_ctor_get_uint8(v_val_2297_, sizeof(void*)*5);
v_kind_2354_ = lean_ctor_get_uint8(v_val_2297_, sizeof(void*)*5 + 1);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_val_2297_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v_val_2297_, 0);
lean_dec(v_unused_2382_);
v___x_2356_ = v_val_2297_;
v_isShared_2357_ = v_isSharedCheck_2381_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_value_2352_);
lean_inc(v_type_2351_);
lean_inc(v_userName_2350_);
lean_inc(v_fvarId_2349_);
lean_dec(v_val_2297_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2381_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; 
v___x_2358_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2351_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2358_);
v___x_2360_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2352_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref(v___x_2360_);
lean_inc(v_snd_2306_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 4, v_a_2361_);
lean_ctor_set(v___x_2356_, 3, v_a_2359_);
lean_ctor_set(v___x_2356_, 0, v_snd_2306_);
v___x_2363_ = v___x_2356_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_snd_2306_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_fvarId_2349_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_userName_2350_);
lean_ctor_set(v_reuseFailAlloc_2364_, 3, v_a_2359_);
lean_ctor_set(v_reuseFailAlloc_2364_, 4, v_a_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*5, v_nondep_2353_);
lean_ctor_set_uint8(v_reuseFailAlloc_2364_, sizeof(void*)*5 + 1, v_kind_2354_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
v_decl_2311_ = v___x_2363_;
goto v___jp_2310_;
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_a_2359_);
lean_del_object(v___x_2356_);
lean_dec(v_userName_2350_);
lean_dec(v_fvarId_2349_);
lean_del_object(v___x_2308_);
lean_dec(v_snd_2306_);
lean_dec(v_fst_2305_);
lean_del_object(v___x_2303_);
lean_dec(v_fst_2301_);
lean_del_object(v___x_2299_);
lean_del_object(v___x_2284_);
v_a_2365_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2360_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2360_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_del_object(v___x_2356_);
lean_dec_ref(v_value_2352_);
lean_dec(v_userName_2350_);
lean_dec(v_fvarId_2349_);
lean_del_object(v___x_2308_);
lean_dec(v_snd_2306_);
lean_dec(v_fst_2305_);
lean_del_object(v___x_2303_);
lean_dec(v_fst_2301_);
lean_del_object(v___x_2299_);
lean_del_object(v___x_2284_);
v_a_2373_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2358_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2358_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
v___jp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = lean_nat_add(v_snd_2306_, v___x_2312_);
lean_dec(v_snd_2306_);
lean_inc_ref(v_decl_2311_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v_decl_2311_);
v___x_2315_ = v___x_2299_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_decl_2311_);
v___x_2315_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2316_ = l_Lean_PersistentArray_push___redArg(v_fst_2305_, v___x_2315_);
v___x_2317_ = l_Lean_LocalDecl_fvarId(v_decl_2311_);
v___x_2318_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2301_, v___x_2317_, v_decl_2311_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v___x_2313_);
lean_ctor_set(v___x_2308_, 0, v___x_2316_);
v___x_2320_ = v___x_2308_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v___x_2313_);
v___x_2320_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 1, v___x_2320_);
lean_ctor_set(v___x_2303_, 0, v___x_2318_);
v___x_2322_ = v___x_2303_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
v_a_2288_ = v___x_2322_;
goto v___jp_2287_;
}
}
}
}
}
}
}
}
v___jp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 1, v_a_2288_);
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_a_2288_);
v___x_2290_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
size_t v___x_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = ((size_t)1ULL);
v___x_2292_ = lean_usize_add(v_i_2271_, v___x_2291_);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6_spec__8(v_as_2269_, v_sz_2270_, v___x_2292_, v___x_2290_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6___boxed(lean_object* v_as_2389_, lean_object* v_sz_2390_, lean_object* v_i_2391_, lean_object* v_b_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
size_t v_sz_boxed_2400_; size_t v_i_boxed_2401_; lean_object* v_res_2402_; 
v_sz_boxed_2400_ = lean_unbox_usize(v_sz_2390_);
lean_dec(v_sz_2390_);
v_i_boxed_2401_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_res_2402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_as_2389_, v_sz_boxed_2400_, v_i_boxed_2401_, v_b_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec_ref(v_as_2389_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(lean_object* v_init_2403_, lean_object* v_n_2404_, lean_object* v_b_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
if (lean_obj_tag(v_n_2404_) == 0)
{
lean_object* v_cs_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; size_t v_sz_2416_; size_t v___x_2417_; lean_object* v___x_2418_; 
v_cs_2413_ = lean_ctor_get(v_n_2404_, 0);
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v_b_2405_);
v_sz_2416_ = lean_array_size(v_cs_2413_);
v___x_2417_ = ((size_t)0ULL);
v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_2403_, v_cs_2413_, v_sz_2416_, v___x_2417_, v___x_2415_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2433_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2433_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2433_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_fst_2423_; 
v_fst_2423_ = lean_ctor_get(v_a_2419_, 0);
if (lean_obj_tag(v_fst_2423_) == 0)
{
lean_object* v_snd_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v_snd_2424_ = lean_ctor_get(v_a_2419_, 1);
lean_inc(v_snd_2424_);
lean_dec(v_a_2419_);
v___x_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_snd_2424_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2425_);
v___x_2427_ = v___x_2421_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
else
{
lean_object* v_val_2429_; lean_object* v___x_2431_; 
lean_inc_ref(v_fst_2423_);
lean_dec(v_a_2419_);
v_val_2429_ = lean_ctor_get(v_fst_2423_, 0);
lean_inc(v_val_2429_);
lean_dec_ref(v_fst_2423_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_val_2429_);
v___x_2431_ = v___x_2421_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_val_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
v_a_2434_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2418_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2418_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_vs_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; size_t v_sz_2445_; size_t v___x_2446_; lean_object* v___x_2447_; 
v_vs_2442_ = lean_ctor_get(v_n_2404_, 0);
v___x_2443_ = lean_box(0);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v_b_2405_);
v_sz_2445_ = lean_array_size(v_vs_2442_);
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__6(v_vs_2442_, v_sz_2445_, v___x_2446_, v___x_2444_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2462_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2462_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2462_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_fst_2452_; 
v_fst_2452_ = lean_ctor_get(v_a_2448_, 0);
if (lean_obj_tag(v_fst_2452_) == 0)
{
lean_object* v_snd_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v_snd_2453_ = lean_ctor_get(v_a_2448_, 1);
lean_inc(v_snd_2453_);
lean_dec(v_a_2448_);
v___x_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2454_, 0, v_snd_2453_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2454_);
v___x_2456_ = v___x_2450_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
else
{
lean_object* v_val_2458_; lean_object* v___x_2460_; 
lean_inc_ref(v_fst_2452_);
lean_dec(v_a_2448_);
v_val_2458_ = lean_ctor_get(v_fst_2452_, 0);
lean_inc(v_val_2458_);
lean_dec_ref(v_fst_2452_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_val_2458_);
v___x_2460_ = v___x_2450_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_val_2458_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
v_a_2463_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2447_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2447_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(lean_object* v_init_2471_, lean_object* v_as_2472_, size_t v_sz_2473_, size_t v_i_2474_, lean_object* v_b_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_usize_dec_lt(v_i_2474_, v_sz_2473_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2484_, 0, v_b_2475_);
return v___x_2484_;
}
else
{
lean_object* v_snd_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2519_; 
v_snd_2485_ = lean_ctor_get(v_b_2475_, 1);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_b_2475_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v_b_2475_, 0);
lean_dec(v_unused_2520_);
v___x_2487_ = v_b_2475_;
v_isShared_2488_ = v_isSharedCheck_2519_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_snd_2485_);
lean_dec(v_b_2475_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2519_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_a_2489_; lean_object* v___x_2490_; 
v_a_2489_ = lean_array_uget_borrowed(v_as_2472_, v_i_2474_);
lean_inc(v_snd_2485_);
v___x_2490_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2471_, v_a_2489_, v_snd_2485_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2510_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2493_ = v___x_2490_;
v_isShared_2494_ = v_isSharedCheck_2510_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2490_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2510_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
if (lean_obj_tag(v_a_2491_) == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_a_2491_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2495_);
v___x_2497_ = v___x_2487_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_snd_2485_);
v___x_2497_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2499_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___x_2497_);
v___x_2499_ = v___x_2493_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
lean_del_object(v___x_2493_);
lean_dec(v_snd_2485_);
v_a_2502_ = lean_ctor_get(v_a_2491_, 0);
lean_inc(v_a_2502_);
lean_dec_ref(v_a_2491_);
v___x_2503_ = lean_box(0);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 1, v_a_2502_);
lean_ctor_set(v___x_2487_, 0, v___x_2503_);
v___x_2505_ = v___x_2487_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_a_2502_);
v___x_2505_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
size_t v___x_2506_; size_t v___x_2507_; 
v___x_2506_ = ((size_t)1ULL);
v___x_2507_ = lean_usize_add(v_i_2474_, v___x_2506_);
v_i_2474_ = v___x_2507_;
v_b_2475_ = v___x_2505_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_del_object(v___x_2487_);
lean_dec(v_snd_2485_);
v_a_2511_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2490_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2490_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_init_2521_, lean_object* v_as_2522_, lean_object* v_sz_2523_, lean_object* v_i_2524_, lean_object* v_b_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
size_t v_sz_boxed_2533_; size_t v_i_boxed_2534_; lean_object* v_res_2535_; 
v_sz_boxed_2533_ = lean_unbox_usize(v_sz_2523_);
lean_dec(v_sz_2523_);
v_i_boxed_2534_ = lean_unbox_usize(v_i_2524_);
lean_dec(v_i_2524_);
v_res_2535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2_spec__5(v_init_2521_, v_as_2522_, v_sz_boxed_2533_, v_i_boxed_2534_, v_b_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v_as_2522_);
lean_dec_ref(v_init_2521_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2___boxed(lean_object* v_init_2536_, lean_object* v_n_2537_, lean_object* v_b_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2536_, v_n_2537_, v_b_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec_ref(v_n_2537_);
lean_dec_ref(v_init_2536_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(lean_object* v_as_2547_, size_t v_sz_2548_, size_t v_i_2549_, lean_object* v_b_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
uint8_t v___x_2558_; 
v___x_2558_ = lean_usize_dec_lt(v_i_2549_, v_sz_2548_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_b_2550_);
return v___x_2559_;
}
else
{
lean_object* v_snd_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2665_; 
v_snd_2560_ = lean_ctor_get(v_b_2550_, 1);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_b_2550_);
if (v_isSharedCheck_2665_ == 0)
{
lean_object* v_unused_2666_; 
v_unused_2666_ = lean_ctor_get(v_b_2550_, 0);
lean_dec(v_unused_2666_);
v___x_2562_ = v_b_2550_;
v_isShared_2563_ = v_isSharedCheck_2665_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snd_2560_);
lean_dec(v_b_2550_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2665_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; lean_object* v_a_2566_; lean_object* v_a_2573_; 
v___x_2564_ = lean_box(0);
v_a_2573_ = lean_array_uget(v_as_2547_, v_i_2549_);
if (lean_obj_tag(v_a_2573_) == 0)
{
v_a_2566_ = v_snd_2560_;
goto v___jp_2565_;
}
else
{
lean_object* v_snd_2574_; lean_object* v_val_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2664_; 
v_snd_2574_ = lean_ctor_get(v_snd_2560_, 1);
lean_inc(v_snd_2574_);
v_val_2575_ = lean_ctor_get(v_a_2573_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_a_2573_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2577_ = v_a_2573_;
v_isShared_2578_ = v_isSharedCheck_2664_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_val_2575_);
lean_dec(v_a_2573_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2664_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_fst_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2662_; 
v_fst_2579_ = lean_ctor_get(v_snd_2560_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_snd_2560_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; 
v_unused_2663_ = lean_ctor_get(v_snd_2560_, 1);
lean_dec(v_unused_2663_);
v___x_2581_ = v_snd_2560_;
v_isShared_2582_ = v_isSharedCheck_2662_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_fst_2579_);
lean_dec(v_snd_2560_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2662_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v_fst_2583_; lean_object* v_snd_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2661_; 
v_fst_2583_ = lean_ctor_get(v_snd_2574_, 0);
v_snd_2584_ = lean_ctor_get(v_snd_2574_, 1);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_snd_2574_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2586_ = v_snd_2574_;
v_isShared_2587_ = v_isSharedCheck_2661_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_snd_2584_);
lean_inc(v_fst_2583_);
lean_dec(v_snd_2574_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2661_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v_decl_2589_; 
if (lean_obj_tag(v_val_2575_) == 0)
{
lean_object* v_fvarId_2604_; lean_object* v_userName_2605_; lean_object* v_type_2606_; uint8_t v_bi_2607_; uint8_t v_kind_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2625_; 
v_fvarId_2604_ = lean_ctor_get(v_val_2575_, 1);
v_userName_2605_ = lean_ctor_get(v_val_2575_, 2);
v_type_2606_ = lean_ctor_get(v_val_2575_, 3);
v_bi_2607_ = lean_ctor_get_uint8(v_val_2575_, sizeof(void*)*4);
v_kind_2608_ = lean_ctor_get_uint8(v_val_2575_, sizeof(void*)*4 + 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_val_2575_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v_val_2575_, 0);
lean_dec(v_unused_2626_);
v___x_2610_ = v_val_2575_;
v_isShared_2611_ = v_isSharedCheck_2625_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_type_2606_);
lean_inc(v_userName_2605_);
lean_inc(v_fvarId_2604_);
lean_dec(v_val_2575_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2625_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; 
v___x_2612_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2606_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
lean_inc(v_snd_2584_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 3, v_a_2613_);
lean_ctor_set(v___x_2610_, 0, v_snd_2584_);
v___x_2615_ = v___x_2610_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_snd_2584_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_fvarId_2604_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_userName_2605_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_a_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*4, v_bi_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*4 + 1, v_kind_2608_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
v_decl_2589_ = v___x_2615_;
goto v___jp_2588_;
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_del_object(v___x_2610_);
lean_dec(v_userName_2605_);
lean_dec(v_fvarId_2604_);
lean_del_object(v___x_2586_);
lean_dec(v_snd_2584_);
lean_dec(v_fst_2583_);
lean_del_object(v___x_2581_);
lean_dec(v_fst_2579_);
lean_del_object(v___x_2577_);
lean_del_object(v___x_2562_);
v_a_2617_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2612_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2612_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2627_; lean_object* v_userName_2628_; lean_object* v_type_2629_; lean_object* v_value_2630_; uint8_t v_nondep_2631_; uint8_t v_kind_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2659_; 
v_fvarId_2627_ = lean_ctor_get(v_val_2575_, 1);
v_userName_2628_ = lean_ctor_get(v_val_2575_, 2);
v_type_2629_ = lean_ctor_get(v_val_2575_, 3);
v_value_2630_ = lean_ctor_get(v_val_2575_, 4);
v_nondep_2631_ = lean_ctor_get_uint8(v_val_2575_, sizeof(void*)*5);
v_kind_2632_ = lean_ctor_get_uint8(v_val_2575_, sizeof(void*)*5 + 1);
v_isSharedCheck_2659_ = !lean_is_exclusive(v_val_2575_);
if (v_isSharedCheck_2659_ == 0)
{
lean_object* v_unused_2660_; 
v_unused_2660_ = lean_ctor_get(v_val_2575_, 0);
lean_dec(v_unused_2660_);
v___x_2634_ = v_val_2575_;
v_isShared_2635_ = v_isSharedCheck_2659_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_value_2630_);
lean_inc(v_type_2629_);
lean_inc(v_userName_2628_);
lean_inc(v_fvarId_2627_);
lean_dec(v_val_2575_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2659_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; 
v___x_2636_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2629_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2638_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
v___x_2638_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2630_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref(v___x_2638_);
lean_inc(v_snd_2584_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 4, v_a_2639_);
lean_ctor_set(v___x_2634_, 3, v_a_2637_);
lean_ctor_set(v___x_2634_, 0, v_snd_2584_);
v___x_2641_ = v___x_2634_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_snd_2584_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_fvarId_2627_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_userName_2628_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_a_2637_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v_a_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, sizeof(void*)*5, v_nondep_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2642_, sizeof(void*)*5 + 1, v_kind_2632_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
v_decl_2589_ = v___x_2641_;
goto v___jp_2588_;
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_a_2637_);
lean_del_object(v___x_2634_);
lean_dec(v_userName_2628_);
lean_dec(v_fvarId_2627_);
lean_del_object(v___x_2586_);
lean_dec(v_snd_2584_);
lean_dec(v_fst_2583_);
lean_del_object(v___x_2581_);
lean_dec(v_fst_2579_);
lean_del_object(v___x_2577_);
lean_del_object(v___x_2562_);
v_a_2643_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2638_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2638_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_del_object(v___x_2634_);
lean_dec_ref(v_value_2630_);
lean_dec(v_userName_2628_);
lean_dec(v_fvarId_2627_);
lean_del_object(v___x_2586_);
lean_dec(v_snd_2584_);
lean_dec(v_fst_2583_);
lean_del_object(v___x_2581_);
lean_dec(v_fst_2579_);
lean_del_object(v___x_2577_);
lean_del_object(v___x_2562_);
v_a_2651_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2636_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2636_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
v___jp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2590_ = lean_unsigned_to_nat(1u);
v___x_2591_ = lean_nat_add(v_snd_2584_, v___x_2590_);
lean_dec(v_snd_2584_);
lean_inc_ref(v_decl_2589_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v_decl_2589_);
v___x_2593_ = v___x_2577_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_decl_2589_);
v___x_2593_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2594_ = l_Lean_PersistentArray_push___redArg(v_fst_2583_, v___x_2593_);
v___x_2595_ = l_Lean_LocalDecl_fvarId(v_decl_2589_);
v___x_2596_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2579_, v___x_2595_, v_decl_2589_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 1, v___x_2591_);
lean_ctor_set(v___x_2586_, 0, v___x_2594_);
v___x_2598_ = v___x_2586_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v___x_2591_);
v___x_2598_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2600_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 1, v___x_2598_);
lean_ctor_set(v___x_2581_, 0, v___x_2596_);
v___x_2600_ = v___x_2581_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
v_a_2566_ = v___x_2600_;
goto v___jp_2565_;
}
}
}
}
}
}
}
}
v___jp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v_a_2566_);
lean_ctor_set(v___x_2562_, 0, v___x_2564_);
v___x_2568_ = v___x_2562_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_a_2566_);
v___x_2568_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
size_t v___x_2569_; size_t v___x_2570_; 
v___x_2569_ = ((size_t)1ULL);
v___x_2570_ = lean_usize_add(v_i_2549_, v___x_2569_);
v_i_2549_ = v___x_2570_;
v_b_2550_ = v___x_2568_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8___boxed(lean_object* v_as_2667_, lean_object* v_sz_2668_, lean_object* v_i_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
size_t v_sz_boxed_2678_; size_t v_i_boxed_2679_; lean_object* v_res_2680_; 
v_sz_boxed_2678_ = lean_unbox_usize(v_sz_2668_);
lean_dec(v_sz_2668_);
v_i_boxed_2679_ = lean_unbox_usize(v_i_2669_);
lean_dec(v_i_2669_);
v_res_2680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2667_, v_sz_boxed_2678_, v_i_boxed_2679_, v_b_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v_as_2667_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(lean_object* v_as_2681_, size_t v_sz_2682_, size_t v_i_2683_, lean_object* v_b_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_2692_; 
v___x_2692_ = lean_usize_dec_lt(v_i_2683_, v_sz_2682_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v_b_2684_);
return v___x_2693_;
}
else
{
lean_object* v_snd_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2799_; 
v_snd_2694_ = lean_ctor_get(v_b_2684_, 1);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_b_2684_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v_b_2684_, 0);
lean_dec(v_unused_2800_);
v___x_2696_ = v_b_2684_;
v_isShared_2697_ = v_isSharedCheck_2799_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_snd_2694_);
lean_dec(v_b_2684_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2799_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v_a_2700_; lean_object* v_a_2707_; 
v___x_2698_ = lean_box(0);
v_a_2707_ = lean_array_uget(v_as_2681_, v_i_2683_);
if (lean_obj_tag(v_a_2707_) == 0)
{
v_a_2700_ = v_snd_2694_;
goto v___jp_2699_;
}
else
{
lean_object* v_snd_2708_; lean_object* v_val_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2798_; 
v_snd_2708_ = lean_ctor_get(v_snd_2694_, 1);
lean_inc(v_snd_2708_);
v_val_2709_ = lean_ctor_get(v_a_2707_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_a_2707_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2711_ = v_a_2707_;
v_isShared_2712_ = v_isSharedCheck_2798_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_val_2709_);
lean_dec(v_a_2707_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2798_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_fst_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2796_; 
v_fst_2713_ = lean_ctor_get(v_snd_2694_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_snd_2694_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; 
v_unused_2797_ = lean_ctor_get(v_snd_2694_, 1);
lean_dec(v_unused_2797_);
v___x_2715_ = v_snd_2694_;
v_isShared_2716_ = v_isSharedCheck_2796_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_fst_2713_);
lean_dec(v_snd_2694_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2796_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v_fst_2717_; lean_object* v_snd_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2795_; 
v_fst_2717_ = lean_ctor_get(v_snd_2708_, 0);
v_snd_2718_ = lean_ctor_get(v_snd_2708_, 1);
v_isSharedCheck_2795_ = !lean_is_exclusive(v_snd_2708_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2720_ = v_snd_2708_;
v_isShared_2721_ = v_isSharedCheck_2795_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_snd_2718_);
lean_inc(v_fst_2717_);
lean_dec(v_snd_2708_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2795_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v_decl_2723_; 
if (lean_obj_tag(v_val_2709_) == 0)
{
lean_object* v_fvarId_2738_; lean_object* v_userName_2739_; lean_object* v_type_2740_; uint8_t v_bi_2741_; uint8_t v_kind_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2759_; 
v_fvarId_2738_ = lean_ctor_get(v_val_2709_, 1);
v_userName_2739_ = lean_ctor_get(v_val_2709_, 2);
v_type_2740_ = lean_ctor_get(v_val_2709_, 3);
v_bi_2741_ = lean_ctor_get_uint8(v_val_2709_, sizeof(void*)*4);
v_kind_2742_ = lean_ctor_get_uint8(v_val_2709_, sizeof(void*)*4 + 1);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_val_2709_);
if (v_isSharedCheck_2759_ == 0)
{
lean_object* v_unused_2760_; 
v_unused_2760_ = lean_ctor_get(v_val_2709_, 0);
lean_dec(v_unused_2760_);
v___x_2744_ = v_val_2709_;
v_isShared_2745_ = v_isSharedCheck_2759_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_type_2740_);
lean_inc(v_userName_2739_);
lean_inc(v_fvarId_2738_);
lean_dec(v_val_2709_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2759_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; 
v___x_2746_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2740_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
lean_inc(v_snd_2718_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 3, v_a_2747_);
lean_ctor_set(v___x_2744_, 0, v_snd_2718_);
v___x_2749_ = v___x_2744_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_snd_2718_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_fvarId_2738_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v_userName_2739_);
lean_ctor_set(v_reuseFailAlloc_2750_, 3, v_a_2747_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*4, v_bi_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*4 + 1, v_kind_2742_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
v_decl_2723_ = v___x_2749_;
goto v___jp_2722_;
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_del_object(v___x_2744_);
lean_dec(v_userName_2739_);
lean_dec(v_fvarId_2738_);
lean_del_object(v___x_2720_);
lean_dec(v_snd_2718_);
lean_dec(v_fst_2717_);
lean_del_object(v___x_2715_);
lean_dec(v_fst_2713_);
lean_del_object(v___x_2711_);
lean_del_object(v___x_2696_);
v_a_2751_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2746_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2746_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
else
{
lean_object* v_fvarId_2761_; lean_object* v_userName_2762_; lean_object* v_type_2763_; lean_object* v_value_2764_; uint8_t v_nondep_2765_; uint8_t v_kind_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2793_; 
v_fvarId_2761_ = lean_ctor_get(v_val_2709_, 1);
v_userName_2762_ = lean_ctor_get(v_val_2709_, 2);
v_type_2763_ = lean_ctor_get(v_val_2709_, 3);
v_value_2764_ = lean_ctor_get(v_val_2709_, 4);
v_nondep_2765_ = lean_ctor_get_uint8(v_val_2709_, sizeof(void*)*5);
v_kind_2766_ = lean_ctor_get_uint8(v_val_2709_, sizeof(void*)*5 + 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_val_2709_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v_val_2709_, 0);
lean_dec(v_unused_2794_);
v___x_2768_ = v_val_2709_;
v_isShared_2769_ = v_isSharedCheck_2793_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_value_2764_);
lean_inc(v_type_2763_);
lean_inc(v_userName_2762_);
lean_inc(v_fvarId_2761_);
lean_dec(v_val_2709_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2793_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; 
v___x_2770_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_2763_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2772_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref(v___x_2770_);
v___x_2772_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_value_2764_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2775_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref(v___x_2772_);
lean_inc(v_snd_2718_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 4, v_a_2773_);
lean_ctor_set(v___x_2768_, 3, v_a_2771_);
lean_ctor_set(v___x_2768_, 0, v_snd_2718_);
v___x_2775_ = v___x_2768_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_snd_2718_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_fvarId_2761_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_userName_2762_);
lean_ctor_set(v_reuseFailAlloc_2776_, 3, v_a_2771_);
lean_ctor_set(v_reuseFailAlloc_2776_, 4, v_a_2773_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*5, v_nondep_2765_);
lean_ctor_set_uint8(v_reuseFailAlloc_2776_, sizeof(void*)*5 + 1, v_kind_2766_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
v_decl_2723_ = v___x_2775_;
goto v___jp_2722_;
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_a_2771_);
lean_del_object(v___x_2768_);
lean_dec(v_userName_2762_);
lean_dec(v_fvarId_2761_);
lean_del_object(v___x_2720_);
lean_dec(v_snd_2718_);
lean_dec(v_fst_2717_);
lean_del_object(v___x_2715_);
lean_dec(v_fst_2713_);
lean_del_object(v___x_2711_);
lean_del_object(v___x_2696_);
v_a_2777_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2772_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2772_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2768_);
lean_dec_ref(v_value_2764_);
lean_dec(v_userName_2762_);
lean_dec(v_fvarId_2761_);
lean_del_object(v___x_2720_);
lean_dec(v_snd_2718_);
lean_dec(v_fst_2717_);
lean_del_object(v___x_2715_);
lean_dec(v_fst_2713_);
lean_del_object(v___x_2711_);
lean_del_object(v___x_2696_);
v_a_2785_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2770_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2770_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
v___jp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2724_ = lean_unsigned_to_nat(1u);
v___x_2725_ = lean_nat_add(v_snd_2718_, v___x_2724_);
lean_dec(v_snd_2718_);
lean_inc_ref(v_decl_2723_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v_decl_2723_);
v___x_2727_ = v___x_2711_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_decl_2723_);
v___x_2727_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2728_ = l_Lean_PersistentArray_push___redArg(v_fst_2717_, v___x_2727_);
v___x_2729_ = l_Lean_LocalDecl_fvarId(v_decl_2723_);
v___x_2730_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_fst_2713_, v___x_2729_, v_decl_2723_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 1, v___x_2725_);
lean_ctor_set(v___x_2720_, 0, v___x_2728_);
v___x_2732_ = v___x_2720_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2725_);
v___x_2732_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2734_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v___x_2732_);
lean_ctor_set(v___x_2715_, 0, v___x_2730_);
v___x_2734_ = v___x_2715_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
v_a_2700_ = v___x_2734_;
goto v___jp_2699_;
}
}
}
}
}
}
}
}
v___jp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 1, v_a_2700_);
lean_ctor_set(v___x_2696_, 0, v___x_2698_);
v___x_2702_ = v___x_2696_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_a_2700_);
v___x_2702_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = ((size_t)1ULL);
v___x_2704_ = lean_usize_add(v_i_2683_, v___x_2703_);
v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3_spec__8(v_as_2681_, v_sz_2682_, v___x_2704_, v___x_2702_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3___boxed(lean_object* v_as_2801_, lean_object* v_sz_2802_, lean_object* v_i_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
size_t v_sz_boxed_2812_; size_t v_i_boxed_2813_; lean_object* v_res_2814_; 
v_sz_boxed_2812_ = lean_unbox_usize(v_sz_2802_);
lean_dec(v_sz_2802_);
v_i_boxed_2813_ = lean_unbox_usize(v_i_2803_);
lean_dec(v_i_2803_);
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_as_2801_, v_sz_boxed_2812_, v_i_boxed_2813_, v_b_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec_ref(v_as_2801_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(lean_object* v_t_2815_, lean_object* v_init_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_root_2824_; lean_object* v_tail_2825_; lean_object* v___x_2826_; 
v_root_2824_ = lean_ctor_get(v_t_2815_, 0);
v_tail_2825_ = lean_ctor_get(v_t_2815_, 1);
lean_inc_ref(v_init_2816_);
v___x_2826_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__2(v_init_2816_, v_root_2824_, v_init_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec_ref(v_init_2816_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2863_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2863_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2863_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
if (lean_obj_tag(v_a_2827_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; 
v_a_2831_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v_a_2827_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v_a_2831_);
v___x_2833_ = v___x_2829_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; size_t v_sz_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
lean_del_object(v___x_2829_);
v_a_2835_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_a_2835_);
lean_dec_ref(v_a_2827_);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v_a_2835_);
v_sz_2838_ = lean_array_size(v_tail_2825_);
v___x_2839_ = ((size_t)0ULL);
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1_spec__3(v_tail_2825_, v_sz_2838_, v___x_2839_, v___x_2837_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2854_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2854_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2854_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v_fst_2845_; 
v_fst_2845_ = lean_ctor_get(v_a_2841_, 0);
if (lean_obj_tag(v_fst_2845_) == 0)
{
lean_object* v_snd_2846_; lean_object* v___x_2848_; 
v_snd_2846_ = lean_ctor_get(v_a_2841_, 1);
lean_inc(v_snd_2846_);
lean_dec(v_a_2841_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_snd_2846_);
v___x_2848_ = v___x_2843_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_snd_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
else
{
lean_object* v_val_2850_; lean_object* v___x_2852_; 
lean_inc_ref(v_fst_2845_);
lean_dec(v_a_2841_);
v_val_2850_ = lean_ctor_get(v_fst_2845_, 0);
lean_inc(v_val_2850_);
lean_dec_ref(v_fst_2845_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v_val_2850_);
v___x_2852_ = v___x_2843_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_val_2850_);
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
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
v_a_2855_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2840_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2840_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
v_a_2864_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2826_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2826_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1___boxed(lean_object* v_t_2872_, lean_object* v_init_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_t_2872_, v_init_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec_ref(v_t_2872_);
return v_res_2881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_unsigned_to_nat(32u);
v___x_2883_ = lean_mk_empty_array_with_capacity(v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1(void){
_start:
{
size_t v___x_2885_; lean_object* v_index_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v_decls_2890_; 
v___x_2885_ = ((size_t)5ULL);
v_index_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_unsigned_to_nat(32u);
v___x_2888_ = lean_mk_empty_array_with_capacity(v___x_2887_);
v___x_2889_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__0);
v_decls_2890_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_decls_2890_, 0, v___x_2889_);
lean_ctor_set(v_decls_2890_, 1, v___x_2888_);
lean_ctor_set(v_decls_2890_, 2, v_index_2886_);
lean_ctor_set(v_decls_2890_, 3, v_index_2886_);
lean_ctor_set_usize(v_decls_2890_, 4, v___x_2885_);
return v_decls_2890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2(void){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3(void){
_start:
{
lean_object* v___x_2892_; lean_object* v_fvarIdToDecl_2893_; 
v___x_2892_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__2);
v_fvarIdToDecl_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fvarIdToDecl_2893_, 0, v___x_2892_);
return v_fvarIdToDecl_2893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4(void){
_start:
{
lean_object* v_index_2894_; lean_object* v_decls_2895_; lean_object* v___x_2896_; 
v_index_2894_ = lean_unsigned_to_nat(0u);
v_decls_2895_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__1);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v_decls_2895_);
lean_ctor_set(v___x_2896_, 1, v_index_2894_);
return v___x_2896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5(void){
_start:
{
lean_object* v___x_2897_; lean_object* v_fvarIdToDecl_2898_; lean_object* v___x_2899_; 
v___x_2897_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__4);
v_fvarIdToDecl_2898_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__3);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_fvarIdToDecl_2898_);
lean_ctor_set(v___x_2899_, 1, v___x_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(lean_object* v_lctx_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_decls_2908_; lean_object* v_auxDeclToFullName_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2937_; 
v_decls_2908_ = lean_ctor_get(v_lctx_2900_, 1);
v_auxDeclToFullName_2909_ = lean_ctor_get(v_lctx_2900_, 2);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_lctx_2900_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; 
v_unused_2938_ = lean_ctor_get(v_lctx_2900_, 0);
lean_dec(v_unused_2938_);
v___x_2911_ = v_lctx_2900_;
v_isShared_2912_ = v_isSharedCheck_2937_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_auxDeclToFullName_2909_);
lean_inc(v_decls_2908_);
lean_dec(v_lctx_2900_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2937_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5, &l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___closed__5);
v___x_2914_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__1(v_decls_2908_, v___x_2913_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec_ref(v_decls_2908_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2928_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2928_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2928_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_snd_2919_; lean_object* v_fst_2920_; lean_object* v_fst_2921_; lean_object* v___x_2923_; 
v_snd_2919_ = lean_ctor_get(v_a_2915_, 1);
lean_inc(v_snd_2919_);
v_fst_2920_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_fst_2920_);
lean_dec(v_a_2915_);
v_fst_2921_ = lean_ctor_get(v_snd_2919_, 0);
lean_inc(v_fst_2921_);
lean_dec(v_snd_2919_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v_fst_2921_);
lean_ctor_set(v___x_2911_, 0, v_fst_2920_);
v___x_2923_ = v___x_2911_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_fst_2920_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_fst_2921_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_auxDeclToFullName_2909_);
v___x_2923_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2925_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2923_);
v___x_2925_ = v___x_2917_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2923_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_del_object(v___x_2911_);
lean_dec(v_auxDeclToFullName_2909_);
v_a_2929_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2914_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2914_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx___boxed(lean_object* v_lctx_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0(lean_object* v_00_u03b2_2948_, lean_object* v_x_2949_, lean_object* v_x_2950_, lean_object* v_x_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0___redArg(v_x_2949_, v_x_2950_, v_x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(lean_object* v_00_u03b2_2953_, lean_object* v_x_2954_, size_t v_x_2955_, size_t v_x_2956_, lean_object* v_x_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg(v_x_2954_, v_x_2955_, v_x_2956_, v_x_2957_, v_x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2960_, lean_object* v_x_2961_, lean_object* v_x_2962_, lean_object* v_x_2963_, lean_object* v_x_2964_, lean_object* v_x_2965_){
_start:
{
size_t v_x_10744__boxed_2966_; size_t v_x_10745__boxed_2967_; lean_object* v_res_2968_; 
v_x_10744__boxed_2966_ = lean_unbox_usize(v_x_2962_);
lean_dec(v_x_2962_);
v_x_10745__boxed_2967_ = lean_unbox_usize(v_x_2963_);
lean_dec(v_x_2963_);
v_res_2968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0(v_00_u03b2_2960_, v_x_2961_, v_x_10744__boxed_2966_, v_x_10745__boxed_2967_, v_x_2964_, v_x_2965_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2969_, lean_object* v_n_2970_, lean_object* v_k_2971_, lean_object* v_v_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1___redArg(v_n_2970_, v_k_2971_, v_v_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2974_, size_t v_depth_2975_, lean_object* v_keys_2976_, lean_object* v_vals_2977_, lean_object* v_heq_2978_, lean_object* v_i_2979_, lean_object* v_entries_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___redArg(v_depth_2975_, v_keys_2976_, v_vals_2977_, v_i_2979_, v_entries_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2982_, lean_object* v_depth_2983_, lean_object* v_keys_2984_, lean_object* v_vals_2985_, lean_object* v_heq_2986_, lean_object* v_i_2987_, lean_object* v_entries_2988_){
_start:
{
size_t v_depth_boxed_2989_; lean_object* v_res_2990_; 
v_depth_boxed_2989_ = lean_unbox_usize(v_depth_2983_);
lean_dec(v_depth_2983_);
v_res_2990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__2(v_00_u03b2_2982_, v_depth_boxed_2989_, v_keys_2984_, v_vals_2985_, v_heq_2986_, v_i_2987_, v_entries_2988_);
lean_dec_ref(v_vals_2985_);
lean_dec_ref(v_keys_2984_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2992_, v_x_2993_, v_x_2994_, v_x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v_ks_3001_; lean_object* v_vs_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3026_; 
v_ks_3001_ = lean_ctor_get(v_x_2997_, 0);
v_vs_3002_ = lean_ctor_get(v_x_2997_, 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_x_2997_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3004_ = v_x_2997_;
v_isShared_3005_ = v_isSharedCheck_3026_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_vs_3002_);
lean_inc(v_ks_3001_);
lean_dec(v_x_2997_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3026_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = lean_array_get_size(v_ks_3001_);
v___x_3007_ = lean_nat_dec_lt(v_x_2998_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_dec(v_x_2998_);
v___x_3008_ = lean_array_push(v_ks_3001_, v_x_2999_);
v___x_3009_ = lean_array_push(v_vs_3002_, v_x_3000_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 1, v___x_3009_);
lean_ctor_set(v___x_3004_, 0, v___x_3008_);
v___x_3011_ = v___x_3004_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
else
{
lean_object* v_k_x27_3013_; uint8_t v___x_3014_; 
v_k_x27_3013_ = lean_array_fget_borrowed(v_ks_3001_, v_x_2998_);
v___x_3014_ = l_Lean_instBEqMVarId_beq(v_x_2999_, v_k_x27_3013_);
if (v___x_3014_ == 0)
{
lean_object* v___x_3016_; 
if (v_isShared_3005_ == 0)
{
v___x_3016_ = v___x_3004_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_ks_3001_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_vs_3002_);
v___x_3016_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_unsigned_to_nat(1u);
v___x_3018_ = lean_nat_add(v_x_2998_, v___x_3017_);
lean_dec(v_x_2998_);
v_x_2997_ = v___x_3016_;
v_x_2998_ = v___x_3018_;
goto _start;
}
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3021_ = lean_array_fset(v_ks_3001_, v_x_2998_, v_x_2999_);
v___x_3022_ = lean_array_fset(v_vs_3002_, v_x_2998_, v_x_3000_);
lean_dec(v_x_2998_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 1, v___x_3022_);
lean_ctor_set(v___x_3004_, 0, v___x_3021_);
v___x_3024_ = v___x_3004_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_3027_, lean_object* v_k_3028_, lean_object* v_v_3029_){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_3027_, v___x_3030_, v_k_3028_, v_v_3029_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3032_, size_t v_x_3033_, size_t v_x_3034_, lean_object* v_x_3035_, lean_object* v_x_3036_){
_start:
{
if (lean_obj_tag(v_x_3032_) == 0)
{
lean_object* v_es_3037_; size_t v___x_3038_; size_t v___x_3039_; size_t v___x_3040_; size_t v___x_3041_; lean_object* v_j_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_es_3037_ = lean_ctor_get(v_x_3032_, 0);
v___x_3038_ = ((size_t)5ULL);
v___x_3039_ = ((size_t)1ULL);
v___x_3040_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_3041_ = lean_usize_land(v_x_3033_, v___x_3040_);
v_j_3042_ = lean_usize_to_nat(v___x_3041_);
v___x_3043_ = lean_array_get_size(v_es_3037_);
v___x_3044_ = lean_nat_dec_lt(v_j_3042_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_dec(v_j_3042_);
lean_dec(v_x_3036_);
lean_dec(v_x_3035_);
return v_x_3032_;
}
else
{
lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3081_; 
lean_inc_ref(v_es_3037_);
v_isSharedCheck_3081_ = !lean_is_exclusive(v_x_3032_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v_x_3032_, 0);
lean_dec(v_unused_3082_);
v___x_3046_ = v_x_3032_;
v_isShared_3047_ = v_isSharedCheck_3081_;
goto v_resetjp_3045_;
}
else
{
lean_dec(v_x_3032_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3081_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v_v_3048_; lean_object* v___x_3049_; lean_object* v_xs_x27_3050_; lean_object* v___y_3052_; 
v_v_3048_ = lean_array_fget(v_es_3037_, v_j_3042_);
v___x_3049_ = lean_box(0);
v_xs_x27_3050_ = lean_array_fset(v_es_3037_, v_j_3042_, v___x_3049_);
switch(lean_obj_tag(v_v_3048_))
{
case 0:
{
lean_object* v_key_3057_; lean_object* v_val_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3068_; 
v_key_3057_ = lean_ctor_get(v_v_3048_, 0);
v_val_3058_ = lean_ctor_get(v_v_3048_, 1);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_v_3048_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3060_ = v_v_3048_;
v_isShared_3061_ = v_isSharedCheck_3068_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_val_3058_);
lean_inc(v_key_3057_);
lean_dec(v_v_3048_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3068_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_instBEqMVarId_beq(v_x_3035_, v_key_3057_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_del_object(v___x_3060_);
v___x_3063_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3057_, v_val_3058_, v_x_3035_, v_x_3036_);
v___x_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
v___y_3052_ = v___x_3064_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3066_; 
lean_dec(v_val_3058_);
lean_dec(v_key_3057_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 1, v_x_3036_);
lean_ctor_set(v___x_3060_, 0, v_x_3035_);
v___x_3066_ = v___x_3060_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_x_3035_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_x_3036_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
v___y_3052_ = v___x_3066_;
goto v___jp_3051_;
}
}
}
}
case 1:
{
lean_object* v_node_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3079_; 
v_node_3069_ = lean_ctor_get(v_v_3048_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_v_3048_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3071_ = v_v_3048_;
v_isShared_3072_ = v_isSharedCheck_3079_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_node_3069_);
lean_dec(v_v_3048_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3079_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3073_ = lean_usize_shift_right(v_x_3033_, v___x_3038_);
v___x_3074_ = lean_usize_add(v_x_3034_, v___x_3039_);
v___x_3075_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_node_3069_, v___x_3073_, v___x_3074_, v_x_3035_, v_x_3036_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3075_);
v___x_3077_ = v___x_3071_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
v___y_3052_ = v___x_3077_;
goto v___jp_3051_;
}
}
}
default: 
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3080_, 0, v_x_3035_);
lean_ctor_set(v___x_3080_, 1, v_x_3036_);
v___y_3052_ = v___x_3080_;
goto v___jp_3051_;
}
}
v___jp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3053_ = lean_array_fset(v_xs_x27_3050_, v_j_3042_, v___y_3052_);
lean_dec(v_j_3042_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 0, v___x_3053_);
v___x_3055_ = v___x_3046_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
else
{
lean_object* v_ks_3083_; lean_object* v_vs_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3104_; 
v_ks_3083_ = lean_ctor_get(v_x_3032_, 0);
v_vs_3084_ = lean_ctor_get(v_x_3032_, 1);
v_isSharedCheck_3104_ = !lean_is_exclusive(v_x_3032_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3086_ = v_x_3032_;
v_isShared_3087_ = v_isSharedCheck_3104_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_vs_3084_);
lean_inc(v_ks_3083_);
lean_dec(v_x_3032_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3104_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_ks_3083_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_vs_3084_);
v___x_3089_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v_newNode_3090_; uint8_t v___y_3092_; size_t v___x_3098_; uint8_t v___x_3099_; 
v_newNode_3090_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v___x_3089_, v_x_3035_, v_x_3036_);
v___x_3098_ = ((size_t)7ULL);
v___x_3099_ = lean_usize_dec_le(v___x_3098_, v_x_3034_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3100_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3090_);
v___x_3101_ = lean_unsigned_to_nat(4u);
v___x_3102_ = lean_nat_dec_lt(v___x_3100_, v___x_3101_);
lean_dec(v___x_3100_);
v___y_3092_ = v___x_3102_;
goto v___jp_3091_;
}
else
{
v___y_3092_ = v___x_3099_;
goto v___jp_3091_;
}
v___jp_3091_:
{
if (v___y_3092_ == 0)
{
lean_object* v_ks_3093_; lean_object* v_vs_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_ks_3093_ = lean_ctor_get(v_newNode_3090_, 0);
lean_inc_ref(v_ks_3093_);
v_vs_3094_ = lean_ctor_get(v_newNode_3090_, 1);
lean_inc_ref(v_vs_3094_);
lean_dec_ref(v_newNode_3090_);
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__2);
v___x_3097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3034_, v_ks_3093_, v_vs_3094_, v___x_3095_, v___x_3096_);
lean_dec_ref(v_vs_3094_);
lean_dec_ref(v_ks_3093_);
return v___x_3097_;
}
else
{
return v_newNode_3090_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_3105_, lean_object* v_keys_3106_, lean_object* v_vals_3107_, lean_object* v_i_3108_, lean_object* v_entries_3109_){
_start:
{
lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = lean_array_get_size(v_keys_3106_);
v___x_3111_ = lean_nat_dec_lt(v_i_3108_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_dec(v_i_3108_);
return v_entries_3109_;
}
else
{
lean_object* v_k_3112_; lean_object* v_v_3113_; uint64_t v___x_3114_; size_t v_h_3115_; size_t v___x_3116_; lean_object* v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; size_t v___x_3120_; size_t v_h_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_k_3112_ = lean_array_fget_borrowed(v_keys_3106_, v_i_3108_);
v_v_3113_ = lean_array_fget_borrowed(v_vals_3107_, v_i_3108_);
v___x_3114_ = l_Lean_instHashableMVarId_hash(v_k_3112_);
v_h_3115_ = lean_uint64_to_usize(v___x_3114_);
v___x_3116_ = ((size_t)5ULL);
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = ((size_t)1ULL);
v___x_3119_ = lean_usize_sub(v_depth_3105_, v___x_3118_);
v___x_3120_ = lean_usize_mul(v___x_3116_, v___x_3119_);
v_h_3121_ = lean_usize_shift_right(v_h_3115_, v___x_3120_);
v___x_3122_ = lean_nat_add(v_i_3108_, v___x_3117_);
lean_dec(v_i_3108_);
lean_inc(v_v_3113_);
lean_inc(v_k_3112_);
v___x_3123_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_entries_3109_, v_h_3121_, v_depth_3105_, v_k_3112_, v_v_3113_);
v_i_3108_ = v___x_3122_;
v_entries_3109_ = v___x_3123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_3125_, lean_object* v_keys_3126_, lean_object* v_vals_3127_, lean_object* v_i_3128_, lean_object* v_entries_3129_){
_start:
{
size_t v_depth_boxed_3130_; lean_object* v_res_3131_; 
v_depth_boxed_3130_ = lean_unbox_usize(v_depth_3125_);
lean_dec(v_depth_3125_);
v_res_3131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_3130_, v_keys_3126_, v_vals_3127_, v_i_3128_, v_entries_3129_);
lean_dec_ref(v_vals_3127_);
lean_dec_ref(v_keys_3126_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3132_, lean_object* v_x_3133_, lean_object* v_x_3134_, lean_object* v_x_3135_, lean_object* v_x_3136_){
_start:
{
size_t v_x_2256__boxed_3137_; size_t v_x_2257__boxed_3138_; lean_object* v_res_3139_; 
v_x_2256__boxed_3137_ = lean_unbox_usize(v_x_3133_);
lean_dec(v_x_3133_);
v_x_2257__boxed_3138_ = lean_unbox_usize(v_x_3134_);
lean_dec(v_x_3134_);
v_res_3139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_3132_, v_x_2256__boxed_3137_, v_x_2257__boxed_3138_, v_x_3135_, v_x_3136_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(lean_object* v_x_3140_, lean_object* v_x_3141_, lean_object* v_x_3142_){
_start:
{
uint64_t v___x_3143_; size_t v___x_3144_; size_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3143_ = l_Lean_instHashableMVarId_hash(v_x_3141_);
v___x_3144_ = lean_uint64_to_usize(v___x_3143_);
v___x_3145_ = ((size_t)1ULL);
v___x_3146_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_3140_, v___x_3144_, v___x_3145_, v_x_3141_, v_x_3142_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(lean_object* v_mvarId_3147_, lean_object* v_val_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; lean_object* v_mctx_3152_; lean_object* v_cache_3153_; lean_object* v_zetaDeltaFVarIds_3154_; lean_object* v_postponed_3155_; lean_object* v_diag_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3184_; 
v___x_3151_ = lean_st_ref_take(v___y_3149_);
v_mctx_3152_ = lean_ctor_get(v___x_3151_, 0);
v_cache_3153_ = lean_ctor_get(v___x_3151_, 1);
v_zetaDeltaFVarIds_3154_ = lean_ctor_get(v___x_3151_, 2);
v_postponed_3155_ = lean_ctor_get(v___x_3151_, 3);
v_diag_3156_ = lean_ctor_get(v___x_3151_, 4);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3158_ = v___x_3151_;
v_isShared_3159_ = v_isSharedCheck_3184_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_diag_3156_);
lean_inc(v_postponed_3155_);
lean_inc(v_zetaDeltaFVarIds_3154_);
lean_inc(v_cache_3153_);
lean_inc(v_mctx_3152_);
lean_dec(v___x_3151_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3184_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v_depth_3160_; lean_object* v_levelAssignDepth_3161_; lean_object* v_lmvarCounter_3162_; lean_object* v_mvarCounter_3163_; lean_object* v_lDecls_3164_; lean_object* v_decls_3165_; lean_object* v_userNames_3166_; lean_object* v_lAssignment_3167_; lean_object* v_eAssignment_3168_; lean_object* v_dAssignment_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3183_; 
v_depth_3160_ = lean_ctor_get(v_mctx_3152_, 0);
v_levelAssignDepth_3161_ = lean_ctor_get(v_mctx_3152_, 1);
v_lmvarCounter_3162_ = lean_ctor_get(v_mctx_3152_, 2);
v_mvarCounter_3163_ = lean_ctor_get(v_mctx_3152_, 3);
v_lDecls_3164_ = lean_ctor_get(v_mctx_3152_, 4);
v_decls_3165_ = lean_ctor_get(v_mctx_3152_, 5);
v_userNames_3166_ = lean_ctor_get(v_mctx_3152_, 6);
v_lAssignment_3167_ = lean_ctor_get(v_mctx_3152_, 7);
v_eAssignment_3168_ = lean_ctor_get(v_mctx_3152_, 8);
v_dAssignment_3169_ = lean_ctor_get(v_mctx_3152_, 9);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_mctx_3152_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3171_ = v_mctx_3152_;
v_isShared_3172_ = v_isSharedCheck_3183_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_dAssignment_3169_);
lean_inc(v_eAssignment_3168_);
lean_inc(v_lAssignment_3167_);
lean_inc(v_userNames_3166_);
lean_inc(v_decls_3165_);
lean_inc(v_lDecls_3164_);
lean_inc(v_mvarCounter_3163_);
lean_inc(v_lmvarCounter_3162_);
lean_inc(v_levelAssignDepth_3161_);
lean_inc(v_depth_3160_);
lean_dec(v_mctx_3152_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3183_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3173_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_eAssignment_3168_, v_mvarId_3147_, v_val_3148_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 8, v___x_3173_);
v___x_3175_ = v___x_3171_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_depth_3160_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_levelAssignDepth_3161_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_lmvarCounter_3162_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_mvarCounter_3163_);
lean_ctor_set(v_reuseFailAlloc_3182_, 4, v_lDecls_3164_);
lean_ctor_set(v_reuseFailAlloc_3182_, 5, v_decls_3165_);
lean_ctor_set(v_reuseFailAlloc_3182_, 6, v_userNames_3166_);
lean_ctor_set(v_reuseFailAlloc_3182_, 7, v_lAssignment_3167_);
lean_ctor_set(v_reuseFailAlloc_3182_, 8, v___x_3173_);
lean_ctor_set(v_reuseFailAlloc_3182_, 9, v_dAssignment_3169_);
v___x_3175_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3177_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 0, v___x_3175_);
v___x_3177_ = v___x_3158_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_cache_3153_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_zetaDeltaFVarIds_3154_);
lean_ctor_set(v_reuseFailAlloc_3181_, 3, v_postponed_3155_);
lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_diag_3156_);
v___x_3177_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = lean_st_ref_set(v___y_3149_, v___x_3177_);
v___x_3179_ = lean_box(0);
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
return v___x_3180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg___boxed(lean_object* v_mvarId_3185_, lean_object* v_val_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_3185_, v_val_3186_, v___y_3187_);
lean_dec(v___y_3187_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object* v_mvarId_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v___x_3198_; 
lean_inc(v_mvarId_3190_);
v___x_3198_ = l_Lean_MVarId_getDecl(v_mvarId_3190_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v_userName_3200_; lean_object* v_lctx_3201_; lean_object* v_type_3202_; lean_object* v_localInstances_3203_; lean_object* v___x_3204_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref(v___x_3198_);
v_userName_3200_ = lean_ctor_get(v_a_3199_, 0);
lean_inc(v_userName_3200_);
v_lctx_3201_ = lean_ctor_get(v_a_3199_, 1);
lean_inc_ref(v_lctx_3201_);
v_type_3202_ = lean_ctor_get(v_a_3199_, 2);
lean_inc_ref(v_type_3202_);
v_localInstances_3203_ = lean_ctor_get(v_a_3199_, 4);
lean_inc_ref(v_localInstances_3203_);
lean_dec(v_a_3199_);
v___x_3204_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx(v_lctx_3201_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessExpr(v_type_3202_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; uint8_t v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref(v___x_3206_);
v___x_3208_ = 2;
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_3205_, v_localInstances_3203_, v_a_3207_, v___x_3208_, v_userName_3200_, v___x_3209_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3220_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc_n(v_a_3211_, 2);
lean_dec_ref(v___x_3210_);
v___x_3212_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_3190_, v_a_3211_, v_a_3194_);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v___x_3212_, 0);
lean_dec(v_unused_3221_);
v___x_3214_ = v___x_3212_;
v_isShared_3215_ = v_isSharedCheck_3220_;
goto v_resetjp_3213_;
}
else
{
lean_dec(v___x_3212_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3220_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; lean_object* v___x_3218_; 
v___x_3216_ = l_Lean_Expr_mvarId_x21(v_a_3211_);
lean_dec(v_a_3211_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v___x_3216_);
v___x_3218_ = v___x_3214_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec(v_mvarId_3190_);
v_a_3222_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_3210_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3210_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec(v_a_3205_);
lean_dec_ref(v_localInstances_3203_);
lean_dec(v_userName_3200_);
lean_dec(v_mvarId_3190_);
v_a_3230_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3206_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3206_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v_localInstances_3203_);
lean_dec_ref(v_type_3202_);
lean_dec(v_userName_3200_);
lean_dec(v_mvarId_3190_);
v_a_3238_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3204_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3204_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec(v_mvarId_3190_);
v_a_3246_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3198_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3198_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_preprocessMVar___boxed(lean_object* v_mvarId_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(lean_object* v_mvarId_3263_, lean_object* v_val_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___redArg(v_mvarId_3263_, v_val_3264_, v___y_3268_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0___boxed(lean_object* v_mvarId_3273_, lean_object* v_val_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0(v_mvarId_3273_, v_val_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0(lean_object* v_00_u03b2_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0___redArg(v_x_3284_, v_x_3285_, v_x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3288_, lean_object* v_x_3289_, size_t v_x_3290_, size_t v_x_3291_, lean_object* v_x_3292_, lean_object* v_x_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___redArg(v_x_3289_, v_x_3290_, v_x_3291_, v_x_3292_, v_x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_, lean_object* v_x_3300_){
_start:
{
size_t v_x_2610__boxed_3301_; size_t v_x_2611__boxed_3302_; lean_object* v_res_3303_; 
v_x_2610__boxed_3301_ = lean_unbox_usize(v_x_3297_);
lean_dec(v_x_3297_);
v_x_2611__boxed_3302_ = lean_unbox_usize(v_x_3298_);
lean_dec(v_x_3298_);
v_res_3303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1(v_00_u03b2_3295_, v_x_3296_, v_x_2610__boxed_3301_, v_x_2611__boxed_3302_, v_x_3299_, v_x_3300_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3304_, lean_object* v_n_3305_, lean_object* v_k_3306_, lean_object* v_v_3307_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2___redArg(v_n_3305_, v_k_3306_, v_v_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3309_, size_t v_depth_3310_, lean_object* v_keys_3311_, lean_object* v_vals_3312_, lean_object* v_heq_3313_, lean_object* v_i_3314_, lean_object* v_entries_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_3310_, v_keys_3311_, v_vals_3312_, v_i_3314_, v_entries_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3317_, lean_object* v_depth_3318_, lean_object* v_keys_3319_, lean_object* v_vals_3320_, lean_object* v_heq_3321_, lean_object* v_i_3322_, lean_object* v_entries_3323_){
_start:
{
size_t v_depth_boxed_3324_; lean_object* v_res_3325_; 
v_depth_boxed_3324_ = lean_unbox_usize(v_depth_3318_);
lean_dec(v_depth_3318_);
v_res_3325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3317_, v_depth_boxed_3324_, v_keys_3319_, v_vals_3320_, v_heq_3321_, v_i_3322_, v_entries_3323_);
lean_dec_ref(v_vals_3320_);
lean_dec_ref(v_keys_3319_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_preprocessMVar_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3327_, v_x_3328_, v_x_3329_, v_x_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(lean_object* v_msg_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v_ref_3338_; lean_object* v___x_3339_; lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3348_; 
v_ref_3338_ = lean_ctor_get(v___y_3335_, 5);
v___x_3339_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0_spec__0(v_msg_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3342_ = v___x_3339_;
v_isShared_3343_ = v_isSharedCheck_3348_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3339_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3348_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3344_; lean_object* v___x_3346_; 
lean_inc(v_ref_3338_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v_ref_3338_);
lean_ctor_set(v___x_3344_, 1, v_a_3340_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set_tag(v___x_3342_, 1);
lean_ctor_set(v___x_3342_, 0, v___x_3344_);
v___x_3346_ = v___x_3342_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg___boxed(lean_object* v_msg_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
return v_res_3355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__0));
v___x_3358_ = l_Lean_stringToMessageData(v___x_3357_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(lean_object* v_msg_3361_, lean_object* v_e_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v___y_3371_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Sym_foldProjs_spec__0___closed__1));
v___x_3379_ = lean_string_dec_eq(v_msg_3361_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__2));
v___x_3381_ = lean_string_append(v___x_3380_, v_msg_3361_);
lean_dec_ref(v_msg_3361_);
v___x_3382_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__3));
v___x_3383_ = lean_string_append(v___x_3381_, v___x_3382_);
v___y_3371_ = v___x_3383_;
goto v___jp_3370_;
}
else
{
v___y_3371_ = v_msg_3361_;
goto v___jp_3370_;
}
v___jp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3372_ = l_Lean_stringToMessageData(v___y_3371_);
v___x_3373_ = lean_obj_once(&l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1, &l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1_once, _init_l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___closed__1);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3372_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Lean_indentExpr(v_e_3362_);
v___x_3376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v___x_3376_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
return v___x_3377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared___boxed(lean_object* v_msg_3384_, lean_object* v_e_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3384_, v_e_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(lean_object* v_00_u03b1_3394_, lean_object* v_msg_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___redArg(v_msg_3395_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0___boxed(lean_object* v_00_u03b1_3404_, lean_object* v_msg_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared_spec__0(v_00_u03b1_3404_, v_msg_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3414_, lean_object* v_vals_3415_, lean_object* v_i_3416_, lean_object* v_k_3417_){
_start:
{
lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3418_ = lean_array_get_size(v_keys_3414_);
v___x_3419_ = lean_nat_dec_lt(v_i_3416_, v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; 
lean_dec_ref(v_k_3417_);
lean_dec(v_i_3416_);
v___x_3420_ = lean_box(0);
return v___x_3420_;
}
else
{
lean_object* v_k_x27_3421_; uint8_t v___x_3422_; 
v_k_x27_3421_ = lean_array_fget_borrowed(v_keys_3414_, v_i_3416_);
lean_inc(v_k_x27_3421_);
lean_inc_ref(v_k_3417_);
v___x_3422_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_k_3417_, v_k_x27_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_unsigned_to_nat(1u);
v___x_3424_ = lean_nat_add(v_i_3416_, v___x_3423_);
lean_dec(v_i_3416_);
v_i_3416_ = v___x_3424_;
goto _start;
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_dec_ref(v_k_3417_);
v___x_3426_ = lean_array_fget_borrowed(v_vals_3415_, v_i_3416_);
lean_dec(v_i_3416_);
lean_inc(v___x_3426_);
lean_inc(v_k_x27_3421_);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v_k_x27_3421_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
return v___x_3428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3429_, lean_object* v_vals_3430_, lean_object* v_i_3431_, lean_object* v_k_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3429_, v_vals_3430_, v_i_3431_, v_k_3432_);
lean_dec_ref(v_vals_3430_);
lean_dec_ref(v_keys_3429_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(lean_object* v_x_3434_, size_t v_x_3435_, lean_object* v_x_3436_){
_start:
{
if (lean_obj_tag(v_x_3434_) == 0)
{
lean_object* v_es_3437_; lean_object* v___x_3438_; size_t v___x_3439_; size_t v___x_3440_; size_t v___x_3441_; lean_object* v_j_3442_; lean_object* v___x_3443_; 
v_es_3437_ = lean_ctor_get(v_x_3434_, 0);
lean_inc_ref(v_es_3437_);
lean_dec_ref(v_x_3434_);
v___x_3438_ = lean_box(2);
v___x_3439_ = ((size_t)5ULL);
v___x_3440_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_preprocessLCtx_spec__0_spec__0___redArg___closed__1);
v___x_3441_ = lean_usize_land(v_x_3435_, v___x_3440_);
v_j_3442_ = lean_usize_to_nat(v___x_3441_);
v___x_3443_ = lean_array_get(v___x_3438_, v_es_3437_, v_j_3442_);
lean_dec(v_j_3442_);
lean_dec_ref(v_es_3437_);
switch(lean_obj_tag(v___x_3443_))
{
case 0:
{
lean_object* v_key_3444_; lean_object* v_val_3445_; uint8_t v___x_3446_; 
v_key_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc_n(v_key_3444_, 2);
v_val_3445_ = lean_ctor_get(v___x_3443_, 1);
lean_inc(v_val_3445_);
lean_dec_ref(v___x_3443_);
v___x_3446_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(v_x_3436_, v_key_3444_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec(v_val_3445_);
lean_dec(v_key_3444_);
v___x_3447_ = lean_box(0);
return v___x_3447_;
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v_key_3444_);
lean_ctor_set(v___x_3448_, 1, v_val_3445_);
v___x_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
return v___x_3449_;
}
}
case 1:
{
lean_object* v_node_3450_; size_t v___x_3451_; 
v_node_3450_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_node_3450_);
lean_dec_ref(v___x_3443_);
v___x_3451_ = lean_usize_shift_right(v_x_3435_, v___x_3439_);
v_x_3434_ = v_node_3450_;
v_x_3435_ = v___x_3451_;
goto _start;
}
default: 
{
lean_object* v___x_3453_; 
lean_dec_ref(v_x_3436_);
v___x_3453_ = lean_box(0);
return v___x_3453_;
}
}
}
else
{
lean_object* v_ks_3454_; lean_object* v_vs_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_ks_3454_ = lean_ctor_get(v_x_3434_, 0);
lean_inc_ref(v_ks_3454_);
v_vs_3455_ = lean_ctor_get(v_x_3434_, 1);
lean_inc_ref(v_vs_3455_);
lean_dec_ref(v_x_3434_);
v___x_3456_ = lean_unsigned_to_nat(0u);
v___x_3457_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_ks_3454_, v_vs_3455_, v___x_3456_, v_x_3436_);
lean_dec_ref(v_vs_3455_);
lean_dec_ref(v_ks_3454_);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg___boxed(lean_object* v_x_3458_, lean_object* v_x_3459_, lean_object* v_x_3460_){
_start:
{
size_t v_x_7444__boxed_3461_; lean_object* v_res_3462_; 
v_x_7444__boxed_3461_ = lean_unbox_usize(v_x_3459_);
lean_dec(v_x_3459_);
v_res_3462_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3458_, v_x_7444__boxed_3461_, v_x_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(lean_object* v_x_3463_, lean_object* v_x_3464_){
_start:
{
uint64_t v___x_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3464_);
v___x_3466_ = lean_uint64_to_usize(v___x_3465_);
lean_inc_ref(v_x_3463_);
v___x_3467_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3463_, v___x_3466_, v_x_3464_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg___boxed(lean_object* v_x_3468_, lean_object* v_x_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_3468_, v_x_3469_);
lean_dec_ref(v_x_3468_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0(lean_object* v_msg_3471_, lean_object* v_e_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
lean_object* v___y_3485_; lean_object* v___x_3494_; lean_object* v_share_3495_; lean_object* v___x_3496_; 
v___x_3494_ = lean_st_ref_get(v___y_3474_);
v_share_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc_ref(v_share_3495_);
lean_dec(v___x_3494_);
lean_inc_ref(v_e_3472_);
v___x_3496_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_share_3495_, v_e_3472_);
lean_dec_ref(v_share_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v___x_3497_; 
v___x_3497_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3471_, v_e_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
v___y_3485_ = v___x_3497_;
goto v___jp_3484_;
}
else
{
lean_object* v_val_3498_; lean_object* v_fst_3499_; uint8_t v___x_3500_; 
v_val_3498_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_val_3498_);
lean_dec_ref(v___x_3496_);
v_fst_3499_ = lean_ctor_get(v_val_3498_, 0);
lean_inc(v_fst_3499_);
lean_dec(v_val_3498_);
v___x_3500_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_3499_, v_e_3472_);
lean_dec(v_fst_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
v___x_3501_ = l___private_Lean_Meta_Sym_Util_0__Lean_Expr_checkMaxShared_throwNotMaxShared(v_msg_3471_, v_e_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
v___y_3485_ = v___x_3501_;
goto v___jp_3484_;
}
else
{
lean_dec_ref(v_e_3472_);
lean_dec_ref(v_msg_3471_);
goto v___jp_3480_;
}
}
v___jp_3480_:
{
uint8_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = 1;
v___x_3482_ = lean_box(v___x_3481_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
v___jp_3484_:
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
v_a_3486_ = lean_ctor_get(v___y_3485_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___y_3485_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___y_3485_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___y_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___lam__0___boxed(lean_object* v_msg_3502_, lean_object* v_e_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_Expr_checkMaxShared___lam__0(v_msg_3502_, v_e_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
return v_res_3511_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(lean_object* v_a_3512_, lean_object* v_x_3513_){
_start:
{
if (lean_obj_tag(v_x_3513_) == 0)
{
uint8_t v___x_3514_; 
v___x_3514_ = 0;
return v___x_3514_;
}
else
{
lean_object* v_key_3515_; lean_object* v_tail_3516_; uint8_t v___x_3517_; 
v_key_3515_ = lean_ctor_get(v_x_3513_, 0);
v_tail_3516_ = lean_ctor_get(v_x_3513_, 2);
v___x_3517_ = lean_expr_eqv(v_key_3515_, v_a_3512_);
if (v___x_3517_ == 0)
{
v_x_3513_ = v_tail_3516_;
goto _start;
}
else
{
return v___x_3517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_a_3519_, lean_object* v_x_3520_){
_start:
{
uint8_t v_res_3521_; lean_object* v_r_3522_; 
v_res_3521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3519_, v_x_3520_);
lean_dec(v_x_3520_);
lean_dec_ref(v_a_3519_);
v_r_3522_ = lean_box(v_res_3521_);
return v_r_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(lean_object* v_a_3523_, lean_object* v_b_3524_, lean_object* v_x_3525_){
_start:
{
if (lean_obj_tag(v_x_3525_) == 0)
{
lean_dec(v_b_3524_);
lean_dec_ref(v_a_3523_);
return v_x_3525_;
}
else
{
lean_object* v_key_3526_; lean_object* v_value_3527_; lean_object* v_tail_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3540_; 
v_key_3526_ = lean_ctor_get(v_x_3525_, 0);
v_value_3527_ = lean_ctor_get(v_x_3525_, 1);
v_tail_3528_ = lean_ctor_get(v_x_3525_, 2);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_x_3525_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3530_ = v_x_3525_;
v_isShared_3531_ = v_isSharedCheck_3540_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_tail_3528_);
lean_inc(v_value_3527_);
lean_inc(v_key_3526_);
lean_dec(v_x_3525_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3540_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
uint8_t v___x_3532_; 
v___x_3532_ = lean_expr_eqv(v_key_3526_, v_a_3523_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3523_, v_b_3524_, v_tail_3528_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 2, v___x_3533_);
v___x_3535_ = v___x_3530_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_key_3526_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_value_3527_);
lean_ctor_set(v_reuseFailAlloc_3536_, 2, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
else
{
lean_object* v___x_3538_; 
lean_dec(v_value_3527_);
lean_dec(v_key_3526_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v_b_3524_);
lean_ctor_set(v___x_3530_, 0, v_a_3523_);
v___x_3538_ = v___x_3530_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3523_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_b_3524_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_tail_3528_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(lean_object* v_x_3541_, lean_object* v_x_3542_){
_start:
{
if (lean_obj_tag(v_x_3542_) == 0)
{
return v_x_3541_;
}
else
{
lean_object* v_key_3543_; lean_object* v_value_3544_; lean_object* v_tail_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3568_; 
v_key_3543_ = lean_ctor_get(v_x_3542_, 0);
v_value_3544_ = lean_ctor_get(v_x_3542_, 1);
v_tail_3545_ = lean_ctor_get(v_x_3542_, 2);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_x_3542_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3547_ = v_x_3542_;
v_isShared_3548_ = v_isSharedCheck_3568_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_tail_3545_);
lean_inc(v_value_3544_);
lean_inc(v_key_3543_);
lean_dec(v_x_3542_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3568_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; uint64_t v___x_3550_; uint64_t v___x_3551_; uint64_t v___x_3552_; uint64_t v_fold_3553_; uint64_t v___x_3554_; uint64_t v___x_3555_; uint64_t v___x_3556_; size_t v___x_3557_; size_t v___x_3558_; size_t v___x_3559_; size_t v___x_3560_; size_t v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3549_ = lean_array_get_size(v_x_3541_);
v___x_3550_ = l_Lean_Expr_hash(v_key_3543_);
v___x_3551_ = 32ULL;
v___x_3552_ = lean_uint64_shift_right(v___x_3550_, v___x_3551_);
v_fold_3553_ = lean_uint64_xor(v___x_3550_, v___x_3552_);
v___x_3554_ = 16ULL;
v___x_3555_ = lean_uint64_shift_right(v_fold_3553_, v___x_3554_);
v___x_3556_ = lean_uint64_xor(v_fold_3553_, v___x_3555_);
v___x_3557_ = lean_uint64_to_usize(v___x_3556_);
v___x_3558_ = lean_usize_of_nat(v___x_3549_);
v___x_3559_ = ((size_t)1ULL);
v___x_3560_ = lean_usize_sub(v___x_3558_, v___x_3559_);
v___x_3561_ = lean_usize_land(v___x_3557_, v___x_3560_);
v___x_3562_ = lean_array_uget_borrowed(v_x_3541_, v___x_3561_);
lean_inc(v___x_3562_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 2, v___x_3562_);
v___x_3564_ = v___x_3547_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_key_3543_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_value_3544_);
lean_ctor_set(v_reuseFailAlloc_3567_, 2, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_array_uset(v_x_3541_, v___x_3561_, v___x_3564_);
v_x_3541_ = v___x_3565_;
v_x_3542_ = v_tail_3545_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(lean_object* v_i_3569_, lean_object* v_source_3570_, lean_object* v_target_3571_){
_start:
{
lean_object* v___x_3572_; uint8_t v___x_3573_; 
v___x_3572_ = lean_array_get_size(v_source_3570_);
v___x_3573_ = lean_nat_dec_lt(v_i_3569_, v___x_3572_);
if (v___x_3573_ == 0)
{
lean_dec_ref(v_source_3570_);
lean_dec(v_i_3569_);
return v_target_3571_;
}
else
{
lean_object* v_es_3574_; lean_object* v___x_3575_; lean_object* v_source_3576_; lean_object* v_target_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_es_3574_ = lean_array_fget(v_source_3570_, v_i_3569_);
v___x_3575_ = lean_box(0);
v_source_3576_ = lean_array_fset(v_source_3570_, v_i_3569_, v___x_3575_);
v_target_3577_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_target_3571_, v_es_3574_);
v___x_3578_ = lean_unsigned_to_nat(1u);
v___x_3579_ = lean_nat_add(v_i_3569_, v___x_3578_);
lean_dec(v_i_3569_);
v_i_3569_ = v___x_3579_;
v_source_3570_ = v_source_3576_;
v_target_3571_ = v_target_3577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(lean_object* v_data_3581_){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v_nbuckets_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3582_ = lean_array_get_size(v_data_3581_);
v___x_3583_ = lean_unsigned_to_nat(2u);
v_nbuckets_3584_ = lean_nat_mul(v___x_3582_, v___x_3583_);
v___x_3585_ = lean_unsigned_to_nat(0u);
v___x_3586_ = lean_box(0);
v___x_3587_ = lean_mk_array(v_nbuckets_3584_, v___x_3586_);
v___x_3588_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v___x_3585_, v_data_3581_, v___x_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(lean_object* v_m_3589_, lean_object* v_a_3590_, lean_object* v_b_3591_){
_start:
{
lean_object* v_size_3592_; lean_object* v_buckets_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3636_; 
v_size_3592_ = lean_ctor_get(v_m_3589_, 0);
v_buckets_3593_ = lean_ctor_get(v_m_3589_, 1);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_m_3589_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3595_ = v_m_3589_;
v_isShared_3596_ = v_isSharedCheck_3636_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_buckets_3593_);
lean_inc(v_size_3592_);
lean_dec(v_m_3589_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3636_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3597_; uint64_t v___x_3598_; uint64_t v___x_3599_; uint64_t v___x_3600_; uint64_t v_fold_3601_; uint64_t v___x_3602_; uint64_t v___x_3603_; uint64_t v___x_3604_; size_t v___x_3605_; size_t v___x_3606_; size_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; lean_object* v_bkt_3610_; uint8_t v___x_3611_; 
v___x_3597_ = lean_array_get_size(v_buckets_3593_);
v___x_3598_ = l_Lean_Expr_hash(v_a_3590_);
v___x_3599_ = 32ULL;
v___x_3600_ = lean_uint64_shift_right(v___x_3598_, v___x_3599_);
v_fold_3601_ = lean_uint64_xor(v___x_3598_, v___x_3600_);
v___x_3602_ = 16ULL;
v___x_3603_ = lean_uint64_shift_right(v_fold_3601_, v___x_3602_);
v___x_3604_ = lean_uint64_xor(v_fold_3601_, v___x_3603_);
v___x_3605_ = lean_uint64_to_usize(v___x_3604_);
v___x_3606_ = lean_usize_of_nat(v___x_3597_);
v___x_3607_ = ((size_t)1ULL);
v___x_3608_ = lean_usize_sub(v___x_3606_, v___x_3607_);
v___x_3609_ = lean_usize_land(v___x_3605_, v___x_3608_);
v_bkt_3610_ = lean_array_uget_borrowed(v_buckets_3593_, v___x_3609_);
v___x_3611_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3590_, v_bkt_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; lean_object* v_size_x27_3613_; lean_object* v___x_3614_; lean_object* v_buckets_x27_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; 
v___x_3612_ = lean_unsigned_to_nat(1u);
v_size_x27_3613_ = lean_nat_add(v_size_3592_, v___x_3612_);
lean_dec(v_size_3592_);
lean_inc(v_bkt_3610_);
v___x_3614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3614_, 0, v_a_3590_);
lean_ctor_set(v___x_3614_, 1, v_b_3591_);
lean_ctor_set(v___x_3614_, 2, v_bkt_3610_);
v_buckets_x27_3615_ = lean_array_uset(v_buckets_3593_, v___x_3609_, v___x_3614_);
v___x_3616_ = lean_unsigned_to_nat(4u);
v___x_3617_ = lean_nat_mul(v_size_x27_3613_, v___x_3616_);
v___x_3618_ = lean_unsigned_to_nat(3u);
v___x_3619_ = lean_nat_div(v___x_3617_, v___x_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_array_get_size(v_buckets_x27_3615_);
v___x_3621_ = lean_nat_dec_le(v___x_3619_, v___x_3620_);
lean_dec(v___x_3619_);
if (v___x_3621_ == 0)
{
lean_object* v_val_3622_; lean_object* v___x_3624_; 
v_val_3622_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_buckets_x27_3615_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v_val_3622_);
lean_ctor_set(v___x_3595_, 0, v_size_x27_3613_);
v___x_3624_ = v___x_3595_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_size_x27_3613_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_val_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
else
{
lean_object* v___x_3627_; 
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v_buckets_x27_3615_);
lean_ctor_set(v___x_3595_, 0, v_size_x27_3613_);
v___x_3627_ = v___x_3595_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_size_x27_3613_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_buckets_x27_3615_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
else
{
lean_object* v___x_3629_; lean_object* v_buckets_x27_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3634_; 
lean_inc(v_bkt_3610_);
v___x_3629_ = lean_box(0);
v_buckets_x27_3630_ = lean_array_uset(v_buckets_3593_, v___x_3609_, v___x_3629_);
v___x_3631_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3590_, v_b_3591_, v_bkt_3610_);
v___x_3632_ = lean_array_uset(v_buckets_x27_3630_, v___x_3609_, v___x_3631_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v___x_3632_);
v___x_3634_ = v___x_3595_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_size_3592_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(lean_object* v_a_3637_, lean_object* v_x_3638_){
_start:
{
if (lean_obj_tag(v_x_3638_) == 0)
{
lean_object* v___x_3639_; 
v___x_3639_ = lean_box(0);
return v___x_3639_;
}
else
{
lean_object* v_key_3640_; lean_object* v_value_3641_; lean_object* v_tail_3642_; uint8_t v___x_3643_; 
v_key_3640_ = lean_ctor_get(v_x_3638_, 0);
v_value_3641_ = lean_ctor_get(v_x_3638_, 1);
v_tail_3642_ = lean_ctor_get(v_x_3638_, 2);
v___x_3643_ = lean_expr_eqv(v_key_3640_, v_a_3637_);
if (v___x_3643_ == 0)
{
v_x_3638_ = v_tail_3642_;
goto _start;
}
else
{
lean_object* v___x_3645_; 
lean_inc(v_value_3641_);
v___x_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3645_, 0, v_value_3641_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_a_3646_, lean_object* v_x_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3646_, v_x_3647_);
lean_dec(v_x_3647_);
lean_dec_ref(v_a_3646_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(lean_object* v_m_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_buckets_3651_; lean_object* v___x_3652_; uint64_t v___x_3653_; uint64_t v___x_3654_; uint64_t v___x_3655_; uint64_t v_fold_3656_; uint64_t v___x_3657_; uint64_t v___x_3658_; uint64_t v___x_3659_; size_t v___x_3660_; size_t v___x_3661_; size_t v___x_3662_; size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_buckets_3651_ = lean_ctor_get(v_m_3649_, 1);
v___x_3652_ = lean_array_get_size(v_buckets_3651_);
v___x_3653_ = l_Lean_Expr_hash(v_a_3650_);
v___x_3654_ = 32ULL;
v___x_3655_ = lean_uint64_shift_right(v___x_3653_, v___x_3654_);
v_fold_3656_ = lean_uint64_xor(v___x_3653_, v___x_3655_);
v___x_3657_ = 16ULL;
v___x_3658_ = lean_uint64_shift_right(v_fold_3656_, v___x_3657_);
v___x_3659_ = lean_uint64_xor(v_fold_3656_, v___x_3658_);
v___x_3660_ = lean_uint64_to_usize(v___x_3659_);
v___x_3661_ = lean_usize_of_nat(v___x_3652_);
v___x_3662_ = ((size_t)1ULL);
v___x_3663_ = lean_usize_sub(v___x_3661_, v___x_3662_);
v___x_3664_ = lean_usize_land(v___x_3660_, v___x_3663_);
v___x_3665_ = lean_array_uget_borrowed(v_buckets_3651_, v___x_3664_);
v___x_3666_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3650_, v___x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg___boxed(lean_object* v_m_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3667_, v_a_3668_);
lean_dec_ref(v_a_3668_);
lean_dec_ref(v_m_3667_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(lean_object* v_g_3670_, lean_object* v_e_3671_, lean_object* v_a_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v_a_3681_; lean_object* v___y_3687_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_st_ref_get(v_a_3672_);
v___x_3690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v___x_3689_, v_e_3671_);
lean_dec(v___x_3689_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v___x_3691_; 
lean_inc_ref(v_g_3670_);
lean_inc(v___y_3678_);
lean_inc_ref(v___y_3677_);
lean_inc(v___y_3676_);
lean_inc_ref(v___y_3675_);
lean_inc(v___y_3674_);
lean_inc_ref(v___y_3673_);
lean_inc_ref(v_e_3671_);
v___x_3691_ = lean_apply_8(v_g_3670_, v_e_3671_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, lean_box(0));
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v_d_3694_; lean_object* v_b_3695_; lean_object* v___y_3696_; uint8_t v___x_3699_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref(v___x_3691_);
v___x_3699_ = lean_unbox(v_a_3692_);
lean_dec(v_a_3692_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; 
lean_dec_ref(v_g_3670_);
v___x_3700_ = lean_box(0);
v_a_3681_ = v___x_3700_;
goto v___jp_3680_;
}
else
{
switch(lean_obj_tag(v_e_3671_))
{
case 7:
{
lean_object* v_binderType_3701_; lean_object* v_body_3702_; 
v_binderType_3701_ = lean_ctor_get(v_e_3671_, 1);
v_body_3702_ = lean_ctor_get(v_e_3671_, 2);
lean_inc_ref(v_body_3702_);
lean_inc_ref(v_binderType_3701_);
v_d_3694_ = v_binderType_3701_;
v_b_3695_ = v_body_3702_;
v___y_3696_ = v_a_3672_;
goto v___jp_3693_;
}
case 6:
{
lean_object* v_binderType_3703_; lean_object* v_body_3704_; 
v_binderType_3703_ = lean_ctor_get(v_e_3671_, 1);
v_body_3704_ = lean_ctor_get(v_e_3671_, 2);
lean_inc_ref(v_body_3704_);
lean_inc_ref(v_binderType_3703_);
v_d_3694_ = v_binderType_3703_;
v_b_3695_ = v_body_3704_;
v___y_3696_ = v_a_3672_;
goto v___jp_3693_;
}
case 8:
{
lean_object* v_type_3705_; lean_object* v_value_3706_; lean_object* v_body_3707_; lean_object* v___x_3708_; 
v_type_3705_ = lean_ctor_get(v_e_3671_, 1);
v_value_3706_ = lean_ctor_get(v_e_3671_, 2);
v_body_3707_ = lean_ctor_get(v_e_3671_, 3);
lean_inc_ref(v_type_3705_);
lean_inc_ref(v_g_3670_);
v___x_3708_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_type_3705_, v_a_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v___x_3709_; 
lean_dec_ref(v___x_3708_);
lean_inc_ref(v_value_3706_);
lean_inc_ref(v_g_3670_);
v___x_3709_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_value_3706_, v_a_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v___x_3709_);
lean_inc_ref(v_body_3707_);
v___x_3710_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_body_3707_, v_a_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
v___y_3687_ = v___x_3710_;
goto v___jp_3686_;
}
else
{
lean_dec_ref(v_g_3670_);
v___y_3687_ = v___x_3709_;
goto v___jp_3686_;
}
}
else
{
lean_dec_ref(v_g_3670_);
v___y_3687_ = v___x_3708_;
goto v___jp_3686_;
}
}
case 5:
{
lean_object* v_fn_3711_; lean_object* v_arg_3712_; lean_object* v___x_3713_; 
v_fn_3711_ = lean_ctor_get(v_e_3671_, 0);
v_arg_3712_ = lean_ctor_get(v_e_3671_, 1);
lean_inc_ref(v_fn_3711_);
lean_inc_ref(v_g_3670_);
v___x_3713_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_fn_3711_, v_a_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v___x_3714_; 
lean_dec_ref(v___x_3713_);
lean_inc_ref(v_arg_3712_);
v___x_3714_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_arg_3712_, v_a_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
v___y_3687_ = v___x_3714_;
goto v___jp_3686_;
}
else
{
lean_dec_ref(v_g_3670_);
v___y_3687_ = v___x_3713_;
goto v___jp_3686_;
}
}
case 10:
{
lean_object* v_expr_3715_; lean_object* v___x_3716_; 
v_expr_3715_ = lean_ctor_get(v_e_3671_, 1);
lean_inc_ref(v_expr_3715_);
v___x_3716_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_expr_3715_, v_a_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
v___y_3687_ = v___x_3716_;
goto v___jp_3686_;
}
case 11:
{
lean_object* v_struct_3717_; lean_object* v___x_3718_; 
v_struct_3717_ = lean_ctor_get(v_e_3671_, 2);
lean_inc_ref(v_struct_3717_);
v___x_3718_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_struct_3717_, v_a_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
v___y_3687_ = v___x_3718_;
goto v___jp_3686_;
}
default: 
{
lean_object* v___x_3719_; 
lean_dec_ref(v_g_3670_);
v___x_3719_ = lean_box(0);
v_a_3681_ = v___x_3719_;
goto v___jp_3680_;
}
}
}
v___jp_3693_:
{
lean_object* v___x_3697_; 
lean_inc_ref(v_g_3670_);
v___x_3697_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_d_3694_, v___y_3696_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v___x_3698_; 
lean_dec_ref(v___x_3697_);
v___x_3698_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3670_, v_b_3695_, v___y_3696_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
v___y_3687_ = v___x_3698_;
goto v___jp_3686_;
}
else
{
lean_dec_ref(v_b_3695_);
lean_dec_ref(v_g_3670_);
v___y_3687_ = v___x_3697_;
goto v___jp_3686_;
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v_e_3671_);
lean_dec_ref(v_g_3670_);
v_a_3720_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3691_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3691_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_object* v_val_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec_ref(v_e_3671_);
lean_dec_ref(v_g_3670_);
v_val_3728_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3690_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_val_3728_);
lean_dec(v___x_3690_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set_tag(v___x_3730_, 0);
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_val_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
v___jp_3680_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3682_ = lean_st_ref_take(v_a_3672_);
v___x_3683_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v___x_3682_, v_e_3671_, v_a_3681_);
v___x_3684_ = lean_st_ref_set(v_a_3672_, v___x_3683_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_a_3681_);
return v___x_3685_;
}
v___jp_3686_:
{
if (lean_obj_tag(v___y_3687_) == 0)
{
lean_object* v_a_3688_; 
v_a_3688_ = lean_ctor_get(v___y_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref(v___y_3687_);
v_a_3681_ = v_a_3688_;
goto v___jp_3680_;
}
else
{
lean_dec_ref(v_e_3671_);
return v___y_3687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1___boxed(lean_object* v_g_3736_, lean_object* v_e_3737_, lean_object* v_a_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v_g_3736_, v_e_3737_, v_a_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v_a_3738_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared(lean_object* v_e_3747_, lean_object* v_msg_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___f_3758_; lean_object* v___x_3759_; 
v___x_3756_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__1);
v___x_3757_ = lean_st_mk_ref(v___x_3756_);
v___f_3758_ = lean_alloc_closure((void*)(l_Lean_Expr_checkMaxShared___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3758_, 0, v_msg_3748_);
v___x_3759_ = l_Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1(v___f_3758_, v_e_3747_, v___x_3757_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3768_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3762_ = v___x_3759_;
v_isShared_3763_ = v_isSharedCheck_3768_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3768_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3764_ = lean_st_ref_get(v___x_3757_);
lean_dec(v___x_3757_);
lean_dec(v___x_3764_);
if (v_isShared_3763_ == 0)
{
v___x_3766_ = v___x_3762_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3760_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
lean_dec(v___x_3757_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_checkMaxShared___boxed(lean_object* v_e_3769_, lean_object* v_msg_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_Expr_checkMaxShared(v_e_3769_, v_msg_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(lean_object* v_00_u03b2_3779_, lean_object* v_x_3780_, lean_object* v_x_3781_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___redArg(v_x_3780_, v_x_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0___boxed(lean_object* v_00_u03b2_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0(v_00_u03b2_3783_, v_x_3784_, v_x_3785_);
lean_dec_ref(v_x_3784_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(lean_object* v_00_u03b2_3787_, lean_object* v_x_3788_, size_t v_x_3789_, lean_object* v_x_3790_){
_start:
{
lean_object* v___x_3791_; 
lean_inc_ref(v_x_3788_);
v___x_3791_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___redArg(v_x_3788_, v_x_3789_, v_x_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3792_, lean_object* v_x_3793_, lean_object* v_x_3794_, lean_object* v_x_3795_){
_start:
{
size_t v_x_8019__boxed_3796_; lean_object* v_res_3797_; 
v_x_8019__boxed_3796_ = lean_unbox_usize(v_x_3794_);
lean_dec(v_x_3794_);
v_res_3797_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0(v_00_u03b2_3792_, v_x_3793_, v_x_8019__boxed_3796_, v_x_3795_);
lean_dec_ref(v_x_3793_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(lean_object* v_00_u03b2_3798_, lean_object* v_m_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___redArg(v_m_3799_, v_a_3800_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3802_, lean_object* v_m_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2(v_00_u03b2_3802_, v_m_3803_, v_a_3804_);
lean_dec_ref(v_a_3804_);
lean_dec_ref(v_m_3803_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3(lean_object* v_00_u03b2_3806_, lean_object* v_m_3807_, lean_object* v_a_3808_, lean_object* v_b_3809_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3___redArg(v_m_3807_, v_a_3808_, v_b_3809_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3811_, lean_object* v_keys_3812_, lean_object* v_vals_3813_, lean_object* v_heq_3814_, lean_object* v_i_3815_, lean_object* v_k_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___redArg(v_keys_3812_, v_vals_3813_, v_i_3815_, v_k_3816_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3818_, lean_object* v_keys_3819_, lean_object* v_vals_3820_, lean_object* v_heq_3821_, lean_object* v_i_3822_, lean_object* v_k_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Expr_checkMaxShared_spec__0_spec__0_spec__1(v_00_u03b2_3818_, v_keys_3819_, v_vals_3820_, v_heq_3821_, v_i_3822_, v_k_3823_);
lean_dec_ref(v_vals_3820_);
lean_dec_ref(v_keys_3819_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_3825_, lean_object* v_a_3826_, lean_object* v_x_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___redArg(v_a_3826_, v_x_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_3829_, lean_object* v_a_3830_, lean_object* v_x_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__2_spec__4(v_00_u03b2_3829_, v_a_3830_, v_x_3831_);
lean_dec(v_x_3831_);
lean_dec_ref(v_a_3830_);
return v_res_3832_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3833_, lean_object* v_a_3834_, lean_object* v_x_3835_){
_start:
{
uint8_t v___x_3836_; 
v___x_3836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___redArg(v_a_3834_, v_x_3835_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_3837_, lean_object* v_a_3838_, lean_object* v_x_3839_){
_start:
{
uint8_t v_res_3840_; lean_object* v_r_3841_; 
v_res_3840_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__6(v_00_u03b2_3837_, v_a_3838_, v_x_3839_);
lean_dec(v_x_3839_);
lean_dec_ref(v_a_3838_);
v_r_3841_ = lean_box(v_res_3840_);
return v_r_3841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3842_, lean_object* v_data_3843_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7___redArg(v_data_3843_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_3845_, lean_object* v_a_3846_, lean_object* v_b_3847_, lean_object* v_x_3848_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__8___redArg(v_a_3846_, v_b_3847_, v_x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3850_, lean_object* v_i_3851_, lean_object* v_source_3852_, lean_object* v_target_3853_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8___redArg(v_i_3851_, v_source_3852_, v_target_3853_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9(lean_object* v_00_u03b2_3855_, lean_object* v_x_3856_, lean_object* v_x_3857_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00Lean_Expr_checkMaxShared_spec__1_spec__3_spec__7_spec__8_spec__9___redArg(v_x_3856_, v_x_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared(lean_object* v_mvarId_3859_, lean_object* v_msg_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_MVarId_getDecl(v_mvarId_3859_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v_type_3870_; lean_object* v___x_3871_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref(v___x_3868_);
v_type_3870_ = lean_ctor_get(v_a_3869_, 2);
lean_inc_ref(v_type_3870_);
lean_dec(v_a_3869_);
v___x_3871_ = l_Lean_Expr_checkMaxShared(v_type_3870_, v_msg_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
return v___x_3871_;
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
lean_dec_ref(v_msg_3860_);
v_a_3872_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3868_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3868_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_checkMaxShared___boxed(lean_object* v_mvarId_3880_, lean_object* v_msg_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_MVarId_checkMaxShared(v_mvarId_3880_, v_msg_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
lean_dec(v_a_3887_);
lean_dec_ref(v_a_3886_);
lean_dec(v_a_3885_);
lean_dec_ref(v_a_3884_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
return v_res_3889_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(lean_object* v_x_3890_){
_start:
{
if (lean_obj_tag(v_x_3890_) == 0)
{
uint8_t v___x_3891_; 
v___x_3891_ = 0;
return v___x_3891_;
}
else
{
lean_object* v_head_3892_; lean_object* v_tail_3893_; uint8_t v___x_3894_; 
v_head_3892_ = lean_ctor_get(v_x_3890_, 0);
v_tail_3893_ = lean_ctor_get(v_x_3890_, 1);
v___x_3894_ = l_Lean_Level_isAlreadyNormalizedCheap(v_head_3892_);
if (v___x_3894_ == 0)
{
uint8_t v___x_3895_; 
v___x_3895_ = 1;
return v___x_3895_;
}
else
{
v_x_3890_ = v_tail_3893_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0___boxed(lean_object* v_x_3897_){
_start:
{
uint8_t v_res_3898_; lean_object* v_r_3899_; 
v_res_3898_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_x_3897_);
lean_dec(v_x_3897_);
v_r_3899_ = lean_box(v_res_3898_);
return v_r_3899_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(lean_object* v_x_3900_){
_start:
{
switch(lean_obj_tag(v_x_3900_))
{
case 4:
{
lean_object* v_us_3901_; uint8_t v___x_3902_; 
v_us_3901_ = lean_ctor_get(v_x_3900_, 1);
v___x_3902_ = l_List_any___at___00__private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized_spec__0(v_us_3901_);
return v___x_3902_;
}
case 3:
{
lean_object* v_u_3903_; uint8_t v___x_3904_; 
v_u_3903_ = lean_ctor_get(v_x_3900_, 0);
v___x_3904_ = l_Lean_Level_isAlreadyNormalizedCheap(v_u_3903_);
if (v___x_3904_ == 0)
{
uint8_t v___x_3905_; 
v___x_3905_ = 1;
return v___x_3905_;
}
else
{
uint8_t v___x_3906_; 
v___x_3906_ = 0;
return v___x_3906_;
}
}
default: 
{
uint8_t v___x_3907_; 
v___x_3907_ = 0;
return v___x_3907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0___boxed(lean_object* v_x_3908_){
_start:
{
uint8_t v_res_3909_; lean_object* v_r_3910_; 
v_res_3909_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___lam__0(v_x_3908_);
lean_dec_ref(v_x_3908_);
v_r_3910_ = lean_box(v_res_3909_);
return v_r_3910_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(lean_object* v_e_3912_){
_start:
{
lean_object* v___f_3913_; lean_object* v___x_3914_; 
v___f_3913_ = ((lean_object*)(l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___closed__0));
v___x_3914_ = lean_find_expr(v___f_3913_, v_e_3912_);
if (lean_obj_tag(v___x_3914_) == 0)
{
uint8_t v___x_3915_; 
v___x_3915_ = 1;
return v___x_3915_;
}
else
{
uint8_t v___x_3916_; 
lean_dec_ref(v___x_3914_);
v___x_3916_ = 0;
return v___x_3916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized___boxed(lean_object* v_e_3917_){
_start:
{
uint8_t v_res_3918_; lean_object* v_r_3919_; 
v_res_3918_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_3917_);
lean_dec_ref(v_e_3917_);
v_r_3919_ = lean_box(v_res_3918_);
return v_r_3919_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(lean_object* v_a_3920_, lean_object* v_a_3921_){
_start:
{
if (lean_obj_tag(v_a_3920_) == 0)
{
lean_object* v___x_3922_; 
v___x_3922_ = l_List_reverse___redArg(v_a_3921_);
return v___x_3922_;
}
else
{
lean_object* v_head_3923_; lean_object* v_tail_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3933_; 
v_head_3923_ = lean_ctor_get(v_a_3920_, 0);
v_tail_3924_ = lean_ctor_get(v_a_3920_, 1);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_a_3920_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3926_ = v_a_3920_;
v_isShared_3927_ = v_isSharedCheck_3933_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_tail_3924_);
lean_inc(v_head_3923_);
lean_dec(v_a_3920_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3933_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3928_ = l_Lean_Level_normalize(v_head_3923_);
lean_dec(v_head_3923_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 1, v_a_3921_);
lean_ctor_set(v___x_3926_, 0, v___x_3928_);
v___x_3930_ = v___x_3926_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_a_3921_);
v___x_3930_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
v_a_3920_ = v_tail_3924_;
v_a_3921_ = v___x_3930_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0(lean_object* v_e_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v___y_3939_; lean_object* v___y_3943_; 
switch(lean_obj_tag(v_e_3934_))
{
case 3:
{
lean_object* v_u_3946_; lean_object* v___x_3947_; size_t v___x_3948_; size_t v___x_3949_; uint8_t v___x_3950_; 
v_u_3946_ = lean_ctor_get(v_e_3934_, 0);
v___x_3947_ = l_Lean_Level_normalize(v_u_3946_);
v___x_3948_ = lean_ptr_addr(v_u_3946_);
v___x_3949_ = lean_ptr_addr(v___x_3947_);
v___x_3950_ = lean_usize_dec_eq(v___x_3948_, v___x_3949_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; 
lean_dec_ref(v_e_3934_);
v___x_3951_ = l_Lean_Expr_sort___override(v___x_3947_);
v___y_3939_ = v___x_3951_;
goto v___jp_3938_;
}
else
{
lean_dec(v___x_3947_);
v___y_3939_ = v_e_3934_;
goto v___jp_3938_;
}
}
case 4:
{
lean_object* v_declName_3952_; lean_object* v_us_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; uint8_t v___x_3956_; 
v_declName_3952_ = lean_ctor_get(v_e_3934_, 0);
v_us_3953_ = lean_ctor_get(v_e_3934_, 1);
v___x_3954_ = lean_box(0);
lean_inc(v_us_3953_);
v___x_3955_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_normalizeLevels_spec__0(v_us_3953_, v___x_3954_);
v___x_3956_ = l_ptrEqList___redArg(v_us_3953_, v___x_3955_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; 
lean_inc(v_declName_3952_);
lean_dec_ref(v_e_3934_);
v___x_3957_ = l_Lean_Expr_const___override(v_declName_3952_, v___x_3955_);
v___y_3943_ = v___x_3957_;
goto v___jp_3942_;
}
else
{
lean_dec(v___x_3955_);
v___y_3943_ = v_e_3934_;
goto v___jp_3942_;
}
}
default: 
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
lean_dec_ref(v_e_3934_);
v___x_3958_ = ((lean_object*)(l_Lean_Meta_Sym_unfoldReducibleStep___closed__0));
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
return v___x_3959_;
}
}
v___jp_3938_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___y_3939_);
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
return v___x_3941_;
}
v___jp_3942_:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___y_3943_);
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
return v___x_3945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__0___boxed(lean_object* v_e_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Lean_Meta_Sym_normalizeLevels___lam__0(v_e_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1(lean_object* v_e_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v_e_3965_);
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___lam__1___boxed(lean_object* v_e_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_Meta_Sym_normalizeLevels___lam__1(v_e_3971_, v___y_3972_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(lean_object* v_ref_3976_){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v_ref_3976_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg___boxed(lean_object* v_ref_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_3981_);
return v_res_3983_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = lean_box(0);
v___x_3985_ = l_Lean_interruptExceptionId;
v___x_3986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
lean_ctor_set(v___x_3986_, 1, v___x_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg(){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___closed__0);
v___x_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v___y_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(lean_object* v_x_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v___y_3998_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; uint8_t v___y_4022_; uint8_t v___y_4023_; lean_object* v_fileName_4028_; lean_object* v_fileMap_4029_; lean_object* v_options_4030_; lean_object* v_currRecDepth_4031_; lean_object* v_maxRecDepth_4032_; lean_object* v_ref_4033_; lean_object* v_currNamespace_4034_; lean_object* v_openDecls_4035_; lean_object* v_initHeartbeats_4036_; lean_object* v_maxHeartbeats_4037_; lean_object* v_quotContext_4038_; lean_object* v_currMacroScope_4039_; uint8_t v_diag_4040_; lean_object* v_cancelTk_x3f_4041_; uint8_t v_suppressElabErrors_4042_; lean_object* v_inheritedTraceOptions_4043_; 
v_fileName_4028_ = lean_ctor_get(v___y_3994_, 0);
v_fileMap_4029_ = lean_ctor_get(v___y_3994_, 1);
v_options_4030_ = lean_ctor_get(v___y_3994_, 2);
v_currRecDepth_4031_ = lean_ctor_get(v___y_3994_, 3);
v_maxRecDepth_4032_ = lean_ctor_get(v___y_3994_, 4);
v_ref_4033_ = lean_ctor_get(v___y_3994_, 5);
v_currNamespace_4034_ = lean_ctor_get(v___y_3994_, 6);
v_openDecls_4035_ = lean_ctor_get(v___y_3994_, 7);
v_initHeartbeats_4036_ = lean_ctor_get(v___y_3994_, 8);
v_maxHeartbeats_4037_ = lean_ctor_get(v___y_3994_, 9);
v_quotContext_4038_ = lean_ctor_get(v___y_3994_, 10);
v_currMacroScope_4039_ = lean_ctor_get(v___y_3994_, 11);
v_diag_4040_ = lean_ctor_get_uint8(v___y_3994_, sizeof(void*)*14);
v_cancelTk_x3f_4041_ = lean_ctor_get(v___y_3994_, 12);
v_suppressElabErrors_4042_ = lean_ctor_get_uint8(v___y_3994_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4043_ = lean_ctor_get(v___y_3994_, 13);
if (lean_obj_tag(v_cancelTk_x3f_4041_) == 1)
{
lean_object* v_val_4049_; uint8_t v___x_4050_; 
v_val_4049_ = lean_ctor_get(v_cancelTk_x3f_4041_, 0);
v___x_4050_ = l_IO_CancelToken_isSet(v_val_4049_);
if (v___x_4050_ == 0)
{
goto v___jp_4044_;
}
else
{
lean_object* v___x_4051_; lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_dec_ref(v_x_3992_);
v___x_4051_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4051_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4051_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
goto v___jp_4044_;
}
v___jp_3997_:
{
if (lean_obj_tag(v___y_3998_) == 0)
{
return v___y_3998_;
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
v_a_3999_ = lean_ctor_get(v___y_3998_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___y_3998_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___y_3998_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___y_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
v___jp_4007_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4024_ = lean_unsigned_to_nat(1u);
v___x_4025_ = lean_nat_add(v___y_4015_, v___x_4024_);
lean_inc_ref(v___y_4021_);
lean_inc(v___y_4010_);
lean_inc(v___y_4019_);
lean_inc(v___y_4011_);
lean_inc(v___y_4012_);
lean_inc(v___y_4008_);
lean_inc(v___y_4020_);
lean_inc(v___y_4018_);
lean_inc(v___y_4016_);
lean_inc_ref(v___y_4009_);
lean_inc_ref(v___y_4014_);
lean_inc_ref(v___y_4013_);
v___x_4026_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4026_, 0, v___y_4013_);
lean_ctor_set(v___x_4026_, 1, v___y_4014_);
lean_ctor_set(v___x_4026_, 2, v___y_4009_);
lean_ctor_set(v___x_4026_, 3, v___x_4025_);
lean_ctor_set(v___x_4026_, 4, v___y_4016_);
lean_ctor_set(v___x_4026_, 5, v___y_4017_);
lean_ctor_set(v___x_4026_, 6, v___y_4018_);
lean_ctor_set(v___x_4026_, 7, v___y_4020_);
lean_ctor_set(v___x_4026_, 8, v___y_4008_);
lean_ctor_set(v___x_4026_, 9, v___y_4012_);
lean_ctor_set(v___x_4026_, 10, v___y_4011_);
lean_ctor_set(v___x_4026_, 11, v___y_4019_);
lean_ctor_set(v___x_4026_, 12, v___y_4010_);
lean_ctor_set(v___x_4026_, 13, v___y_4021_);
lean_ctor_set_uint8(v___x_4026_, sizeof(void*)*14, v___y_4023_);
lean_ctor_set_uint8(v___x_4026_, sizeof(void*)*14 + 1, v___y_4022_);
lean_inc(v___y_3995_);
lean_inc(v___y_3993_);
v___x_4027_ = lean_apply_4(v_x_3992_, v___y_3993_, v___x_4026_, v___y_3995_, lean_box(0));
v___y_3998_ = v___x_4027_;
goto v___jp_3997_;
}
v___jp_4044_:
{
lean_object* v___x_4045_; uint8_t v___x_4046_; 
v___x_4045_ = lean_unsigned_to_nat(0u);
v___x_4046_ = lean_nat_dec_eq(v_maxRecDepth_4032_, v___x_4045_);
if (v___x_4046_ == 0)
{
uint8_t v___x_4047_; 
v___x_4047_ = lean_nat_dec_eq(v_currRecDepth_4031_, v_maxRecDepth_4032_);
if (v___x_4047_ == 0)
{
lean_inc(v_ref_4033_);
v___y_4008_ = v_initHeartbeats_4036_;
v___y_4009_ = v_options_4030_;
v___y_4010_ = v_cancelTk_x3f_4041_;
v___y_4011_ = v_quotContext_4038_;
v___y_4012_ = v_maxHeartbeats_4037_;
v___y_4013_ = v_fileName_4028_;
v___y_4014_ = v_fileMap_4029_;
v___y_4015_ = v_currRecDepth_4031_;
v___y_4016_ = v_maxRecDepth_4032_;
v___y_4017_ = v_ref_4033_;
v___y_4018_ = v_currNamespace_4034_;
v___y_4019_ = v_currMacroScope_4039_;
v___y_4020_ = v_openDecls_4035_;
v___y_4021_ = v_inheritedTraceOptions_4043_;
v___y_4022_ = v_suppressElabErrors_4042_;
v___y_4023_ = v_diag_4040_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4048_; 
lean_dec_ref(v_x_3992_);
lean_inc(v_ref_4033_);
v___x_4048_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_4033_);
v___y_3998_ = v___x_4048_;
goto v___jp_3997_;
}
}
else
{
lean_inc(v_ref_4033_);
v___y_4008_ = v_initHeartbeats_4036_;
v___y_4009_ = v_options_4030_;
v___y_4010_ = v_cancelTk_x3f_4041_;
v___y_4011_ = v_quotContext_4038_;
v___y_4012_ = v_maxHeartbeats_4037_;
v___y_4013_ = v_fileName_4028_;
v___y_4014_ = v_fileMap_4029_;
v___y_4015_ = v_currRecDepth_4031_;
v___y_4016_ = v_maxRecDepth_4032_;
v___y_4017_ = v_ref_4033_;
v___y_4018_ = v_currNamespace_4034_;
v___y_4019_ = v_currMacroScope_4039_;
v___y_4020_ = v_openDecls_4035_;
v___y_4021_ = v_inheritedTraceOptions_4043_;
v___y_4022_ = v_suppressElabErrors_4042_;
v___y_4023_ = v_diag_4040_;
goto v___jp_4007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_x_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_object* v_00_u03b1_4066_, lean_object* v_x_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_apply_1(v_x_4067_, lean_box(0));
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0___boxed(lean_object* v_00_u03b1_4073_, lean_object* v_x_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(v_00_u03b1_4073_, v_x_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(lean_object* v_pre_4079_, lean_object* v_post_4080_, size_t v_sz_4081_, size_t v_i_4082_, lean_object* v_bs_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
uint8_t v___x_4088_; 
v___x_4088_ = lean_usize_dec_lt(v_i_4082_, v_sz_4081_);
if (v___x_4088_ == 0)
{
lean_object* v___x_4089_; 
lean_dec_ref(v_post_4080_);
lean_dec_ref(v_pre_4079_);
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v_bs_4083_);
return v___x_4089_;
}
else
{
lean_object* v_v_4090_; lean_object* v___x_4091_; 
v_v_4090_ = lean_array_uget_borrowed(v_bs_4083_, v_i_4082_);
lean_inc(v_v_4090_);
lean_inc_ref(v_post_4080_);
lean_inc_ref(v_pre_4079_);
v___x_4091_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4079_, v_post_4080_, v_v_4090_, v___y_4084_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4093_; lean_object* v_bs_x27_4094_; size_t v___x_4095_; size_t v___x_4096_; lean_object* v___x_4097_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref(v___x_4091_);
v___x_4093_ = lean_unsigned_to_nat(0u);
v_bs_x27_4094_ = lean_array_uset(v_bs_4083_, v_i_4082_, v___x_4093_);
v___x_4095_ = ((size_t)1ULL);
v___x_4096_ = lean_usize_add(v_i_4082_, v___x_4095_);
v___x_4097_ = lean_array_uset(v_bs_x27_4094_, v_i_4082_, v_a_4092_);
v_i_4082_ = v___x_4096_;
v_bs_4083_ = v___x_4097_;
goto _start;
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec_ref(v_bs_4083_);
lean_dec_ref(v_post_4080_);
lean_dec_ref(v_pre_4079_);
v_a_4099_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4091_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4091_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(lean_object* v_pre_4107_, lean_object* v_post_4108_, lean_object* v_x_4109_, lean_object* v_x_4110_, lean_object* v_x_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
if (lean_obj_tag(v_x_4109_) == 5)
{
lean_object* v_fn_4116_; lean_object* v_arg_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v_fn_4116_ = lean_ctor_get(v_x_4109_, 0);
lean_inc_ref(v_fn_4116_);
v_arg_4117_ = lean_ctor_get(v_x_4109_, 1);
lean_inc_ref(v_arg_4117_);
lean_dec_ref(v_x_4109_);
v___x_4118_ = lean_array_set(v_x_4110_, v_x_4111_, v_arg_4117_);
v___x_4119_ = lean_unsigned_to_nat(1u);
v___x_4120_ = lean_nat_sub(v_x_4111_, v___x_4119_);
lean_dec(v_x_4111_);
v_x_4109_ = v_fn_4116_;
v_x_4110_ = v___x_4118_;
v_x_4111_ = v___x_4120_;
goto _start;
}
else
{
lean_object* v___x_4122_; 
lean_dec(v_x_4111_);
lean_inc_ref(v_post_4108_);
lean_inc_ref(v_pre_4107_);
v___x_4122_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4107_, v_post_4108_, v_x_4109_, v___y_4112_, v___y_4113_, v___y_4114_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; size_t v_sz_4124_; size_t v___x_4125_; lean_object* v___x_4126_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref(v___x_4122_);
v_sz_4124_ = lean_array_size(v_x_4110_);
v___x_4125_ = ((size_t)0ULL);
lean_inc_ref(v_post_4108_);
lean_inc_ref(v_pre_4107_);
v___x_4126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_4107_, v_post_4108_, v_sz_4124_, v___x_4125_, v_x_4110_, v___y_4112_, v___y_4113_, v___y_4114_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref(v___x_4126_);
v___x_4128_ = l_Lean_mkAppN(v_a_4123_, v_a_4127_);
lean_dec(v_a_4127_);
v___x_4129_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4107_, v_post_4108_, v___x_4128_, v___y_4112_, v___y_4113_, v___y_4114_);
return v___x_4129_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec(v_a_4123_);
lean_dec_ref(v_post_4108_);
lean_dec_ref(v_pre_4107_);
v_a_4130_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4126_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4126_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
else
{
lean_dec_ref(v_x_4110_);
lean_dec_ref(v_post_4108_);
lean_dec_ref(v_pre_4107_);
return v___x_4122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(lean_object* v___x_4138_, lean_object* v_pre_4139_, lean_object* v_e_4140_, lean_object* v_post_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___y_4147_; uint8_t v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; uint8_t v___y_4154_; uint8_t v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; uint8_t v___y_4169_; uint8_t v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; uint8_t v___y_4182_; lean_object* v___x_4189_; 
v___x_4189_ = l_Lean_Core_checkSystem(v___x_4138_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v___x_4190_; 
lean_dec_ref(v___x_4189_);
lean_inc_ref(v_pre_4139_);
lean_inc(v___y_4144_);
lean_inc_ref(v___y_4143_);
lean_inc_ref(v_e_4140_);
v___x_4190_ = lean_apply_4(v_pre_4139_, v_e_4140_, v___y_4143_, v___y_4144_, lean_box(0));
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4280_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4193_ = v___x_4190_;
v_isShared_4194_ = v_isSharedCheck_4280_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4280_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___y_4196_; 
switch(lean_obj_tag(v_a_4191_))
{
case 0:
{
lean_object* v_e_4270_; lean_object* v___x_4272_; 
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_e_4140_);
lean_dec_ref(v_pre_4139_);
v_e_4270_ = lean_ctor_get(v_a_4191_, 0);
lean_inc_ref(v_e_4270_);
lean_dec_ref(v_a_4191_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 0, v_e_4270_);
v___x_4272_ = v___x_4193_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_e_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
case 1:
{
lean_object* v_e_4274_; lean_object* v___x_4275_; 
lean_del_object(v___x_4193_);
lean_dec_ref(v_e_4140_);
v_e_4274_ = lean_ctor_get(v_a_4191_, 0);
lean_inc_ref(v_e_4274_);
lean_dec_ref(v_a_4191_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4275_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_e_4274_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4277_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v_a_4276_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4277_;
}
else
{
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4275_;
}
}
default: 
{
lean_object* v_e_x3f_4278_; 
lean_del_object(v___x_4193_);
v_e_x3f_4278_ = lean_ctor_get(v_a_4191_, 0);
lean_inc(v_e_x3f_4278_);
lean_dec_ref(v_a_4191_);
if (lean_obj_tag(v_e_x3f_4278_) == 0)
{
v___y_4196_ = v_e_4140_;
goto v___jp_4195_;
}
else
{
lean_object* v_val_4279_; 
lean_dec_ref(v_e_4140_);
v_val_4279_ = lean_ctor_get(v_e_x3f_4278_, 0);
lean_inc(v_val_4279_);
lean_dec_ref(v_e_x3f_4278_);
v___y_4196_ = v_val_4279_;
goto v___jp_4195_;
}
}
}
v___jp_4195_:
{
switch(lean_obj_tag(v___y_4196_))
{
case 7:
{
lean_object* v_binderName_4197_; lean_object* v_binderType_4198_; lean_object* v_body_4199_; uint8_t v_binderInfo_4200_; lean_object* v___x_4201_; 
v_binderName_4197_ = lean_ctor_get(v___y_4196_, 0);
lean_inc(v_binderName_4197_);
v_binderType_4198_ = lean_ctor_get(v___y_4196_, 1);
v_body_4199_ = lean_ctor_get(v___y_4196_, 2);
v_binderInfo_4200_ = lean_ctor_get_uint8(v___y_4196_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4198_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4201_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_binderType_4198_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4203_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref(v___x_4201_);
lean_inc_ref(v_body_4199_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4203_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_body_4199_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; size_t v___x_4205_; size_t v___x_4206_; uint8_t v___x_4207_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref(v___x_4203_);
v___x_4205_ = lean_ptr_addr(v_binderType_4198_);
v___x_4206_ = lean_ptr_addr(v_a_4202_);
v___x_4207_ = lean_usize_dec_eq(v___x_4205_, v___x_4206_);
if (v___x_4207_ == 0)
{
v___y_4177_ = v_binderInfo_4200_;
v___y_4178_ = v___y_4196_;
v___y_4179_ = v_binderName_4197_;
v___y_4180_ = v_a_4202_;
v___y_4181_ = v_a_4204_;
v___y_4182_ = v___x_4207_;
goto v___jp_4176_;
}
else
{
size_t v___x_4208_; size_t v___x_4209_; uint8_t v___x_4210_; 
v___x_4208_ = lean_ptr_addr(v_body_4199_);
v___x_4209_ = lean_ptr_addr(v_a_4204_);
v___x_4210_ = lean_usize_dec_eq(v___x_4208_, v___x_4209_);
v___y_4177_ = v_binderInfo_4200_;
v___y_4178_ = v___y_4196_;
v___y_4179_ = v_binderName_4197_;
v___y_4180_ = v_a_4202_;
v___y_4181_ = v_a_4204_;
v___y_4182_ = v___x_4210_;
goto v___jp_4176_;
}
}
else
{
lean_dec(v_a_4202_);
lean_dec_ref(v___y_4196_);
lean_dec(v_binderName_4197_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4203_;
}
}
else
{
lean_dec_ref(v___y_4196_);
lean_dec(v_binderName_4197_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4201_;
}
}
case 6:
{
lean_object* v_binderName_4211_; lean_object* v_binderType_4212_; lean_object* v_body_4213_; uint8_t v_binderInfo_4214_; lean_object* v___x_4215_; 
v_binderName_4211_ = lean_ctor_get(v___y_4196_, 0);
lean_inc(v_binderName_4211_);
v_binderType_4212_ = lean_ctor_get(v___y_4196_, 1);
v_body_4213_ = lean_ctor_get(v___y_4196_, 2);
v_binderInfo_4214_ = lean_ctor_get_uint8(v___y_4196_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4212_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4215_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_binderType_4212_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref(v___x_4215_);
lean_inc_ref(v_body_4213_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4217_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_body_4213_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; size_t v___x_4219_; size_t v___x_4220_; uint8_t v___x_4221_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref(v___x_4217_);
v___x_4219_ = lean_ptr_addr(v_binderType_4212_);
v___x_4220_ = lean_ptr_addr(v_a_4216_);
v___x_4221_ = lean_usize_dec_eq(v___x_4219_, v___x_4220_);
if (v___x_4221_ == 0)
{
v___y_4164_ = v_binderInfo_4214_;
v___y_4165_ = v_a_4218_;
v___y_4166_ = v_a_4216_;
v___y_4167_ = v___y_4196_;
v___y_4168_ = v_binderName_4211_;
v___y_4169_ = v___x_4221_;
goto v___jp_4163_;
}
else
{
size_t v___x_4222_; size_t v___x_4223_; uint8_t v___x_4224_; 
v___x_4222_ = lean_ptr_addr(v_body_4213_);
v___x_4223_ = lean_ptr_addr(v_a_4218_);
v___x_4224_ = lean_usize_dec_eq(v___x_4222_, v___x_4223_);
v___y_4164_ = v_binderInfo_4214_;
v___y_4165_ = v_a_4218_;
v___y_4166_ = v_a_4216_;
v___y_4167_ = v___y_4196_;
v___y_4168_ = v_binderName_4211_;
v___y_4169_ = v___x_4224_;
goto v___jp_4163_;
}
}
else
{
lean_dec(v_a_4216_);
lean_dec(v_binderName_4211_);
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4217_;
}
}
else
{
lean_dec(v_binderName_4211_);
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4215_;
}
}
case 8:
{
lean_object* v_declName_4225_; lean_object* v_type_4226_; lean_object* v_value_4227_; lean_object* v_body_4228_; uint8_t v_nondep_4229_; lean_object* v___x_4230_; 
v_declName_4225_ = lean_ctor_get(v___y_4196_, 0);
lean_inc(v_declName_4225_);
v_type_4226_ = lean_ctor_get(v___y_4196_, 1);
v_value_4227_ = lean_ctor_get(v___y_4196_, 2);
v_body_4228_ = lean_ctor_get(v___y_4196_, 3);
lean_inc_ref(v_body_4228_);
v_nondep_4229_ = lean_ctor_get_uint8(v___y_4196_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_4226_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4230_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_type_4226_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; lean_object* v___x_4232_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
lean_inc(v_a_4231_);
lean_dec_ref(v___x_4230_);
lean_inc_ref(v_value_4227_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4232_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_value_4227_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4234_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref(v___x_4232_);
lean_inc_ref(v_body_4228_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4234_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_body_4228_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; size_t v___x_4236_; size_t v___x_4237_; uint8_t v___x_4238_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref(v___x_4234_);
v___x_4236_ = lean_ptr_addr(v_type_4226_);
v___x_4237_ = lean_ptr_addr(v_a_4231_);
v___x_4238_ = lean_usize_dec_eq(v___x_4236_, v___x_4237_);
if (v___x_4238_ == 0)
{
v___y_4147_ = v_a_4235_;
v___y_4148_ = v_nondep_4229_;
v___y_4149_ = v_a_4231_;
v___y_4150_ = v___y_4196_;
v___y_4151_ = v_a_4233_;
v___y_4152_ = v_declName_4225_;
v___y_4153_ = v_body_4228_;
v___y_4154_ = v___x_4238_;
goto v___jp_4146_;
}
else
{
size_t v___x_4239_; size_t v___x_4240_; uint8_t v___x_4241_; 
v___x_4239_ = lean_ptr_addr(v_value_4227_);
v___x_4240_ = lean_ptr_addr(v_a_4233_);
v___x_4241_ = lean_usize_dec_eq(v___x_4239_, v___x_4240_);
v___y_4147_ = v_a_4235_;
v___y_4148_ = v_nondep_4229_;
v___y_4149_ = v_a_4231_;
v___y_4150_ = v___y_4196_;
v___y_4151_ = v_a_4233_;
v___y_4152_ = v_declName_4225_;
v___y_4153_ = v_body_4228_;
v___y_4154_ = v___x_4241_;
goto v___jp_4146_;
}
}
else
{
lean_dec(v_a_4233_);
lean_dec(v_a_4231_);
lean_dec_ref(v_body_4228_);
lean_dec_ref(v___y_4196_);
lean_dec(v_declName_4225_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4234_;
}
}
else
{
lean_dec(v_a_4231_);
lean_dec_ref(v_body_4228_);
lean_dec_ref(v___y_4196_);
lean_dec(v_declName_4225_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4232_;
}
}
else
{
lean_dec_ref(v_body_4228_);
lean_dec_ref(v___y_4196_);
lean_dec(v_declName_4225_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4230_;
}
}
case 5:
{
lean_object* v_dummy_4242_; lean_object* v_nargs_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v_dummy_4242_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__1___closed__1);
v_nargs_4243_ = l_Lean_Expr_getAppNumArgs(v___y_4196_);
lean_inc(v_nargs_4243_);
v___x_4244_ = lean_mk_array(v_nargs_4243_, v_dummy_4242_);
v___x_4245_ = lean_unsigned_to_nat(1u);
v___x_4246_ = lean_nat_sub(v_nargs_4243_, v___x_4245_);
lean_dec(v_nargs_4243_);
v___x_4247_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_4139_, v_post_4141_, v___y_4196_, v___x_4244_, v___x_4246_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4247_;
}
case 10:
{
lean_object* v_data_4248_; lean_object* v_expr_4249_; lean_object* v___x_4250_; 
v_data_4248_ = lean_ctor_get(v___y_4196_, 0);
v_expr_4249_ = lean_ctor_get(v___y_4196_, 1);
lean_inc_ref(v_expr_4249_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4250_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_expr_4249_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; size_t v___x_4252_; size_t v___x_4253_; uint8_t v___x_4254_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref(v___x_4250_);
v___x_4252_ = lean_ptr_addr(v_expr_4249_);
v___x_4253_ = lean_ptr_addr(v_a_4251_);
v___x_4254_ = lean_usize_dec_eq(v___x_4252_, v___x_4253_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
lean_inc(v_data_4248_);
lean_dec_ref(v___y_4196_);
v___x_4255_ = l_Lean_Expr_mdata___override(v_data_4248_, v_a_4251_);
v___x_4256_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___x_4255_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4256_;
}
else
{
lean_object* v___x_4257_; 
lean_dec(v_a_4251_);
v___x_4257_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___y_4196_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4257_;
}
}
else
{
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4250_;
}
}
case 11:
{
lean_object* v_typeName_4258_; lean_object* v_idx_4259_; lean_object* v_struct_4260_; lean_object* v___x_4261_; 
v_typeName_4258_ = lean_ctor_get(v___y_4196_, 0);
v_idx_4259_ = lean_ctor_get(v___y_4196_, 1);
v_struct_4260_ = lean_ctor_get(v___y_4196_, 2);
lean_inc_ref(v_struct_4260_);
lean_inc_ref(v_post_4141_);
lean_inc_ref(v_pre_4139_);
v___x_4261_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4139_, v_post_4141_, v_struct_4260_, v___y_4142_, v___y_4143_, v___y_4144_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; size_t v___x_4263_; size_t v___x_4264_; uint8_t v___x_4265_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref(v___x_4261_);
v___x_4263_ = lean_ptr_addr(v_struct_4260_);
v___x_4264_ = lean_ptr_addr(v_a_4262_);
v___x_4265_ = lean_usize_dec_eq(v___x_4263_, v___x_4264_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_inc(v_idx_4259_);
lean_inc(v_typeName_4258_);
lean_dec_ref(v___y_4196_);
v___x_4266_ = l_Lean_Expr_proj___override(v_typeName_4258_, v_idx_4259_, v_a_4262_);
v___x_4267_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___x_4266_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4267_;
}
else
{
lean_object* v___x_4268_; 
lean_dec(v_a_4262_);
v___x_4268_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___y_4196_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4268_;
}
}
else
{
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_pre_4139_);
return v___x_4261_;
}
}
default: 
{
lean_object* v___x_4269_; 
v___x_4269_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___y_4196_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4269_;
}
}
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_e_4140_);
lean_dec_ref(v_pre_4139_);
v_a_4281_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4190_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4190_);
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
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec_ref(v_post_4141_);
lean_dec_ref(v_e_4140_);
lean_dec_ref(v_pre_4139_);
v_a_4289_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4189_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4189_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
v___jp_4146_:
{
if (v___y_4154_ == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec_ref(v___y_4153_);
lean_dec_ref(v___y_4150_);
v___x_4155_ = l_Lean_Expr_letE___override(v___y_4152_, v___y_4149_, v___y_4151_, v___y_4147_, v___y_4148_);
v___x_4156_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___x_4155_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4156_;
}
else
{
size_t v___x_4157_; size_t v___x_4158_; uint8_t v___x_4159_; 
v___x_4157_ = lean_ptr_addr(v___y_4153_);
lean_dec_ref(v___y_4153_);
v___x_4158_ = lean_ptr_addr(v___y_4147_);
v___x_4159_ = lean_usize_dec_eq(v___x_4157_, v___x_4158_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_dec_ref(v___y_4150_);
v___x_4160_ = l_Lean_Expr_letE___override(v___y_4152_, v___y_4149_, v___y_4151_, v___y_4147_, v___y_4148_);
v___x_4161_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___x_4160_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4161_;
}
else
{
lean_object* v___x_4162_; 
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec_ref(v___y_4149_);
lean_dec_ref(v___y_4147_);
v___x_4162_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___y_4150_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4162_;
}
}
}
v___jp_4163_:
{
if (v___y_4169_ == 0)
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
lean_dec_ref(v___y_4167_);
v___x_4170_ = l_Lean_Expr_lam___override(v___y_4168_, v___y_4166_, v___y_4165_, v___y_4164_);
v___x_4171_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___x_4170_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4171_;
}
else
{
uint8_t v___x_4172_; 
v___x_4172_ = l_Lean_instBEqBinderInfo_beq(v___y_4164_, v___y_4164_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_dec_ref(v___y_4167_);
v___x_4173_ = l_Lean_Expr_lam___override(v___y_4168_, v___y_4166_, v___y_4165_, v___y_4164_);
v___x_4174_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___x_4173_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4174_;
}
else
{
lean_object* v___x_4175_; 
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4166_);
lean_dec_ref(v___y_4165_);
v___x_4175_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___y_4167_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4175_;
}
}
}
v___jp_4176_:
{
if (v___y_4182_ == 0)
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
lean_dec_ref(v___y_4178_);
v___x_4183_ = l_Lean_Expr_forallE___override(v___y_4179_, v___y_4180_, v___y_4181_, v___y_4177_);
v___x_4184_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___x_4183_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4184_;
}
else
{
uint8_t v___x_4185_; 
v___x_4185_ = l_Lean_instBEqBinderInfo_beq(v___y_4177_, v___y_4177_);
if (v___x_4185_ == 0)
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_dec_ref(v___y_4178_);
v___x_4186_ = l_Lean_Expr_forallE___override(v___y_4179_, v___y_4180_, v___y_4181_, v___y_4177_);
v___x_4187_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___x_4186_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4187_;
}
else
{
lean_object* v___x_4188_; 
lean_dec_ref(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
v___x_4188_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4139_, v_post_4141_, v___y_4178_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed(lean_object* v___x_4297_, lean_object* v_pre_4298_, lean_object* v_e_4299_, lean_object* v_post_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1(v___x_4297_, v_pre_4298_, v_e_4299_, v_post_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(lean_object* v_pre_4306_, lean_object* v_post_4307_, lean_object* v_e_4308_, lean_object* v_a_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
lean_inc(v_a_4309_);
v___x_4313_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4313_, 0, lean_box(0));
lean_closure_set(v___x_4313_, 1, lean_box(0));
lean_closure_set(v___x_4313_, 2, v_a_4309_);
v___x_4314_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___x_4313_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4346_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4317_ = v___x_4314_;
v_isShared_4318_ = v_isSharedCheck_4346_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4346_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4319_; 
v___x_4319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0_spec__4___redArg(v_a_4315_, v_e_4308_);
lean_dec(v_a_4315_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4320_; lean_object* v___f_4321_; lean_object* v___x_4322_; 
lean_del_object(v___x_4317_);
v___x_4320_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_4308_);
v___f_4321_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__1___boxed), 8, 4);
lean_closure_set(v___f_4321_, 0, v___x_4320_);
lean_closure_set(v___f_4321_, 1, v_pre_4306_);
lean_closure_set(v___f_4321_, 2, v_e_4308_);
lean_closure_set(v___f_4321_, 3, v_post_4307_);
v___x_4322_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v___f_4321_, v_a_4309_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___f_4324_; lean_object* v___x_4325_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc_n(v_a_4323_, 2);
lean_dec_ref(v___x_4322_);
lean_inc(v_a_4309_);
v___f_4324_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4324_, 0, v_a_4309_);
lean_closure_set(v___f_4324_, 1, v_e_4308_);
lean_closure_set(v___f_4324_, 2, v_a_4323_);
v___x_4325_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___lam__0(lean_box(0), v___f_4324_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4332_ == 0)
{
lean_object* v_unused_4333_; 
v_unused_4333_ = lean_ctor_get(v___x_4325_, 0);
lean_dec(v_unused_4333_);
v___x_4327_ = v___x_4325_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_dec(v___x_4325_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v_a_4323_);
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4323_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec(v_a_4323_);
v_a_4334_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4325_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4325_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
else
{
lean_dec_ref(v_e_4308_);
return v___x_4322_;
}
}
else
{
lean_object* v_val_4342_; lean_object* v___x_4344_; 
lean_dec_ref(v_e_4308_);
lean_dec_ref(v_post_4307_);
lean_dec_ref(v_pre_4306_);
v_val_4342_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_val_4342_);
lean_dec_ref(v___x_4319_);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 0, v_val_4342_);
v___x_4344_ = v___x_4317_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_val_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec_ref(v_e_4308_);
lean_dec_ref(v_post_4307_);
lean_dec_ref(v_pre_4306_);
v_a_4347_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4314_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4314_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(lean_object* v_pre_4355_, lean_object* v_post_4356_, lean_object* v_e_4357_, lean_object* v_a_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v___x_4362_; 
lean_inc_ref(v_post_4356_);
lean_inc(v___y_4360_);
lean_inc_ref(v___y_4359_);
lean_inc_ref(v_e_4357_);
v___x_4362_ = lean_apply_4(v_post_4356_, v_e_4357_, v___y_4359_, v___y_4360_, lean_box(0));
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4381_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4365_ = v___x_4362_;
v_isShared_4366_ = v_isSharedCheck_4381_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4362_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4381_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
switch(lean_obj_tag(v_a_4363_))
{
case 0:
{
lean_object* v_e_4367_; lean_object* v___x_4369_; 
lean_dec_ref(v_e_4357_);
lean_dec_ref(v_post_4356_);
lean_dec_ref(v_pre_4355_);
v_e_4367_ = lean_ctor_get(v_a_4363_, 0);
lean_inc_ref(v_e_4367_);
lean_dec_ref(v_a_4363_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v_e_4367_);
v___x_4369_ = v___x_4365_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_e_4367_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
case 1:
{
lean_object* v_e_4371_; lean_object* v___x_4372_; 
lean_del_object(v___x_4365_);
lean_dec_ref(v_e_4357_);
v_e_4371_ = lean_ctor_get(v_a_4363_, 0);
lean_inc_ref(v_e_4371_);
lean_dec_ref(v_a_4363_);
v___x_4372_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4355_, v_post_4356_, v_e_4371_, v_a_4358_, v___y_4359_, v___y_4360_);
return v___x_4372_;
}
default: 
{
lean_object* v_e_x3f_4373_; 
lean_dec_ref(v_post_4356_);
lean_dec_ref(v_pre_4355_);
v_e_x3f_4373_ = lean_ctor_get(v_a_4363_, 0);
lean_inc(v_e_x3f_4373_);
lean_dec_ref(v_a_4363_);
if (lean_obj_tag(v_e_x3f_4373_) == 0)
{
lean_object* v___x_4375_; 
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v_e_4357_);
v___x_4375_ = v___x_4365_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_e_4357_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
else
{
lean_object* v_val_4377_; lean_object* v___x_4379_; 
lean_dec_ref(v_e_4357_);
v_val_4377_ = lean_ctor_get(v_e_x3f_4373_, 0);
lean_inc(v_val_4377_);
lean_dec_ref(v_e_x3f_4373_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v_val_4377_);
v___x_4379_ = v___x_4365_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_val_4377_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec_ref(v_e_4357_);
lean_dec_ref(v_post_4356_);
lean_dec_ref(v_pre_4355_);
v_a_4382_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4362_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4362_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3___boxed(lean_object* v_pre_4390_, lean_object* v_post_4391_, lean_object* v_e_4392_, lean_object* v_a_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__3(v_pre_4390_, v_post_4391_, v_e_4392_, v_a_4393_, v___y_4394_, v___y_4395_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v_a_4393_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2___boxed(lean_object* v_pre_4398_, lean_object* v_post_4399_, lean_object* v_sz_4400_, lean_object* v_i_4401_, lean_object* v_bs_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
size_t v_sz_boxed_4407_; size_t v_i_boxed_4408_; lean_object* v_res_4409_; 
v_sz_boxed_4407_ = lean_unbox_usize(v_sz_4400_);
lean_dec(v_sz_4400_);
v_i_boxed_4408_ = lean_unbox_usize(v_i_4401_);
lean_dec(v_i_4401_);
v_res_4409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__2(v_pre_4398_, v_post_4399_, v_sz_boxed_4407_, v_i_boxed_4408_, v_bs_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4___boxed(lean_object* v_pre_4410_, lean_object* v_post_4411_, lean_object* v_x_4412_, lean_object* v_x_4413_, lean_object* v_x_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__4(v_pre_4410_, v_post_4411_, v_x_4412_, v_x_4413_, v_x_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v___y_4415_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1___boxed(lean_object* v_pre_4420_, lean_object* v_post_4421_, lean_object* v_e_4422_, lean_object* v_a_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4420_, v_post_4421_, v_e_4422_, v_a_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v_a_4423_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_object* v_00_u03b1_4428_, lean_object* v_x_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = lean_apply_1(v_x_4429_, lean_box(0));
v___x_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0___boxed(lean_object* v_00_u03b1_4435_, lean_object* v_x_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(v_00_u03b1_4435_, v_x_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(lean_object* v_input_4441_, lean_object* v_pre_4442_, lean_object* v_post_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v_a_4449_; lean_object* v___x_4450_; 
v___x_4447_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Meta_Sym_unfoldReducible_spec__0___closed__2);
v___x_4448_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4447_, v___y_4444_, v___y_4445_);
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_a_4449_);
lean_dec_ref(v___x_4448_);
v___x_4450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1(v_pre_4442_, v_post_4443_, v_input_4441_, v_a_4449_, v___y_4444_, v___y_4445_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_a_4451_);
lean_dec_ref(v___x_4450_);
v___x_4452_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4452_, 0, lean_box(0));
lean_closure_set(v___x_4452_, 1, lean_box(0));
lean_closure_set(v___x_4452_, 2, v_a_4449_);
v___x_4453_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___lam__0(lean_box(0), v___x_4452_, v___y_4444_, v___y_4445_);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4460_ == 0)
{
lean_object* v_unused_4461_; 
v_unused_4461_ = lean_ctor_get(v___x_4453_, 0);
lean_dec(v_unused_4461_);
v___x_4455_ = v___x_4453_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_dec(v___x_4453_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 0, v_a_4451_);
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4451_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
else
{
lean_dec(v_a_4449_);
return v___x_4450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1___boxed(lean_object* v_input_4462_, lean_object* v_pre_4463_, lean_object* v_post_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_input_4462_, v_pre_4463_, v_post_4464_, v___y_4465_, v___y_4466_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels(lean_object* v_e_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_){
_start:
{
uint8_t v___x_4475_; 
v___x_4475_ = l___private_Lean_Meta_Sym_Util_0__Lean_Meta_Sym_levelsAlreadyNormalized(v_e_4471_);
if (v___x_4475_ == 0)
{
lean_object* v_pre_4476_; lean_object* v___f_4477_; lean_object* v___x_4478_; 
v_pre_4476_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__0));
v___f_4477_ = ((lean_object*)(l_Lean_Meta_Sym_normalizeLevels___closed__1));
v___x_4478_ = l_Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1(v_e_4471_, v_pre_4476_, v___f_4477_, v_a_4472_, v_a_4473_);
return v___x_4478_;
}
else
{
lean_object* v___x_4479_; 
v___x_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4479_, 0, v_e_4471_);
return v___x_4479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_normalizeLevels___boxed(lean_object* v_e_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_Meta_Sym_normalizeLevels(v_e_4480_, v_a_4481_, v_a_4482_);
lean_dec(v_a_4482_);
lean_dec_ref(v_a_4481_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(lean_object* v_00_u03b1_4485_, lean_object* v_ref_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___redArg(v_ref_4486_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6___boxed(lean_object* v_00_u03b1_4491_, lean_object* v_ref_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__6(v_00_u03b1_4491_, v_ref_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v___x_4501_; 
v___x_4501_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___redArg();
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5_spec__7(v_00_u03b1_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(lean_object* v_00_u03b1_4507_, lean_object* v_x_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___redArg(v_x_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5___boxed(lean_object* v_00_u03b1_4514_, lean_object* v_x_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Sym_normalizeLevels_spec__1_spec__1_spec__5(v_00_u03b1_4514_, v_x_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v___y_4516_);
return v_res_4520_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Util(builtin);
}
#ifdef __cplusplus
}
#endif
